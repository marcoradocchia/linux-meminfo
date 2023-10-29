use std::fs::File;
use std::io::Read;
use std::iter::Iterator;
use std::num::ParseIntError;
use std::{error, fmt, io};

/// A list of errors kinds that may occur while trying to open or read `/proc/meminfo`.
#[derive(Debug, Clone, Copy)]
enum MemInfoErrorKind {
    /// Occurs when opening `/proc/meminfo` fails.
    Open,
    /// Occurs when reading `/proc/meminfo` fails.
    Read,
}

impl fmt::Display for MemInfoErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Open => f.write_str("open"),
            Self::Read => f.write_str("read"),
        }
    }
}

/// Error that may occur while trying to open or read `/proc/meminfo`.
#[derive(Debug)]
pub struct MemInfoError {
    /// The error kind identifier.
    kind: MemInfoErrorKind,
    /// The source of the error, i.e. the reason why `/proc/meminfo` can't be open/read.
    source: io::Error,
}

impl MemInfoError {
    /// Constructs a new instance from a `source` and a `kind`.
    #[inline]
    const fn new(kind: MemInfoErrorKind, source: io::Error) -> Self {
        Self { kind, source }
    }

    /// Constructs a new [`MemInfoErrorKind::Open`] variant from a `source`.
    #[inline]
    const fn open(source: io::Error) -> Self {
        Self::new(MemInfoErrorKind::Open, source)
    }

    /// Constructs a new [`MemInfoErrorKind::Read`] variant from a `source`.
    #[inline]
    const fn read(source: io::Error) -> Self {
        Self::new(MemInfoErrorKind::Read, source)
    }
}

impl fmt::Display for MemInfoError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "failed to {} '/proc/meminfo'", self.kind)
    }
}

impl error::Error for MemInfoError {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        Some(&self.source)
    }
}

/// A buffer around `/proc/meminfo`.
///
/// Provides automatic open and buffered read of `/proc/meminfo` as well as zero allocation
/// parsing of entries.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MemInfo {
    /// Buffer holding `/proc/meminfo` data.
    buf: Vec<u8>,
}

impl MemInfo {
    /// Constructs a new instance of the `/proc/meminfo` buffer.
    #[must_use]
    #[inline]
    pub const fn new() -> Self {
        Self { buf: Vec::new() }
    }

    /// Opens `/proc/meminfo` and returns a [`File`] instance.
    ///
    /// # Errors
    ///
    /// This method returns an error if the open operation on `/proc/meminfo` fails.
    /// [`MemInfoError::Open`] variant hold the respective error source.
    #[inline]
    fn open() -> Result<File, MemInfoError> {
        File::open("/proc/meminfo").map_err(MemInfoError::open)
    }

    /// Clears the internal buffer removing all values, without affecting the allocated capacity
    /// of the buffer.
    #[inline]
    fn clear(&mut self) {
        self.buf.clear();
    }

    /// Clears the internal buffer and shrinks its capacity to the given `size` in bytes.
    #[inline]
    pub fn shrink(&mut self, size: usize) {
        self.clear();
        self.buf.shrink_to(size);
    }

    /// Reads the exact number of bytes from `/proc/meminfo` required to fill the internal buffer.
    ///
    /// The internally buffered data is cleared before the new data is read into the buffer.
    ///
    /// # Errors
    ///
    /// This method returns an error if the open or read operations on `/proc/meminfo` fail.
    /// [`MemInfoError`] variants hold their respective error sources.
    #[inline]
    pub fn read(&mut self) -> Result<(), MemInfoError> {
        self.clear();
        Self::open()?
            .read_exact(&mut self.buf)
            .map_err(MemInfoError::read)
    }

    /// Reads bytes from `/proc/meminfo` until EOF into the internal buffer and returns the total
    /// number of bytes read.
    ///
    /// The internally buffered data is cleared before the new data is read into the buffer.
    ///
    /// # Errors
    ///
    /// This method returns an error if the open or read operations on `/proc/meminfo` fail.
    /// [`MemInfoError`] variants hold their respective error sources.
    #[inline]
    pub fn read_to_end(&mut self) -> Result<usize, MemInfoError> {
        self.clear();
        Self::open()?
            .read_to_end(&mut self.buf)
            .map_err(MemInfoError::read)
    }

    /// Returns an iterator over parsed entries.
    ///
    /// This method does make use of previously internal buffered data, thus does not clear or
    /// write bytes of the internal buffer.
    #[inline]
    pub fn parse(&self) -> impl Iterator<Item = MemInfoEntry> {
        Parser::new(&self.buf)
    }
}

/// Error occurs when parsing [`MemInfoEntry`] size fails.
#[derive(Debug)]
pub struct ParseSizeError {
    /// Entry's label.
    label: String,
    /// Entry's size that can't be parsed as usize.
    size: String,
    /// The source of the error, i.e. the reason why the size can't be parsed.
    source: ParseIntError,
}

impl ParseSizeError {
    /// Constructs a new instance from `/proc/meminfo` entry's `label` and `size` and the `source`
    /// of the error.
    #[inline]
    fn new(label: &str, size: &str, source: ParseIntError) -> Self {
        Self {
            label: String::from(label),
            size: String::from(size),
            source,
        }
    }
}

impl fmt::Display for ParseSizeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "failed to parse '{}' size: '{}'", self.label, self.size)
    }
}

impl error::Error for ParseSizeError {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        Some(&self.source)
    }
}

/// A `/proc/meminfo` entry, as a parsed line of its content.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MemInfoEntry<'data> {
    /// Entry's **label** (or identifier).
    label: &'data str,
    /// Entry's **size** (or amount).
    size: &'data str,
    /// Entry's **unit**, if present.
    ///
    /// The unit might be missing for entries which do not represent memory sizes
    /// (e.g. `HugePages_Total`, `HugePages_Free`, etc.).
    unit: Option<&'data str>,
}

impl<'data> MemInfoEntry<'data> {
    /// Constructs a new instance, converting fields from raw bytes to string slices.
    #[inline]
    fn new(label: &'data [u8], size: &'data [u8], unit: Option<&'data [u8]>) -> Self {
        /// Converts a slice of raw bytes into a string slice, validating its content to be UTF-8.
        ///
        /// # Panics
        ///
        /// This functions panics with a panic message if `bytes` do not represent valid UTF-8.
        #[inline]
        fn from_utf8(bytes: &[u8]) -> &str {
            std::str::from_utf8(bytes).expect("`/proc/meminfo` entries to contain valid UTF-8")
        }

        Self {
            label: from_utf8(label),
            size: from_utf8(size),
            unit: unit.map(from_utf8),
        }
    }

    /// Returns the entry's label.
    #[inline]
    #[must_use]
    pub fn label(&self) -> &str {
        self.label
    }

    /// Returns the entry's size.
    ///
    /// # Errors
    ///
    /// This method returns an error if the entry's size can't be parsed as `usize`.
    #[inline]
    pub fn size(&self) -> Result<usize, ParseSizeError> {
        self.size
            .parse()
            .map_err(|error| ParseSizeError::new(self.label, self.size, error))
    }

    /// Returns the entry's unit, if some.
    #[inline]
    #[must_use]
    pub fn unit(&self) -> Option<&str> {
        self.unit
    }
}

/// A **zero-allocation** `/proc/meminfo` parser.
///
/// This parser struct works on string slices and just owns a reference to `/proc/meminfo`'s
/// buffered bytes (bytes are buffered and owned by the [`MemInfo`] struct). This means that no
/// heap allocations are performed during the parsing operation.
#[derive(Debug)]
struct Parser<'data> {
    /// The `/proc/meminfo` **data** bytes.
    data: &'data [u8],
    /// A **cursor** navigating data's bytes. Keeps track of a position inside the data slice.
    cursor: usize,
}

impl<'data> Parser<'data> {
    /// Constructs a new instance of the parser.
    #[inline]
    const fn new(data: &'data [u8]) -> Self {
        Self { data, cursor: 0 }
    }

    /// Checks wheter EOF has been reached.
    ///
    /// This method skips all ASCII whitespaces, incrementing cursor's position up until any value
    /// not included in the _WHATWG Infra Standard_'s definition of whitespace ASCII whitespace
    /// (see `u8::is_ascii_whitespace`'s documentation), then checks if the cursor has reached EOF.
    #[inline]
    fn is_not_eof(&mut self) -> bool {
        self.cursor += self.offset(u8::is_ascii_whitespace);
        self.cursor < self.data.len()
    }

    /// Calculates an **offset** iterating on data bytes and counting yielded elements based on
    /// `predicate`.
    #[inline]
    fn offset<F>(&self, predicate: F) -> usize
    where
        F: Fn(&u8) -> bool,
    {
        self.data[self.cursor..]
            .iter()
            .take_while(|byte| predicate(byte))
            .count()
    }

    /// Skips all `U+0020` UTF-8 whitespaces, incrementing cursor's position up to the
    /// non-whitespace unicode byte.
    ///
    /// This method does not skip any _tab_, _line feed_, _form feed_ or _carriage return_ UTF-8
    /// bytes (see `u8::is_ascii_whitespace`).
    #[inline]
    fn skip_whitespace(&mut self) {
        self.cursor += self.offset(|byte| *byte == b' ');
    }

    /// Returns current `/proc/meminfo`'s entry **label** bytes.
    #[inline]
    fn get_label(&mut self) -> &'data [u8] {
        self.skip_whitespace();
        let offset = self.offset(|byte| *byte != b':');
        let label = &self.data[self.cursor..][..offset];
        self.cursor += offset + 1;

        label
    }

    /// Returns current `/proc/meminfo`'s entry **size** bytes.
    #[inline]
    fn get_size(&mut self) -> &'data [u8] {
        self.skip_whitespace();
        let offset = self.offset(u8::is_ascii_digit);
        let size = &self.data[self.cursor..][..offset];
        self.cursor += offset;

        size
    }

    /// Returns current `/proc/meminfo`'s entry **unit** bytes, if present.
    #[inline]
    fn get_unit(&mut self) -> Option<&'data [u8]> {
        self.skip_whitespace();
        let offset = self.offset(u8::is_ascii_alphabetic);
        (offset > 0).then(|| {
            let unit = &self.data[self.cursor..][..offset];
            self.cursor += offset;

            unit
        })
    }
}

impl<'data> Iterator for Parser<'data> {
    type Item = MemInfoEntry<'data>;

    fn next(&mut self) -> Option<Self::Item> {
        self.is_not_eof().then(|| {
            let label = self.get_label();
            let size = self.get_size();
            let unit = self.get_unit();

            MemInfoEntry::new(label, size, unit)
        })
    }
}

#[cfg(test)]
mod test {
    use std::num::IntErrorKind;
    use std::{error::Error, io};

    use super::*;

    #[test]
    fn meminfo_debug() {
        let data = r#"MemTotal:        8017324 kB
MemFree:          658700 kB
MemAvailable:    3167444 kB
Buffers:          186968 kB"#;
        let meminfo = MemInfo {
            buf: Vec::from(data),
        };

        assert_eq!(
            format!("MemInfo {{ buf: {:?} }}", data.as_bytes()),
            format!("{meminfo:?}"),
        )
    }

    #[test]
    fn meminfo_read() -> Result<(), MemInfoError> {
        let mut meminfo = MemInfo::new();
        let bytes = meminfo.read_to_end()?;
        dbg!(&meminfo);
        assert!(bytes > 0);

        Ok(())
    }

    #[test]
    fn meminfo_entry_debug() {
        let mem_info_entry = MemInfoEntry {
            label: "MemTotal",
            size: "8017324",
            unit: Some("kB"),
        };

        assert_eq!(
            r#"MemInfoEntry { label: "MemTotal", size: "8017324", unit: Some("kB") }"#,
            format!("{mem_info_entry:?}")
        );
    }

    #[test]
    fn parser_debug() {
        let data = "MemTotal:        8017324 kB";
        let parser = Parser::new(data.as_bytes());

        assert_eq!(
            format!("Parser {{ data: {:?}, cursor: 0 }}", data.as_bytes()),
            format!("{parser:?}")
        );
    }

    #[test]
    fn meminfo_entries_parse() {
        let data = r#"MemTotal:        8017324 kB
VmallocTotal:   34359738367 kB
HugePages_Total:       0"#;
        let mut parser = Parser::new(data.as_bytes());

        assert_eq!(
            Some(MemInfoEntry {
                label: "MemTotal",
                size: "8017324",
                unit: Some("kB"),
            }),
            parser.next()
        );

        assert_eq!(
            Some(MemInfoEntry {
                label: "VmallocTotal",
                size: "34359738367",
                unit: Some("kB"),
            }),
            parser.next(),
        );

        assert_eq!(
            Some(MemInfoEntry {
                label: "HugePages_Total",
                size: "0",
                unit: None
            }),
            parser.next()
        );

        assert_eq!(None, parser.next())
    }

    #[test]
    fn meminfo_error() {
        let open_error_source = io::Error::last_os_error();
        let open_error_source_string = open_error_source.to_string();
        let open_error = MemInfoError::open(open_error_source);

        let read_error_source = io::Error::last_os_error();
        let read_error_source_string = read_error_source.to_string();
        let read_error = MemInfoError::read(read_error_source);

        assert_eq!("failed to open '/proc/meminfo'", open_error.to_string());
        assert_eq!("failed to read '/proc/meminfo'", read_error.to_string());

        assert_eq!(
            open_error_source_string,
            open_error.source().unwrap().to_string()
        );

        assert_eq!(
            read_error_source_string,
            read_error.source().unwrap().to_string()
        );
    }

    #[test]
    fn parse_size_error() {
        let overflow = MemInfoEntry::new(
            "MemTotal".as_bytes(),
            "18446744073709551617".as_bytes(),
            Some("kB".as_bytes()),
        )
        .size()
        .unwrap_err();

        assert_eq!(IntErrorKind::PosOverflow, *overflow.source.kind());
        assert_eq!(
            "failed to parse 'MemTotal' size: '18446744073709551617'",
            overflow.to_string(),
        );

        let float = MemInfoEntry::new(
            "MemTotal".as_bytes(),
            "2.4".as_bytes(),
            Some("kB".as_bytes()),
        )
        .size()
        .unwrap_err();

        assert_eq!(IntErrorKind::InvalidDigit, *float.source.kind());
        assert_eq!("failed to parse 'MemTotal' size: '2.4'", float.to_string());

        let empty = MemInfoEntry::new("MemTotal".as_bytes(), "".as_bytes(), Some("kB".as_bytes()))
            .size()
            .unwrap_err();

        assert_eq!(IntErrorKind::Empty, *empty.source.kind());
        assert_eq!("failed to parse 'MemTotal' size: ''", empty.to_string());
    }
}
