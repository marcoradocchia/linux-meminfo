use std::fs::File;
use std::io::Read;
use std::iter::Iterator;
use std::{error, fmt, io, result};

/// Result type alias around [`MemInfoError`].
pub type Result<T> = result::Result<T, MemInfoError>;

/// A list of errors kinds that may occur while trying to open or read `/proc/meminfo`.
#[derive(Debug, Clone, Copy)]
enum MemInfoErrorKind {
    /// Failed to open `/proc/meminfo`.
    Open,
    /// Failed to read `/proc/meminfo`.
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
    source: io::Error,
    kind: MemInfoErrorKind,
}

impl MemInfoError {
    const fn new(source: io::Error, kind: MemInfoErrorKind) -> Self {
        Self { source, kind }
    }

    const fn open(source: io::Error) -> Self {
        Self::new(source, MemInfoErrorKind::Open)
    }

    const fn read(source: io::Error) -> Self {
        Self::new(source, MemInfoErrorKind::Read)
    }
}

impl fmt::Display for MemInfoError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "failed to {} `/proc/meminfo`", self.kind)
    }
}

impl error::Error for MemInfoError {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        Some(&self.source)
    }
}

/// A buffer around `/proc/meminfo`.
/// Provides easy open and read functionality as well as zero allocation parsing of entries.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MemInfo {
    /// Buffer holding `/proc/meminfo` data.
    buf: Vec<u8>,
}

impl MemInfo {
    /// Constructs a new instance.
    #[must_use]
    pub const fn new() -> Self {
        Self { buf: Vec::new() }
    }

    /// Clears the internal buffer removing all values, without affecting the allocated capacity
    /// of the buffer.
    #[inline]
    fn clear(&mut self) {
        self.buf.clear();
    }

    /// Reads bytes from `/proc/meminfo` until EOF into the internal buffer and returns the total
    /// number of bytes read.
    ///
    /// The internally buffered data is cleared before the new data is read into the buffer.
    ///
    /// # Errors
    ///
    /// This method will return a [`MemInfoError`] if the open or read operations fail.
    /// [`MemInfoError`] variants hold their respective error sources.
    #[inline]
    fn read(&mut self) -> Result<usize> {
        self.clear();
        File::open("/proc/meminfo")
            .map_err(MemInfoError::open)?
            .read_to_end(&mut self.buf)
            .map_err(MemInfoError::read)
    }

    /// Fetches `/proc/meminfo` data and returns an iterator over parsed entries.
    ///
    /// # Errors
    ///
    /// This method will return a [`MemInfoError`] if the open or read operations fail.
    /// [`MemInfoError`] variants hold their respective error sources.
    pub fn fetch(&mut self) -> Result<impl Iterator<Item = MemInfoEntry>> {
        self.read()?;
        Ok(Parser::new(&self.buf))
    }
}

/// A `/proc/meminfo` entry, a parsed line of its content.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MemInfoEntry<'data> {
    /// Entry's label.
    pub label: &'data str,
    /// Entry's size (or amount).
    pub size: &'data str,
    /// Entry's unit, if present.
    pub unit: Option<&'data str>,
}

impl<'data> MemInfoEntry<'data> {
    /// Constructs a new instance, converting fields from raw bytes to string slices.
    #[inline]
    fn new(label: &'data [u8], size: &'data [u8], unit: Option<&'data [u8]>) -> Self {
        #[inline]
        fn from_utf8(bytes: &[u8]) -> &str {
            std::str::from_utf8(bytes).expect("`/proc/meminfo` to contain valid UTF-8")
        }

        MemInfoEntry {
            label: from_utf8(label),
            size: from_utf8(size),
            unit: unit.map(from_utf8),
        }
    }
}

/// A **zero-allocation** `/proc/meminfo` parser.
#[derive(Debug)]
pub(crate) struct Parser<'data> {
    /// `/proc/meminfo` output data.
    data: &'data [u8],
    /// A cursor navigating data's bytes.
    cursor: usize,
}

impl<'data> Parser<'data> {
    /// Constructs a new `/proc/meminfo` [`Parser`].
    const fn new(data: &'data [u8]) -> Self {
        Self { data, cursor: 0 }
    }

    /// Checks wheter EOF has been reached.
    ///
    /// Skips all ASCII whitespaces, incrementing `self.cursor`'s position up until any value not
    /// included in the _WhatWG Infra Standard_'s definition of whitespace ASCII whitespace (see
    /// `u8::is_ascii_whitespace`'s documentation), then checks if `self.cursor` has reached the
    /// end of `self.input`.
    #[inline]
    fn is_not_eof(&mut self) -> bool {
        self.cursor += self.offset(u8::is_ascii_whitespace);
        self.cursor < self.data.len()
    }

    /// Calculates an offset in `self.input`, based on `operand`, starting from `self.cursor`'s
    /// position.
    #[inline]
    fn offset<F>(&self, operand: F) -> usize
    where
        F: Fn(&u8) -> bool,
    {
        self.data[self.cursor..]
            .iter()
            .take_while(|byte| operand(byte))
            .count()
    }

    /// Skips all `U+0020` whitespaces, incrementing `self.cursor`'s position.
    ///
    /// # Notes
    ///
    /// This method does not skip any _tab_, _line feed_, _form feed_ or _carriage return_.
    #[inline]
    fn skip_whitespace(&mut self) {
        self.cursor += self.offset(|byte| *byte == b' ');
    }

    /// Retrieves current `/proc/meminfo`'s entry label's bytes.
    #[inline]
    fn get_label(&mut self) -> &'data [u8] {
        self.skip_whitespace();
        let offset = self.offset(|byte| *byte != b':');
        let label = &self.data[self.cursor..][..offset];
        self.cursor += offset + 1;

        label
    }

    /// Retrieves current `/proc/meminfo`'s entry size's bytes.
    #[inline]
    fn get_size(&mut self) -> &'data [u8] {
        self.skip_whitespace();
        let offset = self.offset(u8::is_ascii_digit);
        let size = &self.data[self.cursor..][..offset];
        self.cursor += offset;

        size
    }

    /// Retrieves current `/proc/meminfo`'s entry unit's bytes, if any unit present.
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
    fn meminfo_fetch() -> Result<()> {
        let mut meminfo = MemInfo::new();
        let _ = meminfo.fetch()?;

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
        let open_error_source_display = open_error_source.to_string();
        let open_error = MemInfoError::open(open_error_source);

        let read_error_source = io::Error::last_os_error();
        let read_error_source_display = read_error_source.to_string();
        let read_error = MemInfoError::read(read_error_source);

        assert_eq!("failed to open `/proc/meminfo`", open_error.to_string());
        assert_eq!("failed to read `/proc/meminfo`", read_error.to_string());

        assert_eq!(
            open_error_source_display,
            open_error.source().unwrap().to_string()
        );

        assert_eq!(
            read_error_source_display,
            read_error.source().unwrap().to_string()
        );
    }
}
