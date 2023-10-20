use std::fs::File;
use std::io::Read;
use std::iter::Iterator;
use std::{error, fmt, io, result};

/// Result type alias around [`MemInfoError`].
pub type Result<T> = result::Result<T, MemInfoError>;

/// A list of errors that may occur while opening, reading or manipulating `/proc/meminfo`.
#[derive(Debug)]
pub enum MemInfoError {
    /// Failed to open `/proc/meminfo`.
    Open(io::Error),
    /// Failed to read `/proc/meminfo`.
    Read(io::Error),
}

impl fmt::Display for MemInfoError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Open(_) => f.write_str("failed to open `/proc/meminfo`"),
            Self::Read(_) => f.write_str("failed to read `/proc/meminfo`"),
        }
    }
}

impl error::Error for MemInfoError {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        match self {
            Self::Open(source) | Self::Read(source) => Some(source),
        }
    }
}

/// A buffer around `/proc/meminfo`.
/// Provides easy open and read functionality as well as zero allocation parsing of entries.
#[derive(Debug)]
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
            .map_err(MemInfoError::Open)?
            .read_to_end(&mut self.buf)
            .map_err(MemInfoError::Read)
    }

    /// Fetches `/proc/meminfo` data and returns an iterator over parsed entries.
    ///
    /// # Errors
    ///
    /// This method will return a [`MemInfoError`] if the open or read operations fail.
    /// [`MemInfoError`] variants hold their respective error sources.
    #[tracing::instrument(skip(self))]
    pub fn fetch(&mut self) -> Result<impl Iterator<Item = MemInfoEntry>> {
        let bytes = self.read()?;
        tracing::debug!("successfully read {bytes} bytes from `/proc/meminfo`");

        Ok(Parser::new(&self.buf))
    }
}

/// A `/proc/meminfo` entry, a parsed line of its content.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MemInfoEntry<'data> {
    /// Entry's label.
    label: &'data str,
    /// Entry's size (or amount).
    size: &'data str,
    /// Entry's unit, if present.
    unit: Option<&'data str>,
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
