//! # Linux MemInfo
//!
//! This library provides easy and low level access to `meminfo`, the _pseudofile_ placed
//! by the Linux kernel inside the `proc` _pseudo-filesystem_ (for more information, see the `proc`
//! [manpage](https://man7.org/linux/man-pages/man5/proc.5.html)).
//!
//! The public API is built around the [`MemInfo`] type, a struct responsible for retrieving
//! memory-related information about the system. Calling its [constructor](`MemInfo::new`)
//! opens the `/proc/meminfo` pseudofile and reads its data into an internal buffer.
//! Having [`MemInfo`] to own both the open file and a buffer of its data allows separation of
//! concerns between _reading_ from the pseudofile, _managing_ and _parsing_ the buffered data.
//!
//! The parser implementation responsible for parsing `/proc/meminfo` entries works exclusively on
//! string slices, just owning a reference to the pseudofile buffered bytes. This allows for
//! efficient, **zero-allocation** parsing.
//!
//! ## Examples
//!
//! The following example shows the most basic usage of the [`MemInfo`] API. First we construct
//! a new instance, which translates to `/proc/meminfo` being opened and read into the internal
//! buffer; then we call the [`MemInfo::parse`], which returns a **lazy** iterator over parsed
//! entries, in this case represented by the [`MemInfoEntry`] type. The iterator being lazy
//! meaning it parses a new entry on each call to the `next` method. In other words: _you only pay
//! for the entries you parse_.
//!
//! ```rust
//! use std::error;
//!
//! use meminfo::MemInfo;
//!
//! fn main() -> Result<(), Box<dyn error::Error>> {
//!     let mut meminfo = MemInfo::new()?;
//!     let mut entries = meminfo.parse();
//!
//!     let mem_total = entries.next().unwrap();
//!     assert_eq!("MemTotal", mem_total.label());
//!     assert_eq!(Some("kB"), mem_total.unit());
//!
//!     println!("System's total usable RAM: {}kB", mem_total.size()?);
//!
//!     Ok(())
//! }
//! ```
//!
//! Users may have distinct use cases that call for regular retrieval of a particular set of
//! entries within the `/proc/meminfo` pseudofile. The [`MemInfo::parse_extended`] efficiently
//! addresses this requirement, extending parsed entries with additional information pertaining to
//! the byte range they occupy in the file stream. This functionality allows users to selectively
//! read and parse specific entries as needed. Also, this way, the internal buffer can be shrank to
//! the capacity required to read in such entries, reducing the runtime memory footprint of the
//! program.
//!
//! ```no_run
//! use std::io::SeekFrom;
//! use std::time::Duration;
//! use std::{error, thread};
//!
//! use meminfo::{MemInfo, MemInfoError};
//!
//! #[derive(Debug)]
//! struct MemAvailable {
//!     size: usize,
//!     start_pos: usize,
//! }
//!
//! impl MemAvailable {
//!     fn new(meminfo: &mut MemInfo) -> Result<Self, MemInfoError> {
//!         let mut entries = meminfo.parse_extended().skip(2);
//!
//!         let mem_available = entries.next().unwrap();
//!         assert_eq!("MemAvailable", mem_available.label());
//!         assert_eq!(Some("kB"), mem_available.unit());
//!
//!         let size = mem_available.size().unwrap();
//!         let start_pos = mem_available.start_pos();
//!         let capacity = mem_available.required_capacity();
//!
//!         drop(entries);
//!         meminfo.clear();
//!         meminfo.shrink_to(capacity);
//!
//!         Ok(MemAvailable { size, start_pos })
//!     }
//!
//!     fn fetch(&mut self, meminfo: &mut MemInfo) -> Result<(), MemInfoError> {
//!         let seek_pos = SeekFrom::Start(self.start_pos as u64);
//!         meminfo.seek(seek_pos)?;
//!
//!         meminfo.clear();
//!         meminfo.read()?;
//!
//!         let entry = meminfo.parse().next().unwrap();
//!         self.size = entry.size().unwrap();
//!
//!         Ok(())
//!     }
//! }
//!
//! fn main() -> Result<(), Box<dyn error::Error>> {
//!     let mut meminfo = MemInfo::new()?;
//!     let mut mem_available = MemAvailable::new(&mut meminfo)?;
//!
//!     loop {
//!         println!("System's available RAM: {}kB", mem_available.size);
//!         thread::sleep(Duration::from_secs(2));
//!         mem_available.fetch(&mut meminfo)?;
//!     }
//! }
//! ```
//!
//! ## Features
//!
//! By default, the [`MemInfoEntry`] and [`MemInfoEntryExtended`] constructors perform UTF-8
//! validation on `/proc/meminfo` parsed data. Malformed data would cause a panic in this case.
//! However, enabling the `utf8-unchecked` feature removes such validation, potentially increasing
//! parsing performance. To achieve this, the new constructors make use of unsafe code, thus the
//! user should be aware that malformed `/proc/meminfo` data would cause undefined behaviour.

// -----------------------------------------------------------------------------------------------
// -- Crate modules --
// -----------------------------------------------------------------------------------------------
mod entry;
mod parser;

// -----------------------------------------------------------------------------------------------
// -- Standard library imports --
// -----------------------------------------------------------------------------------------------
use std::fs::File;
use std::io::{Read, Seek, SeekFrom};
use std::{error, fmt, io, result};

// -----------------------------------------------------------------------------------------------
// -- Crate imports --
// -----------------------------------------------------------------------------------------------
use crate::parser::{MemInfoParser, MemInfoParserExtended};

// -----------------------------------------------------------------------------------------------
// -- Crate public imports (or re-exports) --
// -----------------------------------------------------------------------------------------------
pub use crate::entry::{MemInfoEntry, MemInfoEntryExtended, ParseSizeError};

// -----------------------------------------------------------------------------------------------
// -- Module type aliases --
// -----------------------------------------------------------------------------------------------
/// Return type of fallible [`MemInfo`] functions, or methods.
pub type Result<T> = result::Result<T, MemInfoError>;

// -----------------------------------------------------------------------------------------------
// -- Module error types --
// -----------------------------------------------------------------------------------------------
/// A list of error categories related to manipulation of the `/proc/meminfo` pseudofile.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MemInfoErrorKind {
    /// Opening `/proc/meminfo` failed.
    Open,
    /// Reading `/proc/meminfo` failed.
    Read,
    /// Rewinding `/proc/meminfo` failed.
    Rewind,
    /// Seeking `/proc/meminfo` failed.
    Seek,
}

impl fmt::Display for MemInfoErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Self::Open => f.write_str("open"),
            Self::Read => f.write_str("read"),
            Self::Rewind => f.write_str("rewind"),
            Self::Seek => f.write_str("seek"),
        }
    }
}

/// The error type for the [`MemInfo`] struct type.
#[derive(Debug)]
pub struct MemInfoError {
    /// The error category, (e.g. read, open, etc.).
    kind: MemInfoErrorKind,
    /// The error source (i.e. the reson why the error occurred).
    source: io::Error,
}

impl MemInfoError {
    /// Constructs a new instance of the error from a `kind` and a `source`.
    #[inline]
    const fn new(kind: MemInfoErrorKind, source: io::Error) -> Self {
        Self { kind, source }
    }

    /// Constructs a new instance of the error from a `source`, with kind
    /// [`MemInfoErrorKind::Open`].
    #[inline]
    const fn open(source: io::Error) -> Self {
        Self::new(MemInfoErrorKind::Open, source)
    }

    /// Constructs a new instance of the error from a `source`, with kind
    /// [`MemInfoErrorKind::Read`].
    #[inline]
    const fn read(source: io::Error) -> Self {
        Self::new(MemInfoErrorKind::Read, source)
    }

    /// Constructs a new instance of the error from a `source`, with kind
    /// [`MemInfoErrorKind::Rewind`].
    #[inline]
    const fn rewind(source: io::Error) -> Self {
        Self::new(MemInfoErrorKind::Rewind, source)
    }

    /// Constructs a new instance of the error from a `source`, with kind
    /// [`MemInfoErrorKind::Seek`].
    #[inline]
    const fn seek(source: io::Error) -> Self {
        Self::new(MemInfoErrorKind::Seek, source)
    }

    /// Returns the error kind.
    #[inline]
    #[must_use]
    pub fn kind(&self) -> &MemInfoErrorKind {
        &self.kind
    }
}

impl fmt::Display for MemInfoError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_fmt(format_args!("failed to {} `/proc/meminfo`", self.kind))
    }
}

impl error::Error for MemInfoError {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        Some(&self.source)
    }
}

// -----------------------------------------------------------------------------------------------
// -- Module types --
// -----------------------------------------------------------------------------------------------
/// An object providing buffered access to the `/proc/meminfo` pseudofile.
///
/// This struct is responsible for retrieving memory-related information about the system. Its
/// [constructor](`MemInfo::new`) attempts to:
/// - **open** the `/proc/meminfo` pseudofile;
/// - **read** its data into the internal buffer;
/// - **rewind** to the beginning of the file stream, in order to prepare for the next read call.
pub struct MemInfo {
    /// The buffer holind data from `/proc/meminfo`.
    buf: Vec<u8>,
    /// The `/proc/meminfo` pseudofile.
    file: File,
}

impl MemInfo {
    /// Opens the `/proc/meminfo` pseudofile in read-only mode.
    ///
    /// # Errors
    ///
    /// This method returns an error if `/proc/meminfo` fails to open.
    #[inline]
    fn open() -> Result<File> {
        File::open("/proc/meminfo").map_err(MemInfoError::open)
    }

    /// Constructs a new instance, opening the `/proc/meminfo` pseudofile, reading all of its
    /// data into the internal buffer and rewinding to the beginning of the stream.
    ///
    /// # Errors
    ///
    /// This function returns an error if `/proc/meminfo` could not be opened, read into the
    /// internal buffer, or rewinded.
    #[inline]
    pub fn new() -> Result<Self> {
        let mut meminfo = Self {
            file: Self::open()?,
            buf: Vec::new(),
        };

        meminfo.read_to_end()?;
        meminfo.rewind()?;

        Ok(meminfo)
    }

    /// Constructs a new intance, opening the `/proc/meminfo` pseudofile, reading its data
    /// into the internal buffer up to buffer `capacity` and rewinding to the beginning of the
    /// stream.
    ///
    /// # Errors
    ///
    /// This function returns an error if `/proc/meminfo` could not be opened, read into the
    /// internal buffer, or rewinded.
    #[inline]
    pub fn with_capacity(capacity: usize) -> Result<Self> {
        let mut meminfo = Self {
            file: Self::open()?,
            buf: Vec::with_capacity(capacity),
        };

        meminfo.read()?;
        meminfo.rewind()?;

        Ok(meminfo)
    }

    /// Clears the internal buffer, removing its content without affecting its allocated capacity.
    #[inline]
    pub fn clear(&mut self) {
        self.buf.clear();
    }

    /// Shrinks the capacity of the internal buffer as much as possible close to the buffer length.
    ///
    /// # Notes
    ///
    /// This method does **NOT** clear the internal buffer before attempting to resize its
    /// capacity.
    ///
    /// If the current buffer capacity matches the buffer length, calling this method will result
    /// in a **no-op**.
    #[inline]
    pub fn shrink_to_fit(&mut self) {
        self.buf.shrink_to_fit();
    }

    /// Shrinks the capacity of the internal buffer with a lower `capacity` bound.
    ///
    /// # Notes
    ///
    /// This method does **NOT** clear the internal buffer before attempting to resize its
    /// capacity, meaning that specifying a `size` smaller the buffer _length_ is equivalent to
    /// calling [`MemInfo::shrink_to_fit`].
    ///
    /// Also, if the current buffer _capacity_ is smaller than the specified `size`, this method
    /// will result in a **no-op**.
    #[inline]
    pub fn shrink_to(&mut self, capacity: usize) {
        self.buf.shrink_to(capacity);
    }

    /// Rewinds `/proc/meminfo` to the beginning of the stream.
    ///
    /// # Notes
    ///
    /// Calling this method is equivalent to calling `self.seek(SeekFrom::Start(0))`.
    ///
    /// # Errors
    ///
    /// Returns an error if `/proc/meminfo` could not be rewinded.
    #[inline]
    pub fn rewind(&mut self) -> Result<()> {
        self.file.rewind().map_err(MemInfoError::rewind)
    }

    /// Seeks `/proc/meminfo` to an offset and returns the new position from the start of the
    /// stream.
    ///
    /// # Errors
    ///
    /// Returns an error if `/proc/meminfo` could not be sought.
    #[inline]
    pub fn seek(&mut self, pos: SeekFrom) -> Result<u64> {
        self.file.seek(pos).map_err(MemInfoError::seek)
    }

    /// Reads an exact number of `bytes` from `/proc/meminfo` into the internal buffer.
    ///
    /// # Notes
    ///
    /// The buffered data is **NOT** cleared before the new data is read into the buffer.
    ///
    /// # Errors
    ///
    /// This method returns an error if `/proc/meminfo` could not be read into the internal buffer.
    #[inline]
    pub fn read_exact(&mut self, bytes: u64) -> Result<usize> {
        self.file
            .by_ref()
            .take(bytes)
            .read_to_end(&mut self.buf)
            .map_err(MemInfoError::read)
    }

    /// Reads the exact number of bytes from `/proc/meminfo` required to fill the internal buffer
    /// and returns the number of bytes read.
    ///
    /// # Notes
    ///
    /// The buffered data is **NOT** cleared before the new data is read into the buffer.
    ///
    /// # Errors
    ///
    /// This method returns an error if `/proc/meminfo` could not be read into the internal buffer.
    #[inline]
    pub fn read(&mut self) -> Result<usize> {
        let buf_capacity = self.buf.capacity();
        self.read_exact(buf_capacity as u64)
    }

    /// Reads bytes from `/proc/meminfo` until `EOF` into the internal buffer and returns the total
    /// number of bytes read.
    ///
    /// # Notes
    ///
    /// - The buffered data is **NOT** cleared before the new data is read into the buffer.
    /// - If the internal buffer is not large enough, this method will allocate for data to fit.
    ///
    /// # Errors
    ///
    /// This method returns an error if `/proc/meminfo` could not be read into the internal buffer.
    #[inline]
    pub fn read_to_end(&mut self) -> Result<usize> {
        self.file
            .read_to_end(&mut self.buf)
            .map_err(MemInfoError::read)
    }

    /// Returns a **lazy** iterator over parsed `/proc/meminfo` entries.
    ///
    /// # Notes
    ///
    /// For richer `/proc/meminfo` entry information see [`MemInfo::parse_extended`], which
    /// is an extension of this methods, since it also collects each entry's start and end
    /// positions in the file stream (useful for [`MemInfo::seek`] calls).
    #[inline]
    pub fn parse(&self) -> impl Iterator<Item = MemInfoEntry> {
        MemInfoParser::new(&self.buf)
    }

    /// Returns an iterator over parsed `/proc/meminfo` entries.
    /// Compared to [`MemInfo::parse`], in this case the elements being iterated over are extended
    /// with information about the `start` and `end` bytes of the file they were parsed from.
    ///
    /// # Notes
    ///
    /// For simpler and slimmer `/proc/meminfo` entry information see [`MemInfo::parse`].
    #[inline]
    pub fn parse_extended(&self) -> impl Iterator<Item = MemInfoEntryExtended> {
        MemInfoParserExtended::new(&self.buf)
    }
}

impl fmt::Debug for MemInfo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("MemInfo")
            .field("buf", &BufDebug::from(&self.buf))
            .field("file", &self.file)
            .finish()
    }
}

/// Helper struct implementing [`Debug`], used in the [`MemInfo`]'s [`Debug`] trait implemenation.
///
/// # Notes
///
/// It is used to replace the default `Vec<u8>` [`Debug`] implementation, which displays the
/// actual bytes, with information about the vector's length and capacity.
struct BufDebug {
    /// The [`MemInfo`] interal buffer length.
    length: usize,
    /// The [`MemInfo`] interal buffer capacity.
    capacity: usize,
}

impl From<&Vec<u8>> for BufDebug {
    #[inline]
    fn from(buf: &Vec<u8>) -> Self {
        BufDebug {
            length: buf.len(),
            capacity: buf.capacity(),
        }
    }
}

impl fmt::Debug for BufDebug {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_fmt(format_args!(
            "{{\n\tlength: {},\n\tcapacity: {}\n}}",
            &self.length, &self.capacity
        ))
    }
}
