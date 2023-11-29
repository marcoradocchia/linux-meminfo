// -----------------------------------------------------------------------------------------------
// -- Standard library imports --
// -----------------------------------------------------------------------------------------------
use std::num::ParseIntError;
use std::ops::{Deref, DerefMut, Range};
use std::{error, fmt, str};

// -----------------------------------------------------------------------------------------------
// -- Module error types --
// -----------------------------------------------------------------------------------------------
/// The error type for [`MemInfoEntry`] **size** parsing.
#[derive(Debug)]
pub struct ParseSizeError {
    /// **Label** of the [`MemInfoEntry`] whose size could not be parsed.
    pub(crate) label: String,
    /// **Size** of the [`MemInfoEntry`] that could not be parsed.
    pub(crate) size: String,
    /// The error **source** (i.e. the reson why [`MemInfoEntry`] size could not be parsed).
    pub(crate) source: ParseIntError,
}

impl ParseSizeError {
    /// Constructs a new instance of the error from the `label` of the entry whose `size` could
    /// not be parsed as `usize`, the string representation of the entry `size` that could not be
    /// parsed and the `source` of the error (i.e. the error cause).
    #[inline]
    fn new(label: &str, size: &str, source: ParseIntError) -> Self {
        Self {
            label: label.to_owned(),
            size: size.to_owned(),
            source,
        }
    }
}

impl fmt::Display for ParseSizeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_fmt(format_args!(
            "failed to parse `{size}` as usize in `/proc/meminfo` entry `{label}`",
            size = self.size,
            label = self.label
        ))
    }
}

impl error::Error for ParseSizeError {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        Some(&self.source)
    }
}

// -----------------------------------------------------------------------------------------------
// -- Module types --
// -----------------------------------------------------------------------------------------------
/// A parsed `/proc/meminfo` entry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MemInfoEntry<'m> {
    /// Entry **label** (e.g. `MemAvailable`).
    pub(crate) label: &'m str,
    /// Entry **size** (e.g. `3911344`).
    pub(crate) size: &'m str,
    /// Entry **unit**, if present (e.g. `kB`).
    ///
    /// # Notes
    ///
    /// Unit might be missing for entries which do not represent memory sizes
    /// (e.g. `HugePages_Total`, `HugePages_Free`, etc.).
    pub(crate) unit: Option<&'m str>,
}

impl<'m> MemInfoEntry<'m> {
    /// The delimiter between a `/proc/meminfo` entry label and its size.
    pub(crate) const DELIMITER: u8 = b':';

    /// Constructs a new instance from entry `label`, `size`, and `unit`, converting fields from
    /// UTF-8 bytes to string slices.
    ///
    /// # Panics
    ///
    /// This functions panics if `bytes` do not represent valid UTF-8.
    #[inline]
    #[cfg(not(feature = "utf8-unchecked"))]
    pub(crate) fn new(label: &'m [u8], size: &'m [u8], unit: Option<&'m [u8]>) -> Self {
        /// Converts a slice of bytes to a string slice, validating its content to be UTF-8.
        ///
        /// # Panics
        ///
        /// This functions panics if `bytes` do not represent valid UTF-8.
        #[inline(always)]
        fn from_utf8(bytes: &[u8]) -> &str {
            str::from_utf8(bytes).expect("`/proc/meminfo` to contain valid UTF-8")
        }

        Self {
            label: from_utf8(label),
            size: from_utf8(size),
            unit: unit.map(from_utf8),
        }
    }

    /// Constructs a new instance from entry `label`, `size` and `unit`, converting fields from
    /// UTF-8 bytes to string slices.
    ///
    /// # Safety
    ///
    /// This function assumes `label`, `size` and `unit` (`/proc/meminfo` data) to be valid
    /// UTF-8 bytes. If this is not the case (e.g. malformed `/proc/meminfo` data), calling this
    /// function will result in undefined behaviour. In case of doubt, please use
    /// [`MemInfoEntry::new`] instead, since performs UTF-8 validation and panics on malformed
    /// data.
    #[inline]
    #[must_use]
    #[cfg(feature = "utf8-unchecked")]
    pub(crate) unsafe fn new_unchecked(
        label: &'m [u8],
        size: &'m [u8],
        unit: Option<&'m [u8]>,
    ) -> Self {
        Self {
            label: unsafe { str::from_utf8_unchecked(label) },
            size: unsafe { str::from_utf8_unchecked(size) },
            unit: unit.map(|unit| unsafe { str::from_utf8_unchecked(unit) }),
        }
    }

    /// Returns the entry label (e.g. `MemAvailable`).
    #[inline]
    #[must_use]
    pub fn label(&self) -> &str {
        self.label
    }

    /// Returns the entry size (e.g. `3911344`).
    ///
    /// # Errors
    ///
    /// This method returns an error if the entry size could not be parsed as `usize`.
    #[inline]
    pub fn size(&self) -> Result<usize, ParseSizeError> {
        self.size
            .parse()
            .map_err(|source| ParseSizeError::new(self.label, self.size, source))
    }

    /// Returns the entry unit, if present (e.g. `kB`).
    #[inline]
    #[must_use]
    pub fn unit(&self) -> Option<&str> {
        self.unit
    }
}

/// A parsed `/proc/meminfo` entry with additional information about its position in the file
/// stream.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MemInfoEntryExtended<'m> {
    /// The actual `/proc/meminfo` entry.
    pub(crate) entry: MemInfoEntry<'m>,
    /// The range of bytes this entry was parsed from in the `/proc/meminfo` file stream.
    pub(crate) range: Range<usize>,
}

impl<'m> MemInfoEntryExtended<'m> {
    /// Constructs a new instance from a plain `entry`, and the `start` and `end` byte positions
    /// of the entry in the `/proc/meminfo` file stream.
    #[inline]
    pub(crate) fn new(entry: MemInfoEntry<'m>, start: usize, end: usize) -> Self {
        Self {
            entry,
            range: start..end,
        }
    }

    #[inline]
    #[must_use]
    pub fn byte_range(&self) -> &Range<usize> {
        &self.range
    }
}

impl<'m> Deref for MemInfoEntryExtended<'m> {
    type Target = MemInfoEntry<'m>;

    fn deref(&self) -> &Self::Target {
        &self.entry
    }
}

impl<'m> DerefMut for MemInfoEntryExtended<'m> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.entry
    }
}
