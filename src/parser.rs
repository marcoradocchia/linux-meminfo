// -----------------------------------------------------------------------------------------------
// -- Crate imports --
// -----------------------------------------------------------------------------------------------
use crate::entry::{MemInfoEntry, MemInfoEntryExtended};

// -----------------------------------------------------------------------------------------------
// -- Module traits --
// -----------------------------------------------------------------------------------------------
/// Helper trait used inside [`MemInfoParser`] used to classify bytes.
trait ByteClassify {
    /// Checks if the value is a **whitespace**.
    fn is_whitespace(&self) -> bool;
    /// Checks if the value is a **delimiter**.
    fn is_not_delimiter(&self) -> bool;
}

impl ByteClassify for u8 {
    /// Checks if the value is a **whitespace**, more precisely a `U+0020` UTF-8 value.
    fn is_whitespace(&self) -> bool {
        *self == b' '
    }

    /// Checks if the value is **NOT** a **delimiter**, more precisely the delimiter between a
    /// `/proc/meminfo` entry laabel and its size.
    fn is_not_delimiter(&self) -> bool {
        *self != MemInfoEntry::DELIMITER
    }
}

// -----------------------------------------------------------------------------------------------
// -- Module types --
// -----------------------------------------------------------------------------------------------
/// A **zero-allocation** `/proc/meminfo` parser.
///
/// This parser struct works on string slices and just owns a reference to `/proc/meminfo` buffered
/// bytes (see [`MemInfo`]). This means that no heap allocations are performed during the parsing
/// operation.
///
/// [`MemInfo`]: [`crate::MemInfo`]
#[derive(Debug)]
pub(crate) struct MemInfoParser<'m> {
    /// The `/proc/meminfo` data **bytes**.
    bytes: &'m [u8],
    /// A **cursor** navigating data bytes.
    cursor: usize,
}

impl<'m> MemInfoParser<'m> {
    /// Constructs a new instance of the parser from `/proc/meminfo` data `bytes`.
    #[inline]
    pub(crate) fn new(bytes: &'m [u8]) -> Self {
        Self { bytes, cursor: 0 }
    }

    /// Calculates a cursor offset based on `predicate`.
    ///
    /// # Notes
    ///
    /// This method iterates over `bytes` starting from the current cursor position and counts
    /// yielded elements based on `predicate`.
    #[inline]
    fn offset<F>(&self, predicate: F) -> usize
    where
        F: Fn(&u8) -> bool,
    {
        self.bytes[self.cursor..]
            .iter()
            .take_while(|byte| predicate(byte))
            .count()
    }

    /// Skips all `U+0020` UTF-8 whitespaces, incrementing cursor's position up to the
    /// non-whitespace unicode byte.
    ///
    /// # Notes
    ///
    /// This method does not skip any _tab_, _line feed_, _form feed_ or _carriage return_ UTF-8
    /// bytes (see [`u8::is_ascii_whitespace`]).
    #[inline]
    fn skip_whitespace(&mut self) {
        self.cursor += self.offset(u8::is_whitespace);
    }

    /// Checks wheter `EOF` has been reached.
    ///
    /// This method skips all ASCII whitespaces, incrementing cursor's position up until any value
    /// not included in the _WHATWG Infra Standard_'s definition of whitespace ASCII whitespace
    /// (see `u8::is_ascii_whitespace`'s documentation), then checks if the cursor has reached
    /// `EOF`.
    #[inline]
    fn is_not_eof(&mut self) -> bool {
        self.cursor += self.offset(u8::is_ascii_whitespace);
        self.cursor < self.bytes.len()
    }

    /// Returns a slice of `bytes` starting at the cursor position and ending at the cursor
    /// position incremented by the given `offset`.
    #[inline]
    fn byte_slice(&self, offset: usize) -> &'m [u8] {
        &self.bytes[self.cursor..self.cursor + offset]
    }

    /// Returns the current `/proc/meminfo` entry **label** bytes.
    #[inline]
    fn get_label(&mut self) -> &'m [u8] {
        self.skip_whitespace();
        let offset = self.offset(u8::is_not_delimiter);
        let label = self.byte_slice(offset);
        self.cursor += offset + 1;

        label
    }

    /// Returns the current `/proc/meminfo` entry **size** bytes.
    #[inline]
    fn get_size(&mut self) -> &'m [u8] {
        self.skip_whitespace();
        let offset = self.offset(u8::is_ascii_digit);
        let size = self.byte_slice(offset);
        self.cursor += offset;

        size
    }

    /// Returns the current `/proc/meminfo`'s entry **unit** bytes, if present.
    #[inline]
    fn get_unit(&mut self) -> Option<&'m [u8]> {
        self.skip_whitespace();
        let offset = self.offset(u8::is_ascii_alphabetic);
        (offset > 0).then(|| {
            let unit = self.byte_slice(offset);
            self.cursor += offset;

            unit
        })
    }
}

impl<'m> From<&'m str> for MemInfoParser<'m> {
    #[inline]
    fn from(value: &'m str) -> Self {
        MemInfoParser::new(value.as_bytes())
    }
}

impl<'m> Iterator for MemInfoParser<'m> {
    type Item = MemInfoEntry<'m>;

    fn next(&mut self) -> Option<Self::Item> {
        self.is_not_eof().then(|| {
            let label = self.get_label();
            let size = self.get_size();
            let unit = self.get_unit();

            #[cfg(not(feature = "utf8-unchecked"))]
            return MemInfoEntry::new(label, size, unit);

            #[cfg(feature = "utf8-unchecked")]
            return unsafe { MemInfoEntry::new_unchecked(label, size, unit) };
        })
    }
}

/// An extended **zero-allocation** `/proc/meminfo` parser, extended meaning that this struct
/// enriches [`MemInfoParser`] implementation of the [`Iterator`] trait by upgrading the returned
/// elements to be of [`MemInfoEntryExtended`] type (see the [`MemInfoEntryExtended`]
/// documentation for more information).
///
/// This parser struct works on string slices and just owns a reference to `/proc/meminfo` buffered
/// bytes (see [`MemInfo`]). This means that no heap allocations are performed during the parsing
/// operation.
///
/// [`MemInfo`]: [`crate::MemInfo`]
#[derive(Debug)]
pub(crate) struct MemInfoParserExtended<'m> {
    /// The actual `/proc/meminfo` parser.
    parser: MemInfoParser<'m>,
}

impl<'m> MemInfoParserExtended<'m> {
    /// Constructs a new instance of the parser from `/proc/meminfo` data `bytes`.
    #[inline]
    pub(crate) fn new(bytes: &'m [u8]) -> Self {
        Self {
            parser: MemInfoParser::new(bytes),
        }
    }
}

impl<'m> From<&'m str> for MemInfoParserExtended<'m> {
    #[inline]
    fn from(string: &'m str) -> Self {
        MemInfoParserExtended::new(string.as_bytes())
    }
}

impl<'m> Iterator for MemInfoParserExtended<'m> {
    type Item = MemInfoEntryExtended<'m>;

    fn next(&mut self) -> Option<Self::Item> {
        self.parser.is_not_eof().then(|| {
            let start = self.parser.cursor;
            let label = self.parser.get_label();
            let size = self.parser.get_size();
            let unit = self.parser.get_unit();
            let end = self.parser.cursor;

            #[cfg(not(feature = "utf8-unchecked"))]
            let entry = MemInfoEntry::new(label, size, unit);

            #[cfg(feature = "utf8-unchecked")]
            let entry = unsafe { MemInfoEntry::new_unchecked(label, size, unit) };

            MemInfoEntryExtended::new(entry, start, end)
        })
    }
}

// -----------------------------------------------------------------------------------------------
// -- Unit testing module --
// -----------------------------------------------------------------------------------------------
#[cfg(test)]
mod tests {
    use super::*;

    const MEMINFO: &'static str = r#"MemTotal:       16333776 kB
MemFree:        11779556 kB
MemAvailable:   12900200 kB
Buffers:          149028 kB
SwapTotal:      16777212 kB
SwapFree:       16777212 kB
HugePages_Surp:        0
"#;

    #[test]
    fn parse_entries() {
        let mut parser = MemInfoParser::from(MEMINFO);

        assert_eq!(
            Some(MemInfoEntry {
                label: "MemTotal",
                size: "16333776",
                unit: Some("kB"),
            }),
            parser.next(),
        );

        assert_eq!(
            Some(MemInfoEntry {
                label: "MemFree",
                size: "11779556",
                unit: Some("kB"),
            }),
            parser.next(),
        );

        assert_eq!(
            Some(MemInfoEntry {
                label: "MemAvailable",
                size: "12900200",
                unit: Some("kB"),
            }),
            parser.next(),
        );

        assert_eq!(
            Some(MemInfoEntry {
                label: "Buffers",
                size: "149028",
                unit: Some("kB"),
            }),
            parser.next(),
        );

        assert_eq!(
            Some(MemInfoEntry {
                label: "SwapTotal",
                size: "16777212",
                unit: Some("kB"),
            }),
            parser.next(),
        );

        assert_eq!(
            Some(MemInfoEntry {
                label: "SwapFree",
                size: "16777212",
                unit: Some("kB"),
            }),
            parser.next(),
        );

        assert_eq!(
            Some(MemInfoEntry {
                label: "HugePages_Surp",
                size: "0",
                unit: None,
            }),
            parser.next(),
        );

        assert_eq!(None, parser.next());
    }

    #[test]
    fn parse_entries_extended() {
        let entries = MEMINFO.lines().collect::<Vec<&str>>();
        let mut parser = MemInfoParserExtended::from(MEMINFO);

        let start = 0;
        let end = entries[0].len();
        assert_eq!(
            Some(MemInfoEntryExtended {
                entry: MemInfoEntry {
                    label: "MemTotal",
                    size: "16333776",
                    unit: Some("kB"),
                },
                range: start..end,
            }),
            parser.next(),
        );

        let start = end + 1;
        let end = start + entries[1].len();
        assert_eq!(
            Some(MemInfoEntryExtended {
                entry: MemInfoEntry {
                    label: "MemFree",
                    size: "11779556",
                    unit: Some("kB"),
                },
                range: start..end,
            }),
            parser.next(),
        );

        let start = end + 1;
        let end = start + entries[2].len();
        assert_eq!(
            Some(MemInfoEntryExtended {
                entry: MemInfoEntry {
                    label: "MemAvailable",
                    size: "12900200",
                    unit: Some("kB"),
                },
                range: start..end,
            }),
            parser.next(),
        );

        let start = end + 1;
        let end = start + entries[3].len();
        assert_eq!(
            Some(MemInfoEntryExtended {
                entry: MemInfoEntry {
                    label: "Buffers",
                    size: "149028",
                    unit: Some("kB"),
                },
                range: start..end,
            }),
            parser.next(),
        );

        let start = end + 1;
        let end = start + entries[4].len();
        assert_eq!(
            Some(MemInfoEntryExtended {
                entry: MemInfoEntry {
                    label: "SwapTotal",
                    size: "16777212",
                    unit: Some("kB"),
                },
                range: start..end,
            }),
            parser.next(),
        );

        let start = end + 1;
        let end = start + entries[5].len();
        assert_eq!(
            Some(MemInfoEntryExtended {
                entry: MemInfoEntry {
                    label: "SwapFree",
                    size: "16777212",
                    unit: Some("kB"),
                },
                range: start..end,
            }),
            parser.next(),
        );

        let start = end + 1;
        let end = start + entries[6].len();
        assert_eq!(
            Some(MemInfoEntryExtended {
                entry: MemInfoEntry {
                    label: "HugePages_Surp",
                    size: "0",
                    unit: None,
                },
                range: start..end,
            }),
            parser.next(),
        );

        assert_eq!(None, parser.next());
    }
}
