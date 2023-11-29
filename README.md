<div align="center">
  <h1 align="center">Linux MemInfo</h1>

  ![GitHub source size](https://img.shields.io/github/languages/code-size/marcoradocchia/linux-meminfo?color=ea6962&logo=github)
  ![GitHub open issues](https://img.shields.io/github/issues-raw/marcoradocchia/linux-meminfo?color=%23d8a657&logo=github)
  ![GitHub open pull requests](https://img.shields.io/github/issues-pr-raw/marcoradocchia/linux-meminfo?color=%2389b482&logo=github)
  ![GitHub sponsors](https://img.shields.io/github/sponsors/marcoradocchia?color=%23d3869b&logo=github)
  ![GitHub license](https://img.shields.io/github/license/marcoradocchia/linux-meminfo?color=%23e78a4e)
  ![Crates.io downloads](https://img.shields.io/crates/d/linux-meminfo?label=crates.io%20downloads&color=%23a9b665&logo=rust)
  ![Crates.io version](https://img.shields.io/crates/v/linux-meminfo?logo=rust&color=%23d8a657)
</div>

This library provides easy and low level access to `meminfo`, the _pseudofile_
placed by the Linux kernel inside the `proc` _pseudo-filesystem_ (for more
information, see the `proc`
[manpage](https://man7.org/linux/man-pages/man5/proc.5.html)).

The public API is built around the `MemInfo` type, a struct responsible for
retrieving memory-related information about the system. Calling its constructor
opens the `/proc/meminfo` pseudofile and reads its data into an internal buffer.
Having `MemInfo` to own both the open file and a buffer of its data allows
separation of concerns between _reading_ from the pseudofile, _managing_ and
_parsing_ the buffered data.

The parser implementation responsible for parsing `/proc/meminfo` entries
works exclusively on string slices, just owning a reference to the pseudofile
buffered bytes. This allows for efficient, **zero-allocation** parsing.

## Examples

The following example shows the most basic usage of the `MemInfo` API. First
we construct a new instance, which translates to `/proc/meminfo` being opened
and read into the internal buffer; then we call the `MemInfo::parse`, which
returns a **lazy** iterator over parsed entries, in this case represented by
the `MemInfoEntry` type. The iterator being lazy meaning it parses a new
entry on each call to the `next` method. In other words: _pay only for the
entries you parse_.

```rust
use std::error;

use meminfo::MemInfo;

fn main() -> Result<(), Box<dyn error::Error>> {
    let mut meminfo = MemInfo::new()?;
    let mut entries = meminfo.parse();

    let mem_total = entries.next().unwrap();
    assert_eq!("MemTotal", mem_total.label());
    assert_eq!(Some("kB"), mem_total.unit());

    println!("System's total usable RAM: {}kB", mem_total.size()?);

    Ok(())
}
```

In certain scenarios, users may have distinct use cases that necessitate regular
retrieval of a particular set of entries within the `/proc/meminfo` pseudofile.
The `MemInfo::parse_extended` addresses this requirement in an efficient
fashion, extending parsed entries with additional information pertaining to the
byte range they occupy in the file stream. This functionality allows users to
selectively read and parse specific entries as needed. Also, this way, the
internal buffer can be shrank to the capacity required to read in such entries,
reducing the runtime memory footprint of the program. Below a minimal example:

```rust
use std::io::SeekFrom;
use std::time::Duration;
use std::{error, thread};

use meminfo::{MemInfo, MemInfoError};

#[derive(Debug)]
struct MemAvailable {
    size: usize,
    start_pos: usize,
}

impl MemAvailable {
    fn new(meminfo: &mut MemInfo) -> Result<Self, MemInfoError> {
        let mut entries = meminfo.parse_extended().skip(2);

        let mem_available = entries.next().unwrap();
        assert_eq!("MemAvailable", mem_available.label());
        assert_eq!(Some("kB"), mem_available.unit());

        let size = mem_available.size().unwrap();
        let start_pos = mem_available.start_pos();
        let capacity = mem_available.required_capacity();

        drop(entries);
        meminfo.clear();
        meminfo.shrink_to(capacity);

        Ok(MemAvailable { size, start_pos })
    }

    fn fetch(&mut self, meminfo: &mut MemInfo) -> Result<(), MemInfoError> {
        let seek_pos = SeekFrom::Start(self.start_pos as u64);
        meminfo.seek(seek_pos)?;

        meminfo.clear();
        meminfo.read()?;

        let entry = meminfo.parse().next().unwrap();
        self.size = entry.size().unwrap();

        Ok(())
    }
}

fn main() -> Result<(), Box<dyn error::Error>> {
    let mut meminfo = MemInfo::new()?;
    let mut mem_available = MemAvailable::new(&mut meminfo)?;

    loop {
        println!("System's available RAM: {}kB", mem_available.size);
        thread::sleep(Duration::from_secs(2));
        mem_available.fetch(&mut meminfo)?;
    }
}
```

## Usage

To use this library in your project, run the following command in your project
root directory:

```sh
cargo add linux-meminfo
```

## Features

By default, the `MemInfoEntry` and `MemInfoEntryExtended` constructors perform
UTF-8 validation on `/proc/meminfo` parsed data. Malformed data would cause
a panic in this case. However, enabling the `utf8-unchecked` feature removes
such validation, potentially increasing parsing performance. To achieve this,
the new constructors make use of unsafe code, thus the user should be aware
that malformed `/proc/meminfo` data would cause undefined behaviour.

To opt-in such feature, run the following command in your the project root
directory:

```sh
cargo add linux-meminfo --features=utf8-unchecked
```

## License

This library is licensed under the terms of the [GPLv3](LICENSE) license.

## Contributions

Any contribution is welcome and encouraged.
