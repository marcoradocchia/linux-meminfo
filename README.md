# Linux MemInfo

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

## Examples

The following example shows the most basic usage of the `MemInfo` API. First
we construct a new instance, which translates to `/proc/meminfo` being opened
and read into the internal buffer; then we call the `MemInfo::parse`, which
returns a **lazy** iterator over parsed entries, in this case represented by
the `MemInfoEntry` type. The iterator being lazy meaning it parses a new
entry on each call to the `next` method. In other words: you pay only for the
entries you parse.

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

## License

This library is licensed under the terms of the [GPLv3](LICENSE) license.

## Contributions

Any contribution is welcome and encouraged.
