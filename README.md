Assembly
========

A Rust library for decoding and encoding assembly of various architectures.

Supported architectures currently include:

- `6502`

## Cargo Features

Every architecture has a feature. This allows you to only enable the
architectures you need.

For example `6502` support would be enabled by adding this to your `Cargo.toml`:

```toml
[dependencies.asm]
version = "0.1"
features = ["6502"]
```

## Example

### Decoding

```rust
use asm::{_6502, Decoder};
let assembly = [0x65, 0x83, 0x31];

let mut decoder = _6502::Decoder::new(&assembly[..]);

println!("{:?}", decoder.decode())
```

### Encoding

```rust
use asm::{_6502, Encoder};
let mut assembly = [0u8; 1];

let mut encoder = _6502::Encoder::new(&mut assembly[..]);

encoder.encode(_6502::Instruction::BRK(_6502::Addressing::Implied(())));
```

#### License

<sup>
Licensed under either of <a href="LICENSE-APACHE">Apache License, Version
2.0</a> or <a href="LICENSE-MIT">MIT license</a> at your option.
</sup>

<br>

<sub>
Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in this crate by you, as defined in the Apache-2.0 license, shall
be dual licensed as above, without any additional terms or conditions.
</sub>
