Assembly
========

A Rust library for decoding and encoding assembly of various architectures.

Supported architectures currently include:

- `6502`

## Cargo Features

- `encode` allows for encoding of instructions
- `decode` allows for decoding of instructions

In addition every architecture has a feature. This allows you to only enable the
architectures you need.

For example `6502` support would be enabled by adding this to your `Cargo.toml`:

```toml
[dependencies.asm]
version = "0.1"
features = ["6502"]
```

## Example

```rust
let assembly = [...];

let decoder = asm::Architecture::_6502::decoder(&assembly);

for instruction in decoder {
    println!("{:?}", instruction);
}
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
