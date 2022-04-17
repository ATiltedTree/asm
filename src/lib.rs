//! Decoding and encoding of assembly
//!
//! # Example
//!
//! ## Decode `6502` assembly
//!
//! ```
//! # use asm::{_6502, Decode};
//! let assembly = [0x65, 0x83, 0x31];
//!
//! let mut decoder = _6502::Decoder::new(&assembly[..]);
//!
//! println!("{:?}", decoder.decode())
//! ```
//!
//! ## Encode `6502` assembly
//!
//! ```
//! # use asm::{_6502, Encode};
//! let mut assembly = [0u8; 1];
//!
//! let mut encoder = _6502::Encoder::new(&mut assembly[..]);
//!
//! encoder.encode(_6502::Instruction::BRK(_6502::Addressing::Implied(())));
//! ```

#![deny(missing_docs)]

mod arch;
pub use arch::*;

/// Architectures known by this crate
#[non_exhaustive]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Architecture {
    /// The 6502 ISA
    #[cfg(feature = "6502")]
    _6502,
}

#[cfg(feature = "decode")]
#[doc(inline)]
pub use decode::Decode;

/// Decode related things
#[cfg(feature = "decode")]
pub mod decode {
    use std::io::SeekFrom;

    /// A instruction decoder
    pub trait Decode {
        /// The instruction produced by this decoder
        type Instruction: core::fmt::Debug;

        /// Errors produced during decoding
        type Error: core::fmt::Debug + std::error::Error;

        /// Decode a instruction
        fn decode(&mut self) -> Option<Result<Self::Instruction, Self::Error>>;

        /// Turn this decoder into a [`Iterator`] yielding `Result<Self::Instruction, Self::Error>`
        fn into_iter(self) -> Iter<Self>
        where
            Self: Sized,
        {
            Iter(self)
        }
    }

    /// [`Seek`] support for [`Decode`]
    pub trait Seek: Decode {
        /// Seek to an offest, in bytes, in a stream.
        fn seek(&mut self, pos: SeekFrom) -> Result<u64, Self::Error>;
    }

    /// A Decoder as [`Iterator`]
    /// See [`Decode::into_iter`] for more info
    pub struct Iter<D>(D);

    impl<D: Decode> Iterator for Iter<D> {
        type Item = Result<D::Instruction, D::Error>;

        fn next(&mut self) -> Option<Self::Item> {
            self.0.decode()
        }
    }
}

/// A instruction encoder
#[cfg(feature = "encode")]
pub trait Encode {
    /// The instruction produced by this decoder
    type Instruction: core::fmt::Debug;

    /// Errors produced during decoding
    type Error: core::fmt::Debug + std::error::Error;

    /// Encode a instruction
    fn encode(&mut self, inst: Self::Instruction) -> Result<(), Self::Error>;
}
