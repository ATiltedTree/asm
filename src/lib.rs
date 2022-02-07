//! Decoding and encoding of assembly
//!
//! # Example
//!
//! ## Decode `6502` assembly
//!
//! ```
//! let assembly = [0x65, 0x83, 0x31];
//!
//! let decoder = asm::Architecture::_6502.decoder(assembly.into_iter());
//!
//! for instruction in decoder {
//!     println!("{:?}", instruction);
//! }
//! ```

#![no_std]
#![deny(missing_docs)]

use core::fmt;

mod arch;
pub use arch::*;

#[cfg(not(any(feature = "6502")))]
compile_error!("At least one architecture needs to be enabled");

/// Architectures known by this crate
#[non_exhaustive]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Architecture {
    /// The 6502 ISA
    #[cfg(feature = "6502")]
    _6502,
}

impl Architecture {
    /// Create a decoder for this architecture.
    #[cfg(feature = "decode")]
    pub fn decoder(&self, it: impl Iterator<Item = u8>) -> impl Decoder {
        match self {
            #[cfg(feature = "6502")]
            Self::_6502 => _6502::Decoder::new(it),
        }
    }
}

/// A instruction decoder
#[cfg(feature = "decode")]
pub trait Decoder: Iterator<Item = Result<Self::Instruction, Self::Error>> {
    /// The instruction produced by this decoder
    type Instruction: fmt::Debug;

    /// Errors produced during decoding
    type Error: fmt::Debug;
}
