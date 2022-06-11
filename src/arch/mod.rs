#[cfg(feature = "6502")]
#[path = "6502.rs"]
pub mod _6502;

#[cfg(feature = "riscv")]
pub mod riscv;
