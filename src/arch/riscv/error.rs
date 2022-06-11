use thiserror::Error;

#[derive(Error, Debug)]
pub enum Error {
    #[error(
        "invalid instruction '{inst:#x?}': {opcode:07b} {funct3:03b} {funct5:05b} {funct7:07b}"
    )]
    InvalidInstruction {
        inst: u32,
        opcode: u8,
        funct3: u8,
        funct5: u8,
        funct7: u8,
    },

    /// An I/O Error was encountered during reading
    #[error(transparent)]
    IO(std::io::Error),
}
