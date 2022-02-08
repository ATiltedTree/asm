//! The 6502 ISA
//!
//! Based on the information from:
//! <https://www.nesdev.org/obelisk-6502-guide/index.html>

use std::io::Read;

macro_rules! consume {
    ($reader:ident, $size:literal) => {{
        let mut buf = [0u8; $size];
        $reader.read_exact(&mut buf).map(|_| buf)
    }};
}

macro_rules! regs {
    ($($(#[doc = $doc:expr])* $reg:ident<$size:literal>),*) => {
        /// The 6502 has only a small number of registers compared to other
        /// processor of the same era.
        ///
        /// This makes it especially challenging to
        /// program as algorithms must make efficient use of both registers and
        /// memory.
        pub enum Registers {
            $($(#[doc = $doc])* $reg),+
        }

        impl Registers {
            /// The width of a Register in bits.
            pub fn width(&self) -> usize {
                match self {
                    $(Self::$reg => $size),+
                }
            }
        }
    };
}

regs! {
    /// # Program Counter
    /// The program counter is a 16 bit register which points to the next
    /// instruction to be executed. The value of program counter is modified
    /// automatically as instructions are executed. The value of the program
    /// counter can be modified by executing a jump, a relative branch or a
    /// subroutine call to another memory address or by returning from a
    /// subroutine or interrupt.
    PC<16>,

    /// # Stack Pointer
    /// The processor supports a 256 byte stack located between `$0100` and
    /// `$01FF`. The stack pointer is an 8 bit register and holds the low 8 bits
    /// of the next free location on the stack. The location of the stack is
    /// fixed and cannot be moved.
    ///
    /// Pushing bytes to the stack causes the stack pointer to be decremented.
    /// Conversely pulling bytes causes it to be incremented.
    ///
    /// The CPU does not detect if the stack is overflowed by excessive pushing
    /// or pulling operations and will most likely result in the program
    /// crashing.
    S<8>,

    /// # Accumulator
    ///
    /// The 8 bit accumulator is used all arithmetic and logical operations
    /// (with the exception of increments and decrements). The contents of the
    /// accumulator can be stored and retrieved either from memory or the stack.
    ///
    /// Most complex operations will need to use the accumulator for arithmetic
    /// and efficient optimisation of its use is a key feature of time critical
    /// routines.
    A<8>,

    /// # Index Register X
    ///
    /// The 8 bit index register is most commonly used to hold counters or
    /// offsets for accessing memory. The value of the X register can be loaded
    /// and saved in memory, compared with values held in memory or incremented
    /// and decremented.
    ///
    /// The X register has one special function. It can be used to get a copy of
    /// the stack pointer or change its value.
    X<8>,

    /// # Index Register Y
    ///
    /// The Y register is similar to the X register in that it is available for
    /// holding counter or offsets memory access and supports the same set of
    /// memory load, save and compare operations as wells as increments and
    /// decrements. It has no special functions.
    Y<8>,

    /// # Processor Status
    ///
    /// See: [ProcessorStatus]
    P<8>
}

bitflags::bitflags! {
    /// # Processor Status
    ///
    /// As instructions are executed a set of processor flags are set or clear
    /// to record the results of the operation. This flags and some additional
    /// control flags are held in a special status register. Each flag has a
    /// single bit within the register.
    ///
    /// Instructions exist to test the values of the various bits, to set or
    /// clear some of them and to push or pull the entire set to or from the
    /// stack.
    pub struct ProcessorStatus : u8 {
        /// # Carry Flag
        ///
        /// The carry flag is set if the last operation caused an overflow from
        /// bit 7 of the result or an underflow from bit 0. This condition is
        /// set during arithmetic, comparison and during logical shifts. It can
        /// be explicitly set using the 'Set Carry Flag' (SEC) instruction and
        /// cleared with 'Clear Carry Flag' (CLC).
        const CARRY      = 0b00000001;

        /// # Zero Flag
        ///
        /// The zero flag is set if the result of the last operation as was zero.
        const ZERO       = 0b00000010;

        /// # Interrupt Disable
        ///
        /// The interrupt disable flag is set if the program has executed a 'Set
        /// Interrupt Disable' (SEI) instruction. While this flag is set the
        /// processor will not respond to interrupts from devices until it is
        /// cleared by a 'Clear Interrupt Disable' (CLI) instruction.
        const INTERRUPT  = 0b00000100;

        /// # Decimal Mode
        ///
        /// While the decimal mode flag is set the processor will obey the rules
        /// of Binary Coded Decimal (BCD) arithmetic during addition and
        /// subtraction. The flag can be explicitly set using 'Set Decimal Flag'
        /// (SED) and cleared with 'Clear Decimal Flag' (CLD).
        const DECIMAL    = 0b00001000;

        /// # Break Command
        ///
        /// The break command bit is set when a BRK instruction has been
        /// executed and an interrupt has been generated to process it.
        const BREAK      = 0b00010000;

        /// # Overflow Flag
        ///
        /// The overflow flag is set during arithmetic operations if the result
        /// has yielded an invalid 2's complement result (e.g. adding to
        /// positive numbers and ending up with a negative result: `64 + 64 =>
        /// -128`). It is determined by looking at the carry between bits 6 and
        /// 7 and between bit 7 and the carry flag.
        const OVERFLOW   = 0b00100000;

        /// # Negative Flag
        ///
        /// The negative flag is set if the result of the last operation had bit
        /// 7 set to a one.
        const NEGATIVE   = 0b01000000;
    }
}

/// The 6502 processor provides several ways in which memory locations can be
/// addressed.
///
/// Some instructions support several different modes while others
/// may only support one. In addition the two index registers can not always be
/// used interchangeably. This lack of orthogonality in the instruction set is
/// one of the features that makes the 6502 trickier to program well.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Addressing {
    /// For many 6502 instructions the source and destination of the information
    /// to be manipulated is implied directly by the function of the instruction
    /// itself and no further operand needs to be specified.
    Implied(()),

    /// Some instructions have an option to operate directly upon the
    /// accumulator.
    Accumulator(()),

    /// Immediate addressing allows the programmer to directly specify an 8 bit
    /// constant within the instruction.
    Immediate(u8),

    /// An instruction using zero page addressing mode has only an 8 bit address
    /// operand. This limits it to addressing only the first 256 bytes of memory
    /// (e.g. `$0000` to `$00FF`) where the most significant byte of the address
    /// is always zero. In zero page mode only the least significant byte of the
    /// address is held in the instruction making it shorter by one byte
    /// (important for space saving) and one less memory fetch during execution
    /// (important for speed).
    ZeroPage(u8),

    /// The address to be accessed by an instruction using indexed zero page
    /// addressing is calculated by taking the 8 bit zero page address from the
    /// instruction and adding the current value of the X register to it.
    ///
    /// NOTE: The address calculation wraps around if the sum of the base
    ///       address and the register exceed `$FF`.
    ZeroPageX(u8),

    /// The address to be accessed by an instruction using indexed zero page
    /// addressing is calculated by taking the 8 bit zero page address from the
    /// instruction and adding the current value of the Y register to it.
    ZeroPageY(u8),

    /// Relative addressing mode is used by branch instructions (e.g. BEQ, BNE,
    /// etc.) which contain a signed 8 bit relative offset (e.g. `-128` to
    /// `+127`) which is added to program counter if the condition is true.
    Relative(u8),

    /// Instructions using absolute addressing contain a full 16 bit address to
    /// identify the target location.
    Absolute(u16),

    /// The address to be accessed by an instruction using X register indexed
    /// absolute addressing is computed by taking the 16 bit address from the
    /// instruction and added the contents of the X register.
    AbsoluteX(u16),

    /// The address to be accessed by an instruction using Y register indexed
    /// absolute addressing is computed by taking the 16 bit address from the
    /// instruction and added the contents of the Y register.
    AbsoluteY(u16),

    /// The instruction contains a 16 bit address which identifies the location
    /// of the least significant byte of another 16 bit memory address which is
    /// the real target of the instruction.
    Indirect(u16),

    /// Indexed indirect addressing is normally used in conjunction with a table
    /// of address held on zero page. The address of the table is taken from the
    /// instruction and the X register added to it (with zero page wrap around)
    /// to give the location of the least significant byte of the target
    /// address.
    IndexedIndirect(u8),

    /// Indirect indirect addressing is the most common indirection mode used on
    /// the 6502. In instruction contains the zero page location of the least
    /// significant byte of 16 bit address. The Y register is dynamically added
    /// to this value to generated the actual target address for operation.
    IndirectIndexed(u8),
}

#[cfg_attr(not(feature = "decode"), allow(dead_code))]
#[cfg_attr(not(feature = "encode"), allow(dead_code))]
impl Addressing {
    /// The length a Instruction Argument takes in bytes.
    pub fn length(&self) -> usize {
        match self {
            Addressing::Implied(()) | Addressing::Accumulator(()) => 0,
            Addressing::Immediate(_)
            | Addressing::ZeroPage(_)
            | Addressing::ZeroPageX(_)
            | Addressing::ZeroPageY(_)
            | Addressing::Relative(_)
            | Addressing::IndexedIndirect(_)
            | Addressing::IndirectIndexed(_) => 1,
            Addressing::Absolute(_)
            | Addressing::AbsoluteX(_)
            | Addressing::AbsoluteY(_)
            | Addressing::Indirect(_) => 2,
        }
    }

    fn encode(self, writer: &mut impl std::io::Write) -> Result<(), Error> {
        match self {
            Addressing::Implied(()) | Addressing::Accumulator(()) => Ok(()),
            Addressing::Immediate(imm)
            | Addressing::ZeroPage(imm)
            | Addressing::ZeroPageX(imm)
            | Addressing::ZeroPageY(imm)
            | Addressing::Relative(imm)
            | Addressing::IndexedIndirect(imm)
            | Addressing::IndirectIndexed(imm) => writer.write_all(&[imm]).map_err(Error::IO),
            Addressing::Absolute(imm)
            | Addressing::AbsoluteX(imm)
            | Addressing::AbsoluteY(imm)
            | Addressing::Indirect(imm) => writer.write_all(&imm.to_le_bytes()).map_err(Error::IO),
        }
    }

    fn implied(_: &mut impl Read) -> Result<Self, Error> {
        Ok(Self::Implied(()))
    }
    fn accumulator(_: &mut impl Read) -> Result<Self, Error> {
        Ok(Self::Accumulator(()))
    }

    fn immediate(it: &mut impl Read) -> Result<Self, Error> {
        let imm = consume!(it, 1);
        imm.map(|x| Self::Immediate(x[0])).map_err(Error::IO)
    }

    fn zero_page(it: &mut impl Read) -> Result<Self, Error> {
        let imm = consume!(it, 1);
        imm.map(|x| Self::ZeroPage(x[0])).map_err(Error::IO)
    }
    fn zero_page_x(it: &mut impl Read) -> Result<Self, Error> {
        let imm = consume!(it, 1);
        imm.map(|x| Self::ZeroPageX(x[0])).map_err(Error::IO)
    }
    fn zero_page_y(it: &mut impl Read) -> Result<Self, Error> {
        let imm = consume!(it, 1);
        imm.map(|x| Self::ZeroPageY(x[0])).map_err(Error::IO)
    }

    fn relative(it: &mut impl Read) -> Result<Self, Error> {
        let imm = consume!(it, 1);
        imm.map(|x| Self::Relative(x[0])).map_err(Error::IO)
    }

    fn absolute(it: &mut impl Read) -> Result<Self, Error> {
        let imm = consume!(it, 2);
        imm.map(|x| Self::Absolute(u16::from_le_bytes(x)))
            .map_err(Error::IO)
    }
    fn absolute_x(it: &mut impl Read) -> Result<Self, Error> {
        let imm = consume!(it, 2);
        imm.map(|x| Self::AbsoluteX(u16::from_le_bytes(x)))
            .map_err(Error::IO)
    }
    fn absolute_y(it: &mut impl Read) -> Result<Self, Error> {
        let imm = consume!(it, 2);
        imm.map(|x| Self::AbsoluteY(u16::from_le_bytes(x)))
            .map_err(Error::IO)
    }

    fn indirect(it: &mut impl Read) -> Result<Self, Error> {
        let imm = consume!(it, 2);
        imm.map(|x| Self::Indirect(u16::from_le_bytes(x)))
            .map_err(Error::IO)
    }

    fn indexed_indirect(it: &mut impl Read) -> Result<Self, Error> {
        let imm = consume!(it, 1);
        imm.map(|x| Self::IndexedIndirect(x[0])).map_err(Error::IO)
    }
    fn indirect_indexed(it: &mut impl Read) -> Result<Self, Error> {
        let imm = consume!(it, 1);
        imm.map(|x| Self::IndirectIndexed(x[0])).map_err(Error::IO)
    }
}

/// Errors produced during decoding
#[derive(Debug, thiserror::Error)]
pub enum Error {
    /// A invalid opcode was encountered
    #[error("invalid opcode {0:#x?}")]
    InvalidOpcode(u8),

    /// A instruction with an invalid addressing mode was encoutered
    #[error("invalid addressing for instruction {0:?}")]
    InvalidAddressing(Instruction),

    /// An I/O Error was encountered during reading
    #[error(transparent)]
    IO(std::io::Error),
}

macro_rules! inst {
    ($($(#[doc = $doc:expr])* $name:ident),+,) => {
        /// A 6502 instruction
        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        pub enum Instruction {
            $($(#[doc = $doc])* $name(Addressing)),+
        }

        impl Instruction {
            /// The [Addressing] of a instruction.
            pub fn addressing(&self) -> Addressing {
                match self {
                    $(Self::$name(addr) => *addr),+
                }
            }
            /// The length a instruction takes up in bytes.
            pub fn length(&self) -> usize {
                self.addressing().length() + 1
            }
        }
    };
}

inst! {
    /// # Add with Carry
    ///
    /// This instruction adds the contents of a memory location to the
    /// accumulator together with the carry bit. If overflow occurs the carry
    /// bit is set, this enables multiple byte addition to be performed.
    ADC,

    /// # Logical AND
    ///
    /// A logical AND is performed, bit by bit, on the accumulator contents
    /// using the contents of a byte of memory.
    AND,

    /// # Arithmetic Shift Left
    ///
    /// This operation shifts all the bits of the accumulator or memory contents
    /// one bit left. Bit 0 is set to 0 and bit 7 is placed in the carry flag.
    /// The effect of this operation is to multiply the memory contents by 2
    /// (ignoring 2's complement considerations), setting the carry if the
    /// result will not fit in 8 bits.
    ASL,

    /// # Branch if Carry Clear
    ///
    /// If the carry flag is clear then add the relative displacement to the
    /// program counter to cause a branch to a new location.
    BCC,

    /// # Branch if Carry Set
    ///
    /// If the carry flag is set then add the relative displacement to the
    /// program counter to cause a branch to a new location.
    BCS,

    /// # Branch if Equal
    ///
    /// If the zero flag is set then add the relative displacement to the
    /// program counter to cause a branch to a new location.
    BEQ,

    /// # Bit Test
    ///
    /// This instructions is used to test if one or more bits are set in a
    /// target memory location. The mask pattern in A is ANDed with the value in
    /// memory to set or clear the zero flag, but the result is not kept. Bits 7
    /// and 6 of the value from memory are copied into the N and V flags.
    BIT,

    /// # Branch if Minus
    ///
    /// If the negative flag is set then add the relative displacement to the
    /// program counter to cause a branch to a new location.
    BMI,

    /// # Branch if Not Equal
    ///
    /// If the zero flag is clear then add the relative displacement to the
    /// program counter to cause a branch to a new location.
    BNE,

    /// # Branch if Positive
    ///
    /// If the negative flag is clear then add the relative displacement to the
    /// program counter to cause a branch to a new location.
    BPL,

    /// # Force Interrupt
    ///
    /// The BRK instruction forces the generation of an interrupt request. The
    /// program counter and processor status are pushed on the stack then the
    /// IRQ interrupt vector at `$FFFE/F` is loaded into the PC and the break
    /// flag in the status set to one.
    BRK,

    /// # Branch if Overflow Clear
    ///
    /// If the overflow flag is clear then add the relative displacement to the
    /// program counter to cause a branch to a new location.
    BVC,

    /// # Branch if Overflow Set
    ///
    /// If the overflow flag is set then add the relative displacement to the
    /// program counter to cause a branch to a new location.
    BVS,

    /// # Clear Carry Flag
    ///
    /// Set the carry flag to zero.
    CLC,

    /// # Clear Decimal Mode
    ///
    /// Sets the decimal mode flag to zero.
    CLD,

    /// # Clear Interrupt Disable
    ///
    /// Clears the interrupt disable flag allowing normal interrupt requests to
    /// be serviced.
    CLI,

    /// # Clear Overflow Flag
    ///
    /// Clears the overflow flag.
    CLV,

    /// # Compare
    ///
    /// This instruction compares the contents of the accumulator with another
    /// memory held value and sets the zero and carry flags as appropriate.
    CMP,

    /// # Compare X Register
    ///
    /// This instruction compares the contents of the X register with another
    /// memory held value and sets the zero and carry flags as appropriate.
    CPX,

    /// # Compare Y Register
    ///
    /// This instruction compares the contents of the Y register with another
    /// memory held value and sets the zero and carry flags as appropriate.
    CPY,

    /// # Decrement Memory
    ///
    /// Subtracts one from the value held at a specified memory location setting
    /// the zero and negative flags as appropriate.
    DEC,

    /// # Decrement X Register
    ///
    /// Subtracts one from the X register setting the zero and negative flags as
    /// appropriate.
    DEX,

    /// # Decrement Y Register
    ///
    /// Subtracts one from the Y register setting the zero and negative flags as
    /// appropriate.
    DEY,

    /// # Exclusive OR
    ///
    /// An exclusive OR is performed, bit by bit, on the accumulator contents
    /// using the contents of a byte of memory.
    EOR,

    /// # Increment Memory
    ///
    /// Adds one to the value held at a specified memory location setting the
    /// zero and negative flags as appropriate.
    INC,

    /// # Increment X Register
    ///
    /// Adds one to the X register setting the zero and negative flags as
    /// appropriate.
    INX,

    /// # Increment Y Register
    ///
    /// Adds one to the Y register setting the zero and negative flags as
    /// appropriate.
    INY,

    /// # Jump
    ///
    /// Sets the program counter to the address specified by the operand.
    JMP,

    /// # Jump to Subroutine
    ///
    /// The JSR instruction pushes the address (minus one) of the return point
    /// on to the stack and then sets the program counter to the target memory
    /// address.
    JSR,

    /// # Load Accumulator
    ///
    /// Loads a byte of memory into the accumulator setting the zero and
    /// negative flags as appropriate.
    LDA,

    /// # Load X Register
    ///
    /// Loads a byte of memory into the X register setting the zero and negative
    /// flags as appropriate.
    LDX,

    /// # Load Y Register
    ///
    /// Loads a byte of memory into the Y register setting the zero and negative
    /// flags as appropriate.
    LDY,

    /// # Logical Shift Right
    ///
    /// Each of the bits in A or M is shift one place to the right. The bit that
    /// was in bit 0 is shifted into the carry flag. Bit 7 is set to zero.
    LSR,

    /// # No Operation
    ///
    /// The NOP instruction causes no changes to the processor other than the
    /// normal incrementing of the program counter to the next instruction.
    NOP,

    /// # Logical Inclusive OR
    ///
    /// An inclusive OR is performed, bit by bit, on the accumulator contents
    /// using the contents of a byte of memory.
    ORA,

    /// # Push Accumulator
    ///
    /// Pushes a copy of the accumulator on to the stack.
    PHA,

    /// # Push Processor Status
    ///
    /// Pushes a copy of the status flags on to the stack.
    PHP,

    /// # Pull Accumulator
    ///
    /// Pulls an 8 bit value from the stack and into the accumulator. The zero
    /// and negative flags are set as appropriate.
    PLA,

    /// # Pull Processor Status
    ///
    /// Pulls an 8 bit value from the stack and into the processor flags. The
    /// flags will take on new states as determined by the value pulled.
    PLP,

    /// # Rotate Left
    ///
    /// Move each of the bits in either A or M one place to the left. Bit 0 is
    /// filled with the current value of the carry flag whilst the old bit 7
    /// becomes the new carry flag value.
    ROL,

    /// # Rotate Right
    ///
    /// Move each of the bits in either A or M one place to the right. Bit 7 is
    /// filled with the current value of the carry flag whilst the old bit 0
    /// becomes the new carry flag value.
    ROR,

    /// # Return from Interrupt
    ///
    /// The RTI instruction is used at the end of an interrupt processing
    /// routine. It pulls the processor flags from the stack followed by the
    /// program counter.
    RTI,

    /// # Return from Subroutine
    ///
    /// The RTS instruction is used at the end of a subroutine to return to the
    /// calling routine. It pulls the program counter (minus one) from the
    /// stack.
    RTS,

    /// # Subtract with Carry
    ///
    /// This instruction subtracts the contents of a memory location to the
    /// accumulator together with the not of the carry bit. If overflow occurs
    /// the carry bit is clear, this enables multiple byte subtraction to be
    /// performed.
    SBC,

    /// # Set Carry Flag
    ///
    /// Set the carry flag to one.
    SEC,

    /// # Set Decimal Flag
    ///
    /// Set the decimal mode flag to one.
    SED,

    /// # Set Interrupt Disable
    ///
    /// Set the interrupt disable flag to one.
    SEI,

    /// # Store Accumulator
    ///
    /// Stores the contents of the accumulator into memory.
    STA,

    /// # Store X Register
    ///
    /// Stores the contents of the X register into memory.
    STX,

    /// # Store Y Register
    ///
    /// Stores the contents of the Y register into memory.
    STY,

    /// # Transfer Accumulator to X
    ///
    /// Copies the current contents of the accumulator into the X register and
    /// sets the zero and negative flags as appropriate.
    TAX,

    /// # Transfer Accumulator to Y
    ///
    /// Copies the current contents of the accumulator into the Y register and
    /// sets the zero and negative flags as appropriate.
    TAY,

    /// # Transfer Stack Pointer to X
    ///
    /// Copies the current contents of the stack register into the X register
    /// and sets the zero and negative flags as appropriate.
    TSX,

    /// # Transfer X to Accumulator
    ///
    /// Copies the current contents of the X register into the accumulator and
    /// sets the zero and negative flags as appropriate.
    TXA,

    /// # Transfer X to Stack Pointer
    ///
    /// Copies the current contents of the X register into the stack register.
    TXS,

    /// # Transfer Y to Accumulator
    ///
    /// Copies the current contents of the Y register into the accumulator and
    /// sets the zero and negative flags as appropriate.
    TYA,
}

macro_rules! implementation {
    ($($op:literal => $inst:ident($dec:ident, $enc:ident)),+,) => {
        #[cfg(feature = "decode")]
        pub use decode::Decoder;
        #[cfg(feature = "decode")]
        mod decode {
            use super::*;
            use std::io::{Read, Seek, SeekFrom};
            /// A decoder for 6502 instructions
            pub struct Decoder<T: Read>(T, bool);

            impl<T: Read> Decoder<T> {
                /// Create a new decoder from a byte stream
                pub fn new(inner: T) -> Self {
                    Self(inner, false)
                }
            }

            impl<T: Read> crate::Decoder for Decoder<T> {
                type Instruction = Instruction;
                type Error = Error;

                fn decode(&mut self) -> Option<Result<Self::Instruction, Self::Error>> {
                    use std::io::ErrorKind;
                    if self.1 == true {return None;}
                    let mut opcode = [0u8];
                    let res = self.0.read_exact(&mut opcode);
                    if let Err(err) = res {
                        // We reached the end. Stop the iterator with None.
                        if err.kind() == ErrorKind::UnexpectedEof {
                            return None;
                        } else {
                            // We got an error that is not EOF. Report it.
                            return Some(Err(Error::IO(err)));
                        }
                    }

                    let inst = match opcode[0] {
                        $(
                            $op => Addressing::$dec(&mut self.0).map(Instruction::$inst)
                        ),+,
                        x => {
                            self.1 = true;
                            Err(Error::InvalidOpcode(x))
                        }
                    };
                    Some(inst)

                }
            }

            impl<T: Read + Seek> crate::decode::Seek for Decoder<T> {
                fn seek(&mut self, pos: SeekFrom) -> Result<u64, Self::Error> {
                    self.0.seek(pos).map_err(Error::IO)
                }
            }
        }

        #[cfg(feature = "encode")]
        pub use encode::Encoder;
        #[cfg(feature = "encode")]
        mod encode {
            use super::*;
            /// A encoder for 6502 instructions
            pub struct Encoder<T: std::io::Write>(T);

            impl<T: std::io::Write> Encoder<T> {
                /// Create a new encoder from a writer
                pub fn new(inner: T) -> Self {
                    Self(inner)
                }
            }

            impl<T: std::io::Write> crate::Encoder for Encoder<T> {
                type Instruction = Instruction;

                type Error = Error;

                fn encode(&mut self, inst: Self::Instruction) -> Result<(), Self::Error> {
                    let op = match &inst {
                        $(Instruction::$inst(Addressing::$enc(..)) => $op,)+
                        other => return Err(Error::InvalidAddressing(*other)),
                    };
                    self.0.write_all(&[op]).map_err(Error::IO)?;
                    inst.addressing().encode(&mut self.0)?;
                    Ok(())
                }
            }
        }
    };
}

implementation! {
    // ADC
    0x69 => ADC(immediate, Immediate),
    0x65 => ADC(zero_page, ZeroPage),
    0x75 => ADC(zero_page_x, ZeroPageX),
    0x6D => ADC(absolute, Absolute),
    0x7D => ADC(absolute_x, AbsoluteX),
    0x79 => ADC(absolute_y, AbsoluteY),
    0x61 => ADC(indexed_indirect, IndexedIndirect),
    0x71 => ADC(indirect_indexed, IndirectIndexed),

    // AND
    0x29 => AND(immediate, Immediate),
    0x25 => AND(zero_page, ZeroPage),
    0x35 => AND(zero_page_x, ZeroPageX),
    0x2D => AND(absolute, Absolute),
    0x3D => AND(absolute_x, AbsoluteX),
    0x39 => AND(absolute_y, AbsoluteY),
    0x21 => AND(indexed_indirect, IndexedIndirect),
    0x31 => AND(indirect_indexed, IndirectIndexed),

    // ASL
    0x0A => ASL(accumulator, Accumulator),
    0x06 => ASL(zero_page, ZeroPage),
    0x16 => ASL(zero_page_x, ZeroPageX),
    0x0E => ASL(absolute, Absolute),
    0x1E => ASL(absolute_x, AbsoluteX),

    // BCC
    0x90 => BCC(relative, Relative),

    // BCS
    0xB0 => BCS(relative, Relative),

    // BEQ
    0xF0 => BEQ(relative, Relative),

    // BIT
    0x24 => BIT(zero_page, ZeroPage),
    0x2C => BIT(absolute, Absolute),

    // BMI
    0x30 => BMI(relative, Relative),

    // BNE
    0xD0 => BNE(relative, Relative),

    // BPL
    0x10 => BPL(relative, Relative),

    // BRK
    0x00 => BRK(implied, Implied),

    // BVC
    0x50 => BVC(relative, Relative),

    // BVS
    0x70 => BVS(relative, Relative),

    // CLC
    0x18 => CLC(implied, Implied),

    // CLD
    0xD8 => CLD(implied, Implied),

    // CLI
    0x58 => CLI(implied, Implied),

    // CLV
    0xB8 => CLV(implied, Implied),

    // CMP
    0xC9 => CMP(immediate, Immediate),
    0xC5 => CMP(zero_page, ZeroPage),
    0xD5 => CMP(zero_page_x, ZeroPageX),
    0xCD => CMP(absolute, Absolute),
    0xDD => CMP(absolute_x, AbsoluteX),
    0xD9 => CMP(absolute_y, AbsoluteY),
    0xC1 => CMP(indirect_indexed, IndirectIndexed),
    0xD1 => CMP(indexed_indirect, IndexedIndirect),

    // CPX
    0xE0 => CPX(immediate, Immediate),
    0xE4 => CPX(zero_page, ZeroPage),
    0xEC => CPX(absolute, Absolute),

    // CPY
    0xC0 => CPY(immediate, Immediate),
    0xC4 => CPY(zero_page, ZeroPage),
    0xCC => CPY(absolute, Absolute),

    // DEC
    0xC6 => DEC(zero_page, ZeroPage),
    0xD6 => DEC(zero_page_x, ZeroPageX),
    0xCE => DEC(absolute, Absolute),
    0xDE => DEC(absolute_x, AbsoluteX),

    // DEX
    0xCA => DEX(implied, Implied),

    // DEY
    0x88 => DEY(implied, Implied),

    // EOR
    0x49 => EOR(immediate, Immediate),
    0x45 => EOR(zero_page, ZeroPage),
    0x55 => EOR(zero_page_x, ZeroPageX),
    0x4D => EOR(absolute, Absolute),
    0x5D => EOR(absolute_x, AbsoluteX),
    0x59 => EOR(absolute_y, AbsoluteY),
    0x41 => EOR(indirect_indexed, IndirectIndexed),
    0x51 => EOR(indexed_indirect, IndexedIndirect),

    // INC
    0xE6 => INC(zero_page, ZeroPage),
    0xF6 => INC(zero_page_x, ZeroPageX),
    0xEE => INC(absolute, Absolute),
    0xFE => INC(absolute_x, AbsoluteX),

    // INX
    0xE8 => INX(implied, Implied),

    // INY
    0xC8 => INY(implied, Implied),

    // JMP
    0x4C => JMP(absolute, Absolute),
    0x6C => JMP(indirect, Indirect),

    // JSR
    0x20 => JSR(absolute, Absolute),

    // LDA
    0xA9 => LDA(immediate, Immediate),
    0xA5 => LDA(zero_page, ZeroPage),
    0xB5 => LDA(zero_page_x, ZeroPageX),
    0xAD => LDA(absolute, Absolute),
    0xBD => LDA(absolute_x, AbsoluteX),
    0xB9 => LDA(absolute_y, AbsoluteY),
    0xA1 => LDA(indirect_indexed, IndirectIndexed),
    0xB1 => LDA(indexed_indirect, IndexedIndirect),

    // LDX
    0xA2 => LDX(immediate, Immediate),
    0xA6 => LDX(zero_page, ZeroPage),
    0xB6 => LDX(zero_page_y, ZeroPageY),
    0xAE => LDX(absolute, Absolute),
    0xBE => LDX(absolute_y, AbsoluteY),

    // LDY
    0xA0 => LDY(immediate, Immediate),
    0xA4 => LDY(zero_page, ZeroPage),
    0xB4 => LDY(zero_page_x, ZeroPageX),
    0xAC => LDY(absolute, Absolute),
    0xBC => LDY(absolute_x, AbsoluteX),

    // LSR
    0x4A => LSR(accumulator, Accumulator),
    0x46 => LSR(zero_page, ZeroPage),
    0x56 => LSR(zero_page_x, ZeroPageX),
    0x4E => LSR(absolute, Absolute),
    0x5E => LSR(absolute_x, AbsoluteX),

    // NOP
    0xEA => NOP(implied, Implied),

    // ORA
    0x09 => ORA(immediate, Immediate),
    0x05 => ORA(zero_page, ZeroPage),
    0x15 => ORA(zero_page_x, ZeroPageX),
    0x0D => ORA(absolute, Absolute),
    0x1D => ORA(absolute_x, AbsoluteX),
    0x19 => ORA(absolute_y, AbsoluteY),
    0x01 => ORA(indirect_indexed, IndirectIndexed),
    0x11 => ORA(indexed_indirect, IndexedIndirect),

    // PHA
    0x48 => PHA(implied, Implied),

    // PHP
    0x08 => PHP(implied, Implied),

    // PLA
    0x68 => PLA(implied, Implied),

    // PLP
    0x28 => PLP(implied, Implied),

    // ROL
    0x2A => ROL(accumulator, Accumulator),
    0x26 => ROL(zero_page, ZeroPage),
    0x36 => ROL(zero_page_x, ZeroPageX),
    0x2E => ROL(absolute, Absolute),
    0x3E => ROL(absolute_x, AbsoluteX),

    // ROR
    0x6A => ROR(accumulator, Accumulator),
    0x66 => ROR(zero_page, ZeroPage),
    0x76 => ROR(zero_page_x, ZeroPageX),
    0x6E => ROR(absolute, Absolute),
    0x7E => ROR(absolute_x, AbsoluteX),

    // RTI
    0x40 => RTI(implied, Implied),

    // RTS
    0x60 => RTS(implied, Implied),

    // SBC
    0xE9 => SBC(immediate, Immediate),
    0xE5 => SBC(zero_page, ZeroPage),
    0xF5 => SBC(zero_page_x, ZeroPageX),
    0xED => SBC(absolute, Absolute),
    0xFD => SBC(absolute_x, AbsoluteX),
    0xF9 => SBC(absolute_y, AbsoluteY),
    0xE1 => SBC(indirect_indexed, IndirectIndexed),
    0xF1 => SBC(indexed_indirect, IndexedIndirect),

    // SEC
    0x38 => SEC(implied, Implied),

    // SED
    0xF8 => SED(implied, Implied),

    // SEI
    0x78 => SEI(implied, Implied),

    // STA
    0x85 => STA(zero_page, ZeroPage),
    0x95 => STA(zero_page_x, ZeroPageX),
    0x8D => STA(absolute, Absolute),
    0x9D => STA(absolute_x, AbsoluteX),
    0x99 => STA(absolute_y, AbsoluteY),
    0x81 => STA(indirect_indexed, IndirectIndexed),
    0x91 => STA(indexed_indirect, IndexedIndirect),

    // STX
    0x86 => STX(zero_page, ZeroPage),
    0x96 => STX(zero_page_y, ZeroPageY),
    0x8E => STX(absolute, Absolute),

    // STY
    0x84 => STY(zero_page, ZeroPage),
    0x94 => STY(zero_page_x, ZeroPageX),
    0x8C => STY(absolute, Absolute),

    // TAX
    0xAA => TAX(implied, Implied),

    // TAY
    0xA8 => TAY(implied, Implied),

    // TSX
    0xBA => TSX(implied, Implied),

    // TXA
    0x8A => TXA(implied, Implied),

    // TXS
    0x9A => TXS(implied, Implied),

    // TYA
    0x98 => TYA(implied, Implied),
}
