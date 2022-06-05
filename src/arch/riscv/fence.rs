use super::Register;

bitflags::bitflags! {
    pub struct FenceType : u8 {
        const NONE   = 0b0000;
        const WRITES = 0b0001;
        const READS  = 0b0010;
        const OUTPUT = 0b0100;
        const INPUT  = 0b1000;
    }
}

#[derive(Debug)]
pub enum Fence {
    General {
        succ: FenceType,
        pred: FenceType,
    },
    TSO,
    PAUSE,
    I(Register, Register, i32),
    Unknown {
        rd: Register,
        rs1: Register,
        funct3: u8,
        succ: FenceType,
        pred: FenceType,
        fm: u8,
    },
}

impl Fence {
    pub(crate) fn decode(inst: u32) -> Self {
        let rd = Register::from(((inst >> 7) & 0b11111) as u8);
        let rs1 = Register::from(((inst >> 15) & 0b11111) as u8);
        let funct3 = ((inst >> 12) & 0b111) as u8;
        let succ = FenceType::from_bits_truncate(((inst >> 20) & 0b1111) as u8);
        let pred = FenceType::from_bits_truncate(((inst >> 24) & 0b1111) as u8);
        let fm = ((inst >> 28) & 0b1111) as u8;
        let imm = (inst as i32) >> 20;

        match (rd, funct3, rs1, succ, pred, fm) {
            (
                Register::X0,
                0b000,
                Register::X0,
                FenceType::READS | FenceType::WRITES,
                FenceType::READS | FenceType::WRITES,
                0b1000,
            ) => Self::TSO,
            (Register::X0, 0b000, Register::X0, FenceType::NONE, FenceType::WRITES, 0b0000) => {
                Self::PAUSE
            }
            (_, 0b000, _, _, _, 0b000) => Self::General { succ, pred },
            (_, 0b001, _, _, _, _) => Self::I(rd, rs1, imm),
            (_, _, _, _, _, _) => Self::Unknown {
                rd,
                rs1,
                funct3,
                succ,
                pred,
                fm,
            },
        }
    }
}
