mod csr;
mod decode;
mod error;
mod fence;
mod inst;

pub use csr::*;
pub use decode::*;
pub use error::*;
pub use fence::*;
pub use inst::*;

pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Register {
    X0 = 0,
    X1,
    X2,
    X3,
    X4,
    X5,
    X6,
    X7,
    X8,
    X9,
    X10,
    X11,
    X12,
    X13,
    X14,
    X15,
    X16,
    X17,
    X18,
    X19,
    X20,
    X21,
    X22,
    X23,
    X24,
    X25,
    X26,
    X27,
    X28,
    X29,
    X30,
    X31,
}

impl From<u8> for Register {
    fn from(val: u8) -> Self {
        match val {
            0 | 32 => Self::X0,
            1 => Self::X1,
            2 => Self::X2,
            3 => Self::X3,
            4 => Self::X4,
            5 => Self::X5,
            6 => Self::X6,
            7 => Self::X7,
            8 => Self::X8,
            9 => Self::X9,
            10 => Self::X10,
            11 => Self::X11,
            12 => Self::X12,
            13 => Self::X13,
            14 => Self::X14,
            15 => Self::X15,
            16 => Self::X16,
            17 => Self::X17,
            18 => Self::X18,
            19 => Self::X19,
            20 => Self::X20,
            21 => Self::X21,
            22 => Self::X22,
            23 => Self::X23,
            24 => Self::X24,
            25 => Self::X25,
            26 => Self::X26,
            27 => Self::X27,
            28 => Self::X28,
            29 => Self::X29,
            30 => Self::X30,
            31 => Self::X31,
            _ => todo!(),
        }
    }
}

#[test]
fn test() {
    use crate::Decode;

    let file = std::fs::File::open("test").unwrap(); //&[0x13, 0x01, 0x01, 0xff, 0x23, 0x24, 0xa1, 0x00];

    let dec = Decoder::new(file);

    for (i, inst) in dec.into_iter().enumerate() {
        let i = i * 4;
        let i = i + 0x11d7c;
        println!("{i:#016x}: {inst:?}");
        //println!("{i:#016x}: {inst:}");
    }
}
