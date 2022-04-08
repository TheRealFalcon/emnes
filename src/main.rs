use std::{
    fs::File,
    io::{BufRead, BufReader},
    str::FromStr,
};

// Status (left high order to right low order)
//  Negative flag
//  Overflow flag
//  ALWAYS 1
//  Break command
//  Decimal mode flag
//  Interrupt disable
//  Zero flag
//  Carry flag
pub struct CPU {
    pub program_counter: u16,
    pub stack_pointer: u8,
    pub register_a: u8,
    pub register_x: u8,
    pub register_y: u8,
    pub status: u8,
    memory: [u8; 0xFFFF],
    opcodes: Vec<OpCode>,
}

#[derive(Debug, Clone, Copy)]
#[allow(non_camel_case_types)]
pub enum AddressingMode {
    Immediate,
    ZeroPage,
    ZeroPage_X,
    ZeroPage_Y,
    Absolute,
    Absolute_X,
    Absolute_Y,
    Indirect_X,
    Indirect_Y,
    Indirect,
}

#[derive(Clone)]
struct OpCode {
    name: String,
    code: u8,
    bytes: u8,
    mode: AddressingMode,
}

impl FromStr for OpCode {
    type Err = &'static str;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.starts_with('#') {
            return Err("comment");
        }
        let mut parts = s.split('\t');
        let mode = match parts.next().unwrap() {
            "immediate" => AddressingMode::Immediate,
            "zeropage" => AddressingMode::ZeroPage,
            "zeropage,X" => AddressingMode::ZeroPage_X,
            "zeropage,Y" => AddressingMode::ZeroPage_Y,
            "absolute" => AddressingMode::Absolute,
            "absolute,X" => AddressingMode::Absolute_X,
            "absolute,Y" => AddressingMode::Absolute_Y,
            "(indirect,X)" => AddressingMode::Indirect_X,
            "(indirect),Y" => AddressingMode::Indirect_Y,
            _ => AddressingMode::Indirect,
        };
        let operation = parts.next().unwrap();
        let code = u8::from_str_radix(parts.next().unwrap(), 16).unwrap();
        let bytes: u8 = parts.next().unwrap().parse().unwrap();
        let _cycles = parts.next().unwrap();
        let name = operation
            .split_ascii_whitespace()
            .next()
            .unwrap()
            .to_owned();

        Ok(OpCode {
            name,
            code,
            bytes,
            mode,
        })
    }
}

fn get_opcodes() -> Vec<OpCode> {
    BufReader::new(File::open("src/instructions.csv").unwrap())
        .lines()
        .filter_map(|x| x.unwrap().parse().ok())
        .collect::<Vec<OpCode>>()
}

impl CPU {
    pub fn new() -> Self {
        let mut opcodes = get_opcodes();
        opcodes.sort_unstable_by_key(|op| op.code);
        CPU {
            program_counter: 0,
            stack_pointer: 0, // This is wrong
            register_a: 0,
            register_x: 0,
            register_y: 0,
            status: 0,
            memory: [0; 0xFFFF],
            opcodes,
        }
    }

    fn mem_read(&self, addr: u16) -> u8 {
        self.memory[addr as usize]
    }

    fn mem_write(&mut self, addr: u16, data: u8) {
        self.memory[addr as usize] = data;
    }

    fn mem_read_u16(&self, pos: u16) -> u16 {
        // Little endian fun
        let lo = self.mem_read(pos) as u16;
        let hi = self.mem_read(pos + 1) as u16;
        (hi << 8) | lo
    }

    fn mem_write_u16(&mut self, pos: u16, data: u16) {
        // Little endian fun
        let hi = (data >> 8) as u8;
        let lo = (data & 0xff) as u8;
        self.mem_write(pos, lo);
        self.mem_write(pos + 1, hi);
    }

    pub fn reset(&mut self) {
        self.register_a = 0;
        self.register_x = 0;
        self.status = 0;

        self.program_counter = self.mem_read_u16(0xFFFC);
    }

    pub fn load(&mut self, program: Vec<u8>) {
        self.memory[0x8000..(0x8000 + program.len())].copy_from_slice(&program[..]);
        self.mem_write_u16(0xFFFC, 0x8000);
    }

    pub fn load_and_run(&mut self, program: Vec<u8>) {
        self.load(program);
        self.reset();
        self.run()
    }

    fn get_operand_address(&self, mode: &AddressingMode) -> u16 {
        match mode {
            AddressingMode::Immediate => self.program_counter,

            AddressingMode::ZeroPage => self.mem_read(self.program_counter) as u16,

            AddressingMode::Absolute => self.mem_read_u16(self.program_counter),

            AddressingMode::ZeroPage_X => {
                let pos = self.mem_read(self.program_counter);
                pos.wrapping_add(self.register_x) as u16
            }
            AddressingMode::ZeroPage_Y => {
                let pos = self.mem_read(self.program_counter);

                pos.wrapping_add(self.register_y) as u16
            }

            AddressingMode::Absolute_X => {
                let base = self.mem_read_u16(self.program_counter);

                base.wrapping_add(self.register_x as u16)
            }
            AddressingMode::Absolute_Y => {
                let base = self.mem_read_u16(self.program_counter);

                base.wrapping_add(self.register_y as u16)
            }

            AddressingMode::Indirect_X => {
                let base = self.mem_read(self.program_counter);

                let ptr: u8 = (base as u8).wrapping_add(self.register_x);
                let lo = self.mem_read(ptr as u16);
                let hi = self.mem_read(ptr.wrapping_add(1) as u16);
                (hi as u16) << 8 | (lo as u16)
            }
            AddressingMode::Indirect_Y => {
                let base = self.mem_read(self.program_counter);

                let lo = self.mem_read(base as u16);
                let hi = self.mem_read((base as u8).wrapping_add(1) as u16);
                let deref_base = (hi as u16) << 8 | (lo as u16);

                deref_base.wrapping_add(self.register_y as u16)
            }

            AddressingMode::Indirect => {
                panic!("mode {:?} is not supported", mode);
            }
        }
    }

    fn lda(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);

        self.register_a = value;
        self.update_zero_and_negative_flags(self.register_a);
        // dbg!(self.register_a);
    }

    fn tax(&mut self) {
        self.register_x = self.register_a;
        self.update_zero_and_negative_flags(self.register_x);
        // dbg!(self.register_a);
        // dbg!(self.register_x);
    }

    fn brk(&mut self) {
        self.status |= 0b0001_0000;
    }

    fn inx(&mut self) {
        self.register_x = self.register_x.wrapping_add(1);
        self.update_zero_and_negative_flags(self.register_x);
    }

    fn update_zero_and_negative_flags(&mut self, result: u8) {
        if result == 0 {
            self.status |= 0b0000_0010;
        } else {
            self.status &= 0b1111_1101;
        }

        if result & 0b1000_0000 != 0 {
            self.status |= 0b1000_0000;
        } else {
            self.status &= 0b0111_1111;
        }
    }

    pub fn run(&mut self) {
        loop {
            // dbg!(&self.program_counter);
            let code = self.mem_read(self.program_counter);
            self.program_counter += 1;

            // Retrieve OpCode
            let opcode_index = self
                .opcodes
                .binary_search_by_key(&code, |op| op.code)
                .unwrap();
            let opcode = self.opcodes[opcode_index].clone();

            // dbg!(code);
            // dbg!(&opcode.name);

            match opcode.name.as_str() {
                "BRK" => {
                    self.brk();
                    return;
                }
                "INX" => self.inx(),
                "LDA" => self.lda(&opcode.mode),
                "TAX" => self.tax(),
                _ => panic!("at the disco"),
            }

            self.program_counter += (opcode.bytes - 1) as u16;
        }
    }
}

impl Default for CPU {
    fn default() -> Self {
        Self::new()
    }
}

fn main() {
    dbg!("hi");
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_0xa9_lda_immediate_load_data() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x05, 0x00]);
        assert_eq!(cpu.register_a, 0x05);
        assert!(cpu.status & 0b0000_0010 == 0b00);
        assert!(cpu.status & 0b1000_0000 == 0);
    }

    #[test]
    fn test_0xa9_lda_zero_flag() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x00, 0x00]);
        assert!(cpu.status & 0b0000_0010 == 0b10);
    }

    #[test]
    fn test_0xa9_lda_negative_flag() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0xff, 0x00]);
        assert!(cpu.status & 0b1000_0000 == 0b1000_0000);
    }

    #[test]
    fn test_00_brk_flag() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0x00]);
        assert!(cpu.status & 0b0001_0000 == 0b0001_0000);
    }

    #[test]
    fn test_0xaa_tax_move_a_to_x() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 10, 0xaa, 0x00]);

        assert_eq!(cpu.register_x, 10)
    }

    #[test]
    fn test_5_ops_working_together() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0xc0, 0xaa, 0xe8, 0x00]);

        assert_eq!(cpu.register_x, 0xc1)
    }

    #[test]
    fn test_inx_overflow() {
        let mut cpu = CPU::new();
        // cpu.register_x = 0xff;
        cpu.load_and_run(vec![0xa9, 0xff, 0xaa, 0xe8, 0xe8, 0x00]);

        assert_eq!(cpu.register_x, 1)
    }

    #[test]
    fn test_lda_from_memory() {
        let mut cpu = CPU::new();
        cpu.mem_write(0x10, 0x55);

        cpu.load_and_run(vec![0xa5, 0x10, 0x00]);

        assert_eq!(cpu.register_a, 0x55);
    }

    // Should test TAX status flags
}
