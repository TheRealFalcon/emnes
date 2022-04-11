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
    Accumulator,
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
            "accumulator" => AddressingMode::Accumulator,
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
            _ => {
                panic!("mode {:?} is not supported", mode);
            }
        }
    }

    fn update_zero_and_negative_flags(&mut self, result: u8) {
        // 0 flag
        if result == 0 {
            self.status |= 0b0000_0010;
        } else {
            self.status &= 0b1111_1101;
        }

        // negative flag
        if result & 0x80 != 0 {
            self.status |= 0b1000_0000;
        } else {
            self.status &= 0b0111_1111;
        }
    }

    fn update_carry_flag(&mut self, x: u8, y: u8, result: u8) {
        // Set the carry flag if either...
        // 8th bit of both x and y are 1 OR
        // 8th bit of one of x or y was 1 and result was 0 (meaning we got
        // a carry from bit 7)
        if x & y & 0x80 != 0 || ((x ^ y) & 0x80 != 0 && result & 0x80 == 0) {
            self.status |= 0b0000_0001;
        } else {
            self.status &= 0b1111_1110;
        }
    }

    fn update_overflow_flag(&mut self, x: u8, y: u8, result: u8) {
        // if the sign of both inputs is different from the sign of the result
        // (http://www.righto.com/2012/12/the-6502-overflow-flag-explained.html)
        if (x ^ result) & (y ^ result) & 0x80 != 0 {
            self.status |= 0b0100_0000;
        } else {
            self.status &= 0b1011_1111;
        }
    }

    fn _perform_add(&mut self, original_a: u8, to_add: u8) {
        let to_add_with_carry = to_add.wrapping_add(self.status & 0b0000_0001);
        self.register_a = self.register_a.wrapping_add(to_add_with_carry);
        self.update_zero_and_negative_flags(self.register_a);
        self.update_carry_flag(original_a, to_add_with_carry, self.register_a);
        self.update_overflow_flag(original_a, to_add_with_carry, self.register_a);
    }

    fn adc(&mut self, mode: &AddressingMode) {
        let to_add = self.mem_read(self.get_operand_address(mode));
        self._perform_add(self.register_a, to_add);
    }

    fn and(&mut self, mode: &AddressingMode) {
        let value = self.mem_read(self.get_operand_address(mode));

        self.register_a &= value;
        self.update_zero_and_negative_flags(self.register_a);
    }

    fn asl(&mut self, mode: &AddressingMode) {
        let original_value;
        let new_value;
        if matches!(mode, AddressingMode::Accumulator) {
            original_value = self.register_a;
            self.register_a <<= 1;
            new_value = self.register_a;
        } else {
            let address = self.get_operand_address(mode);
            original_value = self.mem_read(address);
            new_value = original_value << 1;
            self.mem_write(address, new_value);
        }
        self.update_zero_and_negative_flags(new_value);
        self.update_carry_flag(original_value, original_value, new_value);
    }

    fn brk(&mut self) {
        self.status |= 0b0001_0000;
    }

    fn inx(&mut self) {
        self.register_x = self.register_x.wrapping_add(1);
        self.update_zero_and_negative_flags(self.register_x);
    }

    fn jmp(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        self.program_counter = addr;
    }

    fn lda(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);

        self.register_a = value;
        self.update_zero_and_negative_flags(self.register_a);
    }

    fn ldx(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);

        self.register_x = value;
        self.update_zero_and_negative_flags(self.register_x);
    }

    fn ldy(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);

        self.register_y = value;
        self.update_zero_and_negative_flags(self.register_y);
    }

    fn sbc(&mut self, mode: &AddressingMode) {
        // "Come on" said Professor Perdikaris as I slept through the ones complement and
        // twos complement section of my digital logic class
        let original_a = self.register_a;
        let to_subtract = self.mem_read(self.get_operand_address(mode));
        self._perform_add(original_a, !to_subtract);
    }

    fn sec(&mut self) {
        self.status |= 0b0000_0001;
    }

    fn sta(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        self.mem_write(addr, self.register_a);
    }

    fn stx(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        self.mem_write(addr, self.register_x);
    }

    fn sty(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        self.mem_write(addr, self.register_y);
    }

    fn tax(&mut self) {
        self.register_x = self.register_a;
        self.update_zero_and_negative_flags(self.register_x);
    }

    pub fn run(&mut self) {
        loop {
            println!("{:#04x}", &self.program_counter);
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
            dbg!(&opcode.name);

            match opcode.name.as_str() {
                "ADC" => self.adc(&opcode.mode),
                "AND" => self.and(&opcode.mode),
                "ASL" => self.asl(&opcode.mode),
                "BRK" => {
                    self.brk();
                    return;
                }
                "INX" => self.inx(),
                "JMP" => {
                    self.jmp(&opcode.mode);
                    continue; // Ensure we don't increment program counter
                }
                "LDA" => self.lda(&opcode.mode),
                "LDX" => self.ldx(&opcode.mode),
                "LDY" => self.ldy(&opcode.mode),
                "NOP" => {}
                "SBC" => self.sbc(&opcode.mode),
                "SEC" => self.sec(),
                "STA" => self.sta(&opcode.mode),
                "STX" => self.stx(&opcode.mode),
                "STY" => self.sty(&opcode.mode),
                "TAX" => self.tax(),
                _ => panic!("Bad opcode: {}", opcode.name.as_str()),
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
    println!("hi");
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_69_adc_immediate() {
        // Use the values from the table in
        // http://www.righto.com/2012/12/the-6502-overflow-flag-explained.html
        // to ensure we're setting negative, carry and overflow flags correctly

        // 1s from left to right: Negative, overflow, carry
        let check_bits = 0b1100_0001;

        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x50, 0x69, 0x10]);
        assert_eq!(cpu.register_a, 0x60);
        assert_eq!(cpu.status & check_bits, 0);

        cpu.load_and_run(vec![0xa9, 0x50, 0x69, 0x50]);
        assert_eq!(cpu.register_a, 0xa0);
        assert_eq!(cpu.status & check_bits, 0b1100_0000);

        cpu.load_and_run(vec![0xa9, 0x50, 0x69, 0x90]);
        assert_eq!(cpu.register_a, 0xe0);
        assert_eq!(cpu.status & check_bits, 0b1000_0000);

        cpu.load_and_run(vec![0xa9, 0x50, 0x69, 0xd0]);
        assert_eq!(cpu.register_a, 0x20);
        assert_eq!(cpu.status & check_bits, 0b0000_0001);

        cpu.load_and_run(vec![0xa9, 0xd0, 0x69, 0x10]);
        assert_eq!(cpu.register_a, 0xe0);
        assert_eq!(cpu.status & check_bits, 0b1000_0000);

        cpu.load_and_run(vec![0xa9, 0xd0, 0x69, 0x50]);
        assert_eq!(cpu.register_a, 0x20);
        assert_eq!(cpu.status & check_bits, 0b0000_0001);

        cpu.load_and_run(vec![0xa9, 0xd0, 0x69, 0x90]);
        assert_eq!(cpu.register_a, 0x60);
        assert_eq!(cpu.status & check_bits, 0b0100_0001);

        cpu.load_and_run(vec![0xa9, 0xd0, 0x69, 0xd0]);
        assert_eq!(cpu.register_a, 0xa0);
        assert_eq!(cpu.status & check_bits, 0b1000_0001);

        // Test with carry
        // Result of first add should be 0x20 + carry, so next add should result in 0x22
        cpu.load_and_run(vec![0xa9, 0x50, 0x69, 0xd0, 0x69, 0x01]);
        assert_eq!(cpu.register_a, 0x22);
        assert_eq!(cpu.status & check_bits, 0);
    }

    #[test]
    fn test_a9_and_immediate() {
        // LDA #$03
        // AND #$06
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0b0000_0011, 0x29, 0b0000_0110]);
        assert_eq!(cpu.register_a, 0b0000_0010);
    }

    #[test]
    fn test_0a_asl_accumulator() {
        // LDA #$03
        // ASL
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0b0000_0011, 0x0a]);
        assert_eq!(cpu.register_a, 0b0000_0110);
    }

    #[test]
    fn test_06_asl_zero_page() {
        // LDA #$03
        // STA $02
        // ASL $02
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0b0000_0011, 0x85, 0x02, 0x06, 0x02]);
        let result = cpu.mem_read(0x02);
        assert_eq!(result, 0b0000_0110);
    }

    #[test]
    fn test_asl_carry_flag() {
        // LDA #$80
        // ASL
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0b1000_0000, 0x0a]);
        assert_eq!(cpu.register_a, 0);
        assert_eq!(cpu.status & 0b0000_0001, 0b0000_0001);
    }

    #[test]
    fn test_00_brk_flag() {
        // BRK
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0x00]);
        assert!(cpu.status & 0b0001_0000 == 0b0001_0000);
    }

    #[test]
    fn test_inx_overflow() {
        // LDA #$0xff
        // TAX
        // INX
        // INX
        // BRK
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0xff, 0xaa, 0xe8, 0xe8, 0x00]);

        assert_eq!(cpu.register_x, 1)
    }

    #[test]
    fn test_4c_jmp_absolute() {
        // PC starts at 8000, LDA is 2 bytes, JMP is 3 bytes, LDA is 2 bytes,
        // so jump to $8007 (in little endian)
        // LDA #$03
        // JMP $8007
        // LDA #$10  // Should get skipped
        // LDX #$05
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x03, 0x4c, 0x07, 0x80, 0xa9, 0x10, 0xa2, 0x05]);
        assert_eq!(cpu.register_a, 0x03);
        assert_eq!(cpu.register_x, 0x05);
    }

    #[test]
    fn test_a9_lda_immediate_load_data() {
        // LDA #$05
        // BRK
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x05, 0x00]);
        assert_eq!(cpu.register_a, 0x05);
        assert!(cpu.status & 0b0000_0010 == 0b00);
        assert!(cpu.status & 0b1000_0000 == 0);
    }

    #[test]
    fn test_a5_lda_zero_page() {
        // LXD #$55
        // STX $02
        // LDA $02
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa2, 0x55, 0x86, 0x02, 0xa5, 0x02]);

        assert_eq!(cpu.register_a, 0x55);
    }

    #[test]
    fn test_a9_lda_zero_flag() {
        // LDA #$00
        // BRK
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x00, 0x00]);
        assert!(cpu.status & 0b0000_0010 == 0b10);
    }

    #[test]
    fn test_a9_lda_negative_flag() {
        // LDA #$ff
        // BRK
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0xff, 0x00]);
        assert!(cpu.status & 0b1000_0000 == 0b1000_0000);
    }

    #[test]
    fn test_e9_sbc_immediate() {
        // Use table at http://www.righto.com/2012/12/the-6502-overflow-flag-explained.html
        // to test borrow bit and underflow

        // 1s from left to right: Negative, overflow, carry
        let check_bits = 0b1100_0001;

        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0x38, 0xa9, 0x50, 0xe9, 0xf0]);
        assert_eq!(cpu.register_a, 0x60);
        assert_eq!(cpu.status & check_bits, 0);

        cpu.load_and_run(vec![0x38, 0xa9, 0x50, 0xe9, 0xb0]);
        assert_eq!(cpu.register_a, 0xa0);
        assert_eq!(cpu.status & check_bits, 0b1100_0000);

        cpu.load_and_run(vec![0x38, 0xa9, 0x50, 0xe9, 0x70]);
        assert_eq!(cpu.register_a, 0xe0);
        assert_eq!(cpu.status & check_bits, 0b1000_0000);

        cpu.load_and_run(vec![0x38, 0xa9, 0x50, 0xe9, 0x30]);
        assert_eq!(cpu.register_a, 0x20);
        assert_eq!(cpu.status & check_bits, 0b0000_0001);

        cpu.load_and_run(vec![0x38, 0xa9, 0xd0, 0xe9, 0xf0]);
        assert_eq!(cpu.register_a, 0xe0);
        assert_eq!(cpu.status & check_bits, 0b1000_0000);

        cpu.load_and_run(vec![0x38, 0xa9, 0xd0, 0xe9, 0xb0]);
        assert_eq!(cpu.register_a, 0x20);
        assert_eq!(cpu.status & check_bits, 0b0000_0001);

        cpu.load_and_run(vec![0x38, 0xa9, 0xd0, 0xe9, 0x70]);
        assert_eq!(cpu.register_a, 0x60);
        assert_eq!(cpu.status & check_bits, 0b0100_0001);

        cpu.load_and_run(vec![0x38, 0xa9, 0xd0, 0xe9, 0x30]);
        assert_eq!(cpu.register_a, 0xa0);
        assert_eq!(cpu.status & check_bits, 0b1000_0001);
    }

    #[test]
    fn test_85_sta_zero_page() {
        // LDA #$03
        // STA $02
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x03, 0x85, 0x02]);
        let result = cpu.mem_read(0x02);
        assert_eq!(result, 0x03);
    }

    #[test]
    fn test_aa_tax_move_a_to_x() {
        // LDA #$10
        // TAX
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x10, 0xaa, 0x00]);

        assert_eq!(cpu.register_x, 0x10)
    }

    #[test]
    fn test_ops_working_together() {
        // LDA #$c0
        // TAX
        // INX
        // BRK
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0xc0, 0xaa, 0xe8, 0x00]);

        assert_eq!(cpu.register_x, 0xc1)
    }
}
