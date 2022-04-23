use std::{
    fs::File,
    io::{BufRead, BufReader},
    str::FromStr,
};

use rand::Rng;
use sdl2::{
    event::Event,
    keyboard::Keycode,
    pixels::{Color, PixelFormatEnum},
    EventPump,
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
const FLAG_NEGATIVE: u8 = 0b1000_0000;
const FLAG_OVERFLOW: u8 = 0b0100_0000;
const FLAG_DECIMAL: u8 = 0b0000_1000;
const FLAG_INTERRUPT_DISABLE: u8 = 0b0000_0100;
const FLAG_ZERO: u8 = 0b0000_0010;
const FLAG_CARRY: u8 = 0b0000_0001;

pub struct CPU {
    pub program_counter: u16,
    pub stack_pointer: u16, // Should technically be 1 byte, but this is just easier
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
    Relative,
    Implied,
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
            "indirect" => AddressingMode::Indirect,
            "(indirect,X)" => AddressingMode::Indirect_X,
            "(indirect),Y" => AddressingMode::Indirect_Y,
            "accumulator" => AddressingMode::Accumulator,
            "relative" => AddressingMode::Relative,
            "implied" => AddressingMode::Implied,
            value => panic!("Invalid addressing mode: {value}"),
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
            stack_pointer: 0x01FF,
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

    fn mem_read_u16(&self, pos: u16) -> u16 {
        // Little endian fun
        let lo = self.mem_read(pos) as u16;
        let hi = self.mem_read(pos + 1) as u16;
        (hi << 8) | lo
    }

    fn mem_write(&mut self, addr: u16, data: u8) {
        self.memory[addr as usize] = data;
    }

    fn mem_write_u16(&mut self, pos: u16, data: u16) {
        // Little endian fun
        let hi = (data >> 8) as u8;
        let lo = (data & 0xff) as u8;
        self.mem_write(pos, lo);
        self.mem_write(pos + 1, hi);
    }

    // fn _get_stack_address(&self) -> u16 {
    //     (self.stack_pointer as u16) << 8 | STACK_HIGH_BYTE as u16
    // }

    fn push_stack(&mut self, data: u8) {
        dbg!(self.stack_pointer);
        if self.stack_pointer < 0x0100 {
            panic!("stack overflow!");
        }
        self.mem_write(self.stack_pointer, data);
        self.stack_pointer -= 1;
    }

    fn push_stack_u16(&mut self, data: u16) {
        self.push_stack((data >> 8) as u8);
        self.push_stack((data & 0xff) as u8);
    }

    fn pop_stack(&mut self) -> u8 {
        self.stack_pointer += 1;
        self.mem_read(self.stack_pointer)
    }

    fn pop_stack_u16(&mut self) -> u16 {
        (self.pop_stack() as u16 | (self.pop_stack() as u16) << 8) as u16
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
        // println!("Beginning of program space...");
        // println!("{:#04x?}", &self.memory[0x8000..0x8010]);
        self.run()
    }

    fn get_operand_address(&self, mode: &AddressingMode) -> u16 {
        match mode {
            AddressingMode::Immediate | AddressingMode::Relative => self.program_counter,

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
        if result == 0 {
            self.status |= FLAG_ZERO;
        } else {
            self.status &= !FLAG_ZERO;
        }

        // negative flag
        if result & 0x80 != 0 {
            self.status |= FLAG_NEGATIVE;
        } else {
            self.status &= !FLAG_NEGATIVE;
        }
    }

    fn update_carry_flag(&mut self, x: u8, y: u8, result: u8) {
        // Set the carry flag if either...
        // 8th bit of both x and y are 1 OR
        // 8th bit of one of x or y was 1 and result was 0 (meaning we got
        // a carry from bit 7)
        if x & y & 0x80 != 0 || ((x ^ y) & 0x80 != 0 && result & 0x80 == 0) {
            self.status |= FLAG_CARRY;
        } else {
            self.status &= !FLAG_CARRY;
        }
    }

    fn update_overflow_flag(&mut self, x: u8, y: u8, result: u8) {
        // if the sign of both inputs is different from the sign of the result
        // (http://www.righto.com/2012/12/the-6502-overflow-flag-explained.html)
        if (x ^ result) & (y ^ result) & 0x80 != 0 {
            self.status |= FLAG_OVERFLOW;
        } else {
            self.status &= !FLAG_OVERFLOW;
        }
    }

    fn _perform_add(&mut self, original_a: u8, to_add: u8) {
        let to_add_with_carry = to_add.wrapping_add(self.status & FLAG_CARRY);
        self.register_a = self.register_a.wrapping_add(to_add_with_carry);
        self.update_zero_and_negative_flags(self.register_a);
        self.update_carry_flag(original_a, to_add_with_carry, self.register_a);
        self.update_overflow_flag(original_a, to_add_with_carry, self.register_a);
    }

    fn _do_branch(&mut self, mode: &AddressingMode) {
        assert!(matches!(mode, AddressingMode::Relative));
        let value = self.mem_read(self.get_operand_address(mode)) as i8;
        self.program_counter = (self.program_counter as i16).wrapping_add(value as i16) as u16;
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

    fn bcc(&mut self, mode: &AddressingMode) {
        if self.status & FLAG_CARRY == 0 {
            self._do_branch(mode);
        }
    }

    fn bcs(&mut self, mode: &AddressingMode) {
        if self.status & FLAG_CARRY == FLAG_CARRY {
            self._do_branch(mode);
        }
    }

    fn beq(&mut self, mode: &AddressingMode) {
        if self.status & FLAG_ZERO == FLAG_ZERO {
            self._do_branch(mode);
        }
    }

    fn bit(&mut self, mode: &AddressingMode) {
        // What a weird instruction...
        // AND the accumlator with the passed value and use that value to set the zero bit
        // Unrelated to that set the negative and overflow flags based on the passed value
        let value = self.mem_read(self.get_operand_address(mode));
        let new_zero = self.register_a & value & FLAG_ZERO;
        let new_others = value & 0b1100_0000;
        self.status |= new_zero | new_others;
    }

    fn bmi(&mut self, mode: &AddressingMode) {
        // Tell the user if they're fat
        if self.status & FLAG_NEGATIVE == FLAG_NEGATIVE {
            self._do_branch(mode);
        }
    }

    fn bne(&mut self, mode: &AddressingMode) {
        if self.status & FLAG_ZERO == 0 {
            self._do_branch(mode);
        }
    }

    fn bpl(&mut self, mode: &AddressingMode) {
        if self.status & FLAG_NEGATIVE == 0 {
            self._do_branch(mode);
        }
    }

    fn brk(&mut self) {
        self.status |= 0b0001_0000;
    }

    fn bvc(&mut self, mode: &AddressingMode) {
        if self.status & FLAG_OVERFLOW == 0 {
            self._do_branch(mode);
        }
    }

    fn bvs(&mut self, mode: &AddressingMode) {
        if self.status & FLAG_OVERFLOW == FLAG_OVERFLOW {
            self._do_branch(mode);
        }
    }

    fn clc(&mut self) {
        self.status &= !FLAG_CARRY;
    }

    fn cld(&mut self) {
        self.status &= !FLAG_DECIMAL;
    }

    fn cli(&mut self) {
        self.status &= !FLAG_INTERRUPT_DISABLE;
    }

    fn clv(&mut self) {
        self.status &= !FLAG_OVERFLOW;
    }

    fn _cmp_register(&mut self, mode: &AddressingMode, register: u8) {
        let value = self.mem_read(self.get_operand_address(mode));
        let result = register.wrapping_sub(value) as i8;
        if result >= 0 {
            self.status &= FLAG_CARRY;
            if result == 0 {
                self.status &= FLAG_ZERO;
            }
        } else if result < 0 {
            self.status &= FLAG_NEGATIVE;
        } else {
            panic!("This shouldn't happen");
        }
    }

    fn cmp(&mut self, mode: &AddressingMode) {
        self._cmp_register(mode, self.register_a);
    }

    fn cpx(&mut self, mode: &AddressingMode) {
        self._cmp_register(mode, self.register_x);
    }

    fn cpy(&mut self, mode: &AddressingMode) {
        self._cmp_register(mode, self.register_y);
    }

    fn dec(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let new_value = self.mem_read(addr).wrapping_sub(1);
        self.mem_write(addr, new_value);
        self.update_zero_and_negative_flags(new_value);
    }

    fn dex(&mut self) {
        self.register_x = self.register_x.wrapping_sub(1);
        self.update_zero_and_negative_flags(self.register_x);
    }

    fn dey(&mut self) {
        self.register_y = self.register_y.wrapping_sub(1);
        self.update_zero_and_negative_flags(self.register_y);
    }

    fn eor(&mut self, mode: &AddressingMode) {
        let value = self.mem_read(self.get_operand_address(mode));
        self.register_a ^= value;
        self.update_zero_and_negative_flags(self.register_a);
    }

    fn inc(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let new_value = self.mem_read(addr).wrapping_add(1);
        self.mem_write(addr, new_value);
        self.update_zero_and_negative_flags(new_value);
    }

    fn inx(&mut self) {
        self.register_x = self.register_x.wrapping_add(1);
        self.update_zero_and_negative_flags(self.register_x);
    }

    fn iny(&mut self) {
        self.register_y = self.register_y.wrapping_add(1);
        self.update_zero_and_negative_flags(self.register_y);
    }

    fn jmp(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        self.program_counter = addr;
    }

    fn jsr(&mut self, mode: &AddressingMode) {
        // JSR only uses absolute addressing, so we know this totals 3 bytes
        // Since we need to save the address of the next instruction - 1, save our
        // current program counter + 2
        let addr = self.get_operand_address(mode);
        self.push_stack_u16(self.program_counter + 2);
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

    fn lsr(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);

        // Last bit in value goes into carry flag
        self.status = (self.status & !FLAG_CARRY) | (value & FLAG_CARRY);
        let new_value = value >> 1;
        match mode {
            AddressingMode::Accumulator => self.register_a = new_value,
            _ => self.mem_write(addr, new_value),
        }
        self.update_zero_and_negative_flags(new_value);
    }

    fn ora(&mut self, mode: &AddressingMode) {
        let value = self.mem_read(self.get_operand_address(mode));
        self.register_a |= value;
        self.update_zero_and_negative_flags(self.register_a);
    }

    fn pha(&mut self) {
        self.push_stack(self.register_a);
    }

    fn php(&mut self) {
        self.push_stack(self.status);
    }

    fn pla(&mut self) {
        self.register_a = self.pop_stack();
        self.update_zero_and_negative_flags(self.register_a);
    }

    fn plp(&mut self) {
        self.status = self.pop_stack();
    }

    fn rol(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let mut value = self.mem_read(addr);

        // Save off original carry
        let original_carry = self.status & FLAG_CARRY;
        // Move high bit into carry
        self.status = (self.status & !FLAG_CARRY) | (value >> 7);
        // Shift left
        value <<= 1;
        // Move original carry into low bit
        value |= original_carry;

        match mode {
            AddressingMode::Accumulator => self.register_a = value,
            _ => self.mem_write(addr, value),
        }

        self.update_zero_and_negative_flags(value);
    }

    fn ror(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let mut value = self.mem_read(addr);

        // Save off original carry
        let original_carry = self.status & FLAG_CARRY;
        // Move low bit into carry
        self.status = (self.status & !FLAG_CARRY) | value;
        // Shift right
        value >>= 1;
        // Move original carry into high bit
        // value |= original_carry;
        value |= original_carry << 7;

        match mode {
            AddressingMode::Accumulator => self.register_a = value,
            _ => self.mem_write(addr, value),
        }

        self.update_zero_and_negative_flags(value);
    }

    fn rts(&mut self) {
        self.program_counter = self.pop_stack_u16();
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

    fn tay(&mut self) {
        self.register_y = self.register_a;
        self.update_zero_and_negative_flags(self.register_y);
    }

    fn tsx(&mut self) {
        self.register_x = (self.stack_pointer & 0xFF) as u8; //because my stack pointer hack
        self.update_zero_and_negative_flags(self.register_x);
    }

    fn txa(&mut self) {
        self.register_a = self.register_x;
        self.update_zero_and_negative_flags(self.register_a);
    }

    fn txs(&mut self) {
        //because my stack pointer hack
        self.stack_pointer = (self.stack_pointer & 0xFF00) | self.register_x as u16;
    }

    fn tya(&mut self) {
        self.register_a = self.register_y;
        self.update_zero_and_negative_flags(self.register_a);
    }

    pub fn run(&mut self) {
        self.run_with_callback(|_| {});
    }

    pub fn run_with_callback<F>(&mut self, mut callback: F)
    where
        F: FnMut(&mut CPU),
    {
        loop {
            callback(self);
            println!("PC: {:#04x}", &self.program_counter);
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
                "BCC" => self.bcc(&opcode.mode),
                "BCS" => self.bcs(&opcode.mode),
                "BEG" => self.beq(&opcode.mode),
                "BIT" => self.bit(&opcode.mode),
                "BMI" => self.bmi(&opcode.mode),
                "BNE" => self.bne(&opcode.mode),
                "BPL" => self.bpl(&opcode.mode),
                "BRK" => {
                    self.brk();
                    return;
                }
                "BVC" => self.bvc(&opcode.mode),
                "BVS" => self.bvs(&opcode.mode),
                "CLC" => self.clc(),
                "CLD" => self.cld(),
                "CLI" => self.cli(),
                "CLV" => self.clv(),
                "CMP" => self.cmp(&opcode.mode),
                "CPX" => self.cpx(&opcode.mode),
                "CPY" => self.cpy(&opcode.mode),
                "DEC" => self.dec(&opcode.mode),
                "DEX" => self.dex(),
                "DEY" => self.dey(),
                "EOR" => self.eor(&opcode.mode),
                "INC" => self.inc(&opcode.mode),
                "INX" => self.inx(),
                "INY" => self.iny(),
                "JMP" => {
                    self.jmp(&opcode.mode);
                    continue; // Ensure we don't increment program counter
                }
                "JSR" => {
                    self.jsr(&opcode.mode);
                    continue;
                }
                "LDA" => self.lda(&opcode.mode),
                "LDX" => self.ldx(&opcode.mode),
                "LDY" => self.ldy(&opcode.mode),
                "LSR" => self.lsr(&opcode.mode),
                "NOP" => {}
                "ORA" => self.ora(&opcode.mode),
                "PHA" => self.pha(),
                "PHP" => self.php(),
                "PLA" => self.pla(),
                "PLP" => self.plp(),
                "ROL" => self.rol(&opcode.mode),
                "ROR" => self.ror(&opcode.mode),
                "RTI" => panic!("implement me"),
                "RTS" => self.rts(),
                "SBC" => self.sbc(&opcode.mode),
                "SEC" => self.sec(),
                "SED" => panic!("implement me"),
                "SEI" => panic!("implement me"),
                "STA" => self.sta(&opcode.mode),
                "STX" => self.stx(&opcode.mode),
                "STY" => self.sty(&opcode.mode),
                "TAX" => self.tax(),
                "TAY" => self.tay(),
                "TSX" => self.tsx(),
                "TXA" => self.txa(),
                "TXS" => self.txs(),
                "TYA" => self.tya(),
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

fn handle_user_input(cpu: &mut CPU, event_pump: &mut EventPump) {
    for event in event_pump.poll_iter() {
        match event {
            Event::Quit { .. }
            | Event::KeyDown {
                keycode: Some(Keycode::Escape),
                ..
            } => std::process::exit(0),
            Event::KeyDown {
                keycode: Some(Keycode::W),
                ..
            } => cpu.mem_write(0xff, 0x77),

            Event::KeyDown {
                keycode: Some(Keycode::S),
                ..
            } => cpu.mem_write(0xff, 0x73),

            Event::KeyDown {
                keycode: Some(Keycode::A),
                ..
            } => cpu.mem_write(0xff, 0x61),

            Event::KeyDown {
                keycode: Some(Keycode::D),
                ..
            } => cpu.mem_write(0xff, 0x64),

            _ => { /* do nothing */ }
        }
    }
}

fn color(byte: u8) -> Color {
    match byte {
        0 => sdl2::pixels::Color::BLACK,
        1 => sdl2::pixels::Color::WHITE,
        2 | 9 => sdl2::pixels::Color::GREY,
        3 | 10 => sdl2::pixels::Color::RED,
        4 | 11 => sdl2::pixels::Color::GREEN,
        5 | 12 => sdl2::pixels::Color::BLUE,
        6 | 13 => sdl2::pixels::Color::MAGENTA,
        7 | 14 => sdl2::pixels::Color::YELLOW,
        _ => sdl2::pixels::Color::CYAN,
    }
}

fn read_screen_state(cpu: &CPU, frame: &mut [u8; 32 * 3 * 32]) -> bool {
    let mut frame_idx = 0;
    let mut update = false;
    for i in 0x0200..0x600 {
        let color_idx = cpu.mem_read(i as u16);
        let (b1, b2, b3) = color(color_idx).rgb();
        if frame[frame_idx] != b1 || frame[frame_idx + 1] != b2 || frame[frame_idx + 2] != b3 {
            frame[frame_idx] = b1;
            frame[frame_idx + 1] = b2;
            frame[frame_idx + 2] = b3;
            update = true;
        }
        frame_idx += 3;
    }
    update
}

fn main() {
    // init sdl2
    let sdl_context = sdl2::init().unwrap();
    let video_subsystem = sdl_context.video().unwrap();
    let window = video_subsystem
        .window("Snake game", (32.0 * 10.0) as u32, (32.0 * 10.0) as u32)
        .position_centered()
        .build()
        .unwrap();

    let mut canvas = window.into_canvas().present_vsync().build().unwrap();
    let mut event_pump = sdl_context.event_pump().unwrap();
    canvas.set_scale(10.0, 10.0).unwrap();

    let creator = canvas.texture_creator();
    let mut texture = creator
        .create_texture_target(PixelFormatEnum::RGB24, 32, 32)
        .unwrap();

    // Snake
    let game_code = vec![
        0x20, 0x06, 0x06, 0x20, 0x38, 0x06, 0x20, 0x0d, 0x06, 0x20, 0x2a, 0x06, 0x60, 0xa9, 0x02,
        0x85, 0x02, 0xa9, 0x04, 0x85, 0x03, 0xa9, 0x11, 0x85, 0x10, 0xa9, 0x10, 0x85, 0x12, 0xa9,
        0x0f, 0x85, 0x14, 0xa9, 0x04, 0x85, 0x11, 0x85, 0x13, 0x85, 0x15, 0x60, 0xa5, 0xfe, 0x85,
        0x00, 0xa5, 0xfe, 0x29, 0x03, 0x18, 0x69, 0x02, 0x85, 0x01, 0x60, 0x20, 0x4d, 0x06, 0x20,
        0x8d, 0x06, 0x20, 0xc3, 0x06, 0x20, 0x19, 0x07, 0x20, 0x20, 0x07, 0x20, 0x2d, 0x07, 0x4c,
        0x38, 0x06, 0xa5, 0xff, 0xc9, 0x77, 0xf0, 0x0d, 0xc9, 0x64, 0xf0, 0x14, 0xc9, 0x73, 0xf0,
        0x1b, 0xc9, 0x61, 0xf0, 0x22, 0x60, 0xa9, 0x04, 0x24, 0x02, 0xd0, 0x26, 0xa9, 0x01, 0x85,
        0x02, 0x60, 0xa9, 0x08, 0x24, 0x02, 0xd0, 0x1b, 0xa9, 0x02, 0x85, 0x02, 0x60, 0xa9, 0x01,
        0x24, 0x02, 0xd0, 0x10, 0xa9, 0x04, 0x85, 0x02, 0x60, 0xa9, 0x02, 0x24, 0x02, 0xd0, 0x05,
        0xa9, 0x08, 0x85, 0x02, 0x60, 0x60, 0x20, 0x94, 0x06, 0x20, 0xa8, 0x06, 0x60, 0xa5, 0x00,
        0xc5, 0x10, 0xd0, 0x0d, 0xa5, 0x01, 0xc5, 0x11, 0xd0, 0x07, 0xe6, 0x03, 0xe6, 0x03, 0x20,
        0x2a, 0x06, 0x60, 0xa2, 0x02, 0xb5, 0x10, 0xc5, 0x10, 0xd0, 0x06, 0xb5, 0x11, 0xc5, 0x11,
        0xf0, 0x09, 0xe8, 0xe8, 0xe4, 0x03, 0xf0, 0x06, 0x4c, 0xaa, 0x06, 0x4c, 0x35, 0x07, 0x60,
        0xa6, 0x03, 0xca, 0x8a, 0xb5, 0x10, 0x95, 0x12, 0xca, 0x10, 0xf9, 0xa5, 0x02, 0x4a, 0xb0,
        0x09, 0x4a, 0xb0, 0x19, 0x4a, 0xb0, 0x1f, 0x4a, 0xb0, 0x2f, 0xa5, 0x10, 0x38, 0xe9, 0x20,
        0x85, 0x10, 0x90, 0x01, 0x60, 0xc6, 0x11, 0xa9, 0x01, 0xc5, 0x11, 0xf0, 0x28, 0x60, 0xe6,
        0x10, 0xa9, 0x1f, 0x24, 0x10, 0xf0, 0x1f, 0x60, 0xa5, 0x10, 0x18, 0x69, 0x20, 0x85, 0x10,
        0xb0, 0x01, 0x60, 0xe6, 0x11, 0xa9, 0x06, 0xc5, 0x11, 0xf0, 0x0c, 0x60, 0xc6, 0x10, 0xa5,
        0x10, 0x29, 0x1f, 0xc9, 0x1f, 0xf0, 0x01, 0x60, 0x4c, 0x35, 0x07, 0xa0, 0x00, 0xa5, 0xfe,
        0x91, 0x00, 0x60, 0xa6, 0x03, 0xa9, 0x00, 0x81, 0x10, 0xa2, 0x00, 0xa9, 0x01, 0x81, 0x10,
        0x60, 0xa2, 0x00, 0xea, 0xea, 0xca, 0xd0, 0xfb, 0x60,
    ];

    // Load the game
    let mut cpu = CPU::new();
    cpu.load(game_code);
    cpu.reset();

    // run the game cycle
    let mut screen_state = [0; 32 * 3 * 32];
    let mut rng = rand::thread_rng();

    cpu.run_with_callback(move |cpu| {
        handle_user_input(cpu, &mut event_pump);
        cpu.mem_write(0xfe, rng.gen_range(1, 16));

        if read_screen_state(cpu, &mut screen_state) {
            texture.update(None, &screen_state, 32 * 3).unwrap();
            canvas.copy(&texture, None, None).unwrap();
            canvas.present();
        }
        ::std::thread::sleep(std::time::Duration::new(0, 70_000));
    });
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
    fn test_90_bcc_relative() {
        // LDA #$01
        // BCC End
        // LDA #$05
        // End:
        //   LDX #$10
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x01, 0x90, 0x02, 0xa9, 0x05, 0xa2, 0x10]);
        assert_eq!(cpu.register_x, 0x10);
        assert_eq!(cpu.register_a, 0x01);

        // Same thing but with carry set (SEC)
        cpu.load_and_run(vec![0x38, 0xa9, 0x01, 0x90, 0x02, 0xa9, 0x05, 0xa2, 0x10]);
        assert_eq!(cpu.register_x, 0x10);
        assert_eq!(cpu.register_a, 0x05);
    }

    #[test]
    fn test_00_brk() {
        // BRK
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0x00]);
        assert!(cpu.status & 0b0001_0000 == 0b0001_0000);
    }

    #[test]
    fn test_ce_dec_absolute() {
        // LDA #$0x09 (a9)
        // STA $0x0123 (8d)
        // DEC $0x0123 (ce)
        // LDA $0x0123 (ad)
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![
            0xa9, 0x09, 0x8d, 0x23, 0x01, 0xce, 0x23, 0x01, 0xad, 0x23, 0x01,
        ]);
        assert_eq!(cpu.register_a, 0x08);
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
    fn test_jsr_rts() {
        //   JSR init
        //   JSR loop
        //   JSR end
        // init:
        //   LDA #$03
        //   RTS
        // middle:
        //   LDX #$07
        //   RTS
        // end:
        //   BRK

        let mut cpu = CPU::new();
        cpu.load_and_run(vec![
            0x20, 0x09, 0x80, 0x20, 0x0c, 0x80, 0x20, 0x0f, 0x80, 0xa9, 0x03, 0x60, 0xa2, 0x07,
            0x60, 0x00,
        ]);
        assert_eq!(cpu.register_a, 0x03);
        assert_eq!(cpu.register_x, 0x07);
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
