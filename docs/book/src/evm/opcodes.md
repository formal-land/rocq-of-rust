# Opcode Reference

This page provides a reference for all EVM opcodes being verified in rocq-of-rust.

## Reading Opcode Entries

Each opcode shows:
- **Stack effect**: [consumed] → [produced]
- **Gas cost**: Static or formula
- **Status**: ✓ Verified | ○ In Progress | - Planned

## Arithmetic Operations

### ADD (0x01)
Stack: [a, b] → [a + b]
Gas: 3 (VERYLOW)
Status: ✓ Verified

Adds two values modulo 2^256.

### MUL (0x02)
Stack: [a, b] → [a * b]
Gas: 5 (LOW)
Status: ✓ Verified

Multiplies two values modulo 2^256.

### SUB (0x03)
Stack: [a, b] → [a - b]
Gas: 3 (VERYLOW)
Status: ✓ Verified

Subtracts b from a, wrapping on underflow.

### DIV (0x04)
Stack: [a, b] → [a / b]
Gas: 5 (LOW)
Status: ✓ Verified

Integer division. Returns 0 if divisor is 0.

### SDIV (0x05)
Stack: [a, b] → [a /ₛ b]
Gas: 5 (LOW)
Status: ✓ Verified

Signed integer division.

### MOD (0x06)
Stack: [a, b] → [a mod b]
Gas: 5 (LOW)
Status: ✓ Verified

Modulo operation. Returns 0 if divisor is 0.

### SMOD (0x07)
Stack: [a, b] → [a modₛ b]
Gas: 5 (LOW)
Status: ✓ Verified

Signed modulo operation.

### ADDMOD (0x08)
Stack: [a, b, N] → [(a + b) mod N]
Gas: 8 (MID)
Status: ✓ Verified

Addition modulo N. Returns 0 if N is 0.

### MULMOD (0x09)
Stack: [a, b, N] → [(a * b) mod N]
Gas: 8 (MID)
Status: ✓ Verified

Multiplication modulo N. Returns 0 if N is 0.

### EXP (0x0A)
Stack: [a, b] → [a^b]
Gas: 10 + 50 * byte_size(b)
Status: ✓ Verified

Exponentiation modulo 2^256.

### SIGNEXTEND (0x0B)
Stack: [b, x] → [sign_extend(x, b)]
Gas: 5 (LOW)
Status: ✓ Verified

Sign-extends x from (b+1) bytes.

---

## Comparison & Bitwise

### LT (0x10)
Stack: [a, b] → [a < b ? 1 : 0]
Gas: 3 (VERYLOW)
Status: ✓ Verified

Less-than comparison (unsigned).

### GT (0x11)
Stack: [a, b] → [a > b ? 1 : 0]
Gas: 3 (VERYLOW)
Status: ✓ Verified

Greater-than comparison (unsigned).

### SLT (0x12)
Stack: [a, b] → [a <ₛ b ? 1 : 0]
Gas: 3 (VERYLOW)
Status: ✓ Verified

Signed less-than comparison.

### SGT (0x13)
Stack: [a, b] → [a >ₛ b ? 1 : 0]
Gas: 3 (VERYLOW)
Status: ✓ Verified

Signed greater-than comparison.

### EQ (0x14)
Stack: [a, b] → [a == b ? 1 : 0]
Gas: 3 (VERYLOW)
Status: ✓ Verified

Equality comparison.

### ISZERO (0x15)
Stack: [a] → [a == 0 ? 1 : 0]
Gas: 3 (VERYLOW)
Status: ✓ Verified

Check if value is zero.

### AND (0x16)
Stack: [a, b] → [a & b]
Gas: 3 (VERYLOW)
Status: ✓ Verified

Bitwise AND.

### OR (0x17)
Stack: [a, b] → [a | b]
Gas: 3 (VERYLOW)
Status: ✓ Verified

Bitwise OR.

### XOR (0x18)
Stack: [a, b] → [a ^ b]
Gas: 3 (VERYLOW)
Status: ✓ Verified

Bitwise XOR.

### NOT (0x19)
Stack: [a] → [~a]
Gas: 3 (VERYLOW)
Status: ✓ Verified

Bitwise NOT.

### BYTE (0x1A)
Stack: [i, x] → [byte_at(x, i)]
Gas: 3 (VERYLOW)
Status: ✓ Verified

Get byte i of x (0 is most significant).

### SHL (0x1B)
Stack: [shift, value] → [value << shift]
Gas: 3 (VERYLOW)
Status: ✓ Verified

Left shift.

### SHR (0x1C)
Stack: [shift, value] → [value >> shift]
Gas: 3 (VERYLOW)
Status: ✓ Verified

Logical right shift.

### SAR (0x1D)
Stack: [shift, value] → [value >>ₛ shift]
Gas: 3 (VERYLOW)
Status: ✓ Verified

Arithmetic right shift (sign-extending).

---

## Memory Operations

### MLOAD (0x51)
Stack: [offset] → [value]
Gas: 3 + memory_expansion
Status: ○ In Progress

Load 32 bytes from memory.

### MSTORE (0x52)
Stack: [offset, value] → []
Gas: 3 + memory_expansion
Status: ○ In Progress

Store 32 bytes to memory.

### MSTORE8 (0x53)
Stack: [offset, value] → []
Gas: 3 + memory_expansion
Status: ○ In Progress

Store single byte to memory.

### MSIZE (0x59)
Stack: [] → [size]
Gas: 2 (BASE)
Status: ○ In Progress

Get current memory size.

---

## Stack Operations

### POP (0x50)
Stack: [a] → []
Gas: 2 (BASE)
Status: ○ In Progress

Remove top stack item.

### PUSH1-PUSH32 (0x60-0x7F)
Stack: [] → [value]
Gas: 3 (VERYLOW)
Status: ○ In Progress

Push 1-32 byte value onto stack.

### DUP1-DUP16 (0x80-0x8F)
Stack: [a, ...] → [a, a, ...]
Gas: 3 (VERYLOW)
Status: ○ In Progress

Duplicate Nth stack item.

### SWAP1-SWAP16 (0x90-0x9F)
Stack: [a, ..., b] → [b, ..., a]
Gas: 3 (VERYLOW)
Status: ○ In Progress

Swap top with Nth item.

---

## Control Flow

### STOP (0x00)
Stack: [] → []
Gas: 0
Status: ○ In Progress

Halt execution.

### JUMP (0x56)
Stack: [dest] → []
Gas: 8 (MID)
Status: - Planned

Jump to destination.

### JUMPI (0x57)
Stack: [dest, cond] → []
Gas: 10 (HIGH)
Status: - Planned

Conditional jump.

### JUMPDEST (0x5B)
Stack: [] → []
Gas: 1
Status: - Planned

Mark valid jump destination.

### PC (0x58)
Stack: [] → [counter]
Gas: 2 (BASE)
Status: - Planned

Get program counter.

### GAS (0x5A)
Stack: [] → [gas]
Gas: 2 (BASE)
Status: - Planned

Get remaining gas.

---

## Contract Operations

### CALL (0xF1)
Stack: [gas, addr, value, argsOff, argsLen, retOff, retLen] → [success]
Gas: Complex formula
Status: - Planned

Call another contract.

### RETURN (0xF3)
Stack: [offset, length] → []
Gas: 0 + memory_expansion
Status: - Planned

Return from execution.

### REVERT (0xFD)
Stack: [offset, length] → []
Gas: 0 + memory_expansion
Status: - Planned

Revert state changes.

---

## Gas Constants

| Name | Value | Used By |
|------|-------|---------|
| ZERO | 0 | STOP |
| BASE | 2 | POP, PC, MSIZE |
| VERYLOW | 3 | ADD, SUB, LT, GT, etc. |
| LOW | 5 | MUL, DIV, MOD |
| MID | 8 | ADDMOD, MULMOD, JUMP |
| HIGH | 10 | JUMPI |

## Source Files

Verification code is located at:
```
RocqOfRust/revm/revm_interpreter/instructions/
├── arithmetic.v         # Translated Rust
├── bitwise.v
├── links/
│   ├── arithmetic.v     # Type linking
│   └── bitwise/         # Per-opcode links
├── simulate/
│   ├── arithmetic.v     # Simulation models
│   └── bitwise/
└── tests/
    ├── arithmetic.v     # Test cases
    └── bitwise.v
```
