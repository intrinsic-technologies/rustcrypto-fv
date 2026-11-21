import P256.Proofs.Program.Code
import P256.Proofs.SHA256.Compression.Layout
import P256.Proofs.Common.SHA256.Compression.Bswap32
import P256.Proofs.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Decoded

open P256.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

def part50 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117fd3 0x41 0xef (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117fd6 0xcb rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117fd8 0xc3 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117fdb 0xfb rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117fdd 0xcf rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117fdf 0xc7 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117fe2 0xdf rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117fe4 0x44 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117fe7 0xf3 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x117fe9 0xcb rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117feb 0xf3 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117fed 0x44 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x117ff0 0xd8 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x117ff2 0xc7 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x117ff4 0xc7 0xa4506ceb rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117ffa 0x44 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117ffd 0xc0 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x118000 0x44 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x118003 0xc3 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x118006 0xc3 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x118008 0x45 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x11800b 0x41 0xc6 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x11800f 0x41 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x118012 0x44 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x118015 0x44 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x118018 0x44 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x11801b 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x11801e 0x44 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x118021 0xd8 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x118023 0x44 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x118026 0xfa rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x118028 0xf8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11802a 0x44 0xe5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11802d 0x44 0xe7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x118030 0xc7 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x118033 0x44 0xe3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x118036 0xc3 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x118039 0xfb rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x11803b 0xed 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x11803e 0xdd rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x118040 0xd7 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x118042 0xc7 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x118045 0xd3 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x118047 0xc3 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x11804a 0xfb rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x11804c 0xd7 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11804e 0xc7 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x118051 0xdf rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x118053 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 64)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x118058 0xeb rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x11805a 0xf3 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x11805c 0xce rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x11805e 0x44 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x118061 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x118063 0x44 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x118066 0xf3 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x118068 0xdf rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x11806a 0xc7 0xbef9a3f7 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x118070 0xc6 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x118072 0xc6 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x118075 0xc3 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x118077 0xc3 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x11807a 0xf3 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x11807c 0xc5 rfl) (by x86_local)]

def part50Bytes : List UInt8 :=
  [0x41,0x1,0xef,0x89,0xcb,0xc1,0xc3,0x15,0x31,0xfb,0x89,0xcf,0xc1,0xc7,0x7,0x31,0xdf,0x44,0x89,0xc3,0x31,0xf3,0x21,0xcb,0x31,0xf3,0x44,0x1,0xf8,0x1,0xd8,0x1,0xc7,0x81,0xc7,0xeb,0x6c,0x50,0xa4,0x44,0x89,0xc8,0xc1,0xc0,0x1e,0x44,0x89,0xcb,0xc1,0xc3,0x13,0x31,0xc3,0x45,0x89,0xce,0x41,0xc1,0xc6,0xa,0x41,0x31,0xde,0x44,0x89,0xdb,0x44,0x21,0xd3,0x44,0x89,0xd8,0x44,0x31,0xd0,0x44,0x21,0xc8,0x31,0xd8,0x44,0x1,0xf0,0x1,0xfa,0x1,0xf8,0x44,0x89,0xe5,0x44,0x89,0xe7,0xc1,0xc7,0xf,0x44,0x89,0xe3,0xc1,0xc3,0xd,0x31,0xfb,0xc1,0xed,0xa,0x31,0xdd,0x89,0xd7,0xc1,0xc7,0x1a,0x89,0xd3,0xc1,0xc3,0x15,0x31,0xfb,0x89,0xd7,0xc1,0xc7,0x7,0x31,0xdf,0x48,0x8b,0x5c,0x24,0x40,0x1,0xeb,0x1,0xf3,0x89,0xce,0x44,0x31,0xc6,0x21,0xd6,0x44,0x31,0xc6,0x1,0xf3,0x1,0xdf,0x81,0xc7,0xf7,0xa3,0xf9,0xbe,0x89,0xc6,0xc1,0xc6,0x1e,0x89,0xc3,0xc1,0xc3,0x13,0x31,0xf3,0x89,0xc5]

set_option maxRecDepth 4096 in
theorem part50_bytes [Bindings] : part50.flatMap CheckedInstruction.bytes = part50Bytes  := by
  rfl

def part50Layout : List (BitVec 64 × Nat) :=
  [(0x117fd3, 3), (0x117fd6, 2), (0x117fd8, 3), (0x117fdb, 2), (0x117fdd, 2), (0x117fdf, 3), (0x117fe2, 2), (0x117fe4, 3), (0x117fe7, 2), (0x117fe9, 2), (0x117feb, 2), (0x117fed, 3), (0x117ff0, 2), (0x117ff2, 2), (0x117ff4, 6), (0x117ffa, 3), (0x117ffd, 3), (0x118000, 3), (0x118003, 3), (0x118006, 2), (0x118008, 3), (0x11800b, 4), (0x11800f, 3), (0x118012, 3), (0x118015, 3), (0x118018, 3), (0x11801b, 3), (0x11801e, 3), (0x118021, 2), (0x118023, 3), (0x118026, 2), (0x118028, 2), (0x11802a, 3), (0x11802d, 3), (0x118030, 3), (0x118033, 3), (0x118036, 3), (0x118039, 2), (0x11803b, 3), (0x11803e, 2), (0x118040, 2), (0x118042, 3), (0x118045, 2), (0x118047, 3), (0x11804a, 2), (0x11804c, 2), (0x11804e, 3), (0x118051, 2), (0x118053, 5), (0x118058, 2), (0x11805a, 2), (0x11805c, 2), (0x11805e, 3), (0x118061, 2), (0x118063, 3), (0x118066, 2), (0x118068, 2), (0x11806a, 6), (0x118070, 2), (0x118072, 3), (0x118075, 2), (0x118077, 3), (0x11807a, 2), (0x11807c, 2)]

theorem part50_layout [Bindings] : InstructionTrace.layout part50 = part50Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part50_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x17fd3 171 = part50Bytes := by
  rfl

end P256.Proofs.SHA256.Compression.Decoded
