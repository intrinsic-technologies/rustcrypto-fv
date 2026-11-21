import P256.Proofs.Program.Code
import P256.Proofs.SHA256.Compression.Layout
import P256.Proofs.Common.SHA256.Compression.Bswap32
import P256.Proofs.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Decoded

open P256.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

def part30 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1170e6 0x44 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1170e9 0xc2 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1170ec 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1170ee 0x44 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x1170f1 0xce rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1170f3 0x44 0xd7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1170f6 0xcf rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x1170f8 0x44 0xf7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1170fb 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x1170fd 0xd7 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1170ff 0x41 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x117102 0xc7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117104 0x44 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117107 0xc2 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11710a 0x44 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11710d 0xc0 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117110 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117112 0xea rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117114 0xc2 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117117 0xee rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117119 0xc6 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x11711c 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x11711e 0xea rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x117120 0xea 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117123 0xf2 rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_rex_effect_step 0x117125 0x44 (by simp [RexNoWPrefix]) 7 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117129 0x44 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x11712c 2 (.sib 4 none 0 (.d8 8)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117130 0x44 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x117133 0xea 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117136 0xc2 rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x117138 3 (.sib 4 none 0 (.d8 120)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x11713c 0xd3 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11713e 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117141 0xc0 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117144 0x44 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117147 0xc2 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x11714a 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11714c 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11714f 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117152 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117154 0x44 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117157 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x11715a 0x44 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x11715d 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117160 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117163 0x41 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117166 0xfa rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117168 0xc2 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x11716b 0x42 (by simp [RexNoWPrefix]) 6 (.sib 0 (some 9) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x11716f 0xc6 0x650a7354 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117175 0xf8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117177 0xc0 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x11717a 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x11717c 0xfa rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11717e 0xc2 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117181 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117183 0x45 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x117186 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117189 0x44 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x11718c 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x11718f 0xf8 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117191 0x44 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x117194 0xd0 rfl) (by x86_local)]

def part30Bytes : List UInt8 :=
  [0x44,0x89,0xf2,0xc1,0xc2,0xa,0x31,0xf2,0x44,0x89,0xd6,0x21,0xce,0x44,0x89,0xd7,0x31,0xcf,0x44,0x21,0xf7,0x31,0xf7,0x1,0xd7,0x41,0x1,0xc0,0x1,0xc7,0x44,0x89,0xfa,0xc1,0xc2,0xf,0x44,0x89,0xf8,0xc1,0xc0,0xd,0x31,0xd0,0x89,0xea,0xc1,0xc2,0x19,0x89,0xee,0xc1,0xc6,0xe,0x31,0xd6,0x89,0xea,0xc1,0xea,0x3,0x31,0xf2,0x44,0x1,0x3c,0x24,0x44,0x1,0xfa,0x89,0x54,0x24,0x8,0x44,0x89,0xfa,0xc1,0xea,0xa,0x31,0xc2,0x8b,0x5c,0x24,0x78,0x1,0xd3,0x44,0x89,0xc0,0xc1,0xc0,0x1a,0x44,0x89,0xc2,0xc1,0xc2,0x15,0x31,0xc2,0x44,0x89,0xc0,0xc1,0xc0,0x7,0x31,0xd0,0x44,0x89,0xea,0x44,0x31,0xda,0x44,0x21,0xc2,0x44,0x31,0xda,0x41,0x1,0xd9,0x41,0x1,0xd1,0x89,0xfa,0xc1,0xc2,0x1e,0x42,0x8d,0x34,0x8,0x81,0xc6,0x54,0x73,0xa,0x65,0x89,0xf8,0xc1,0xc0,0x13,0x31,0xd0,0x89,0xfa,0xc1,0xc2,0xa,0x31,0xc2,0x45,0x89,0xf1,0x45,0x21,0xd1,0x44,0x89,0xf0,0x44,0x31,0xd0,0x21,0xf8,0x44,0x31,0xc8,0x1,0xd0]

set_option maxRecDepth 4096 in
theorem part30_bytes [Bindings] : part30.flatMap CheckedInstruction.bytes = part30Bytes  := by
  rfl

def part30Layout : List (BitVec 64 × Nat) :=
  [(0x1170e6, 3), (0x1170e9, 3), (0x1170ec, 2), (0x1170ee, 3), (0x1170f1, 2), (0x1170f3, 3), (0x1170f6, 2), (0x1170f8, 3), (0x1170fb, 2), (0x1170fd, 2), (0x1170ff, 3), (0x117102, 2), (0x117104, 3), (0x117107, 3), (0x11710a, 3), (0x11710d, 3), (0x117110, 2), (0x117112, 2), (0x117114, 3), (0x117117, 2), (0x117119, 3), (0x11711c, 2), (0x11711e, 2), (0x117120, 3), (0x117123, 2), (0x117125, 4), (0x117129, 3), (0x11712c, 4), (0x117130, 3), (0x117133, 3), (0x117136, 2), (0x117138, 4), (0x11713c, 2), (0x11713e, 3), (0x117141, 3), (0x117144, 3), (0x117147, 3), (0x11714a, 2), (0x11714c, 3), (0x11714f, 3), (0x117152, 2), (0x117154, 3), (0x117157, 3), (0x11715a, 3), (0x11715d, 3), (0x117160, 3), (0x117163, 3), (0x117166, 2), (0x117168, 3), (0x11716b, 4), (0x11716f, 6), (0x117175, 2), (0x117177, 3), (0x11717a, 2), (0x11717c, 2), (0x11717e, 3), (0x117181, 2), (0x117183, 3), (0x117186, 3), (0x117189, 3), (0x11718c, 3), (0x11718f, 2), (0x117191, 3), (0x117194, 2)]

theorem part30_layout [Bindings] : InstructionTrace.layout part30 = part30Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part30_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x170e6 176 = part30Bytes := by
  rfl

end P256.Proofs.SHA256.Compression.Decoded
