import P256.Proofs.Program.Code
import P256.Proofs.SHA256.Compression.Layout
import P256.Proofs.Common.SHA256.Compression.Bswap32
import P256.Proofs.SHA256.Compression.MemoryAlu
import P256.Proofs.Common.SHA256.Compression.Accumulator

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Decoded

open P256.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

def part10 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116161 0xc6 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116164 0xfe rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116166 0x44 0xf7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x116169 0x44 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11616c 0x45 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x11616f 0x45 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x116172 0x45 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116175 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116178 0x41 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x11617b 0xcb rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x11617d 0x4c (by simp [RexWPrefix]) 4 (.sib 4 none 0 (.d8 56)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116182 0x44 0xe6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116185 0xc6 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116188 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11618b 0x44 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11618e 0xc1 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116191 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116193 0x44 0xe6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x116196 0xee 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116199 0xce rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x11619b 5 (.sib 4 none 0 (.d8 100)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x11619f 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1161a1 0xc1 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1161a4 0xef rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1161a6 0xc7 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1161a9 0xcf rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x1161ab 0xed 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1161ae 0xfd rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x1161b0 0x4c (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 80)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (add_r32_m32_rex_effect_step 0x1161b5 0x44 (by simp [RexNoWPrefix]) 2 (.sib 4 none 0 (.d8 8)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1161ba 0x41 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1161bd 0x41 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1161c0 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1161c2 0xc1 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1161c5 0xde rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1161c7 0xc6 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1161ca 0xce rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1161cc 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1161ce 0xc1 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1161d1 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1161d3 0x44 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1161d6 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x1161d8 0xde rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x1161da 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d32 128)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1161e2 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1161e4 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1161e7 0x44 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1161ea 0xc7 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x1161ed 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1161ef 0x44 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1161f2 0xc6 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x1161f5 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (add_eax_imm32_effect_step 0x1161f7 0xe49b69c1) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1161fc 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1161ff 0x4c 0xc5 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116202 0xc1 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116205 0xfe rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116207 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116209 0x44 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x11620c 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 88)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x116211 0x44 0xf6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116214 0x44 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116217 0x44 0xf7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x11621a 0xef rfl) (by x86_local)]

def part10Bytes : List UInt8 :=
  [0xc1,0xc6,0xa,0x31,0xfe,0x44,0x89,0xf7,0x44,0x21,0xcf,0x45,0x89,0xf0,0x45,0x31,0xc8,0x45,0x21,0xd8,0x41,0x31,0xf8,0x41,0x1,0xf0,0x1,0xcb,0x4c,0x8b,0x64,0x24,0x38,0x44,0x89,0xe6,0xc1,0xc6,0x19,0x41,0x1,0xc8,0x44,0x89,0xe1,0xc1,0xc1,0xe,0x31,0xf1,0x44,0x89,0xe6,0xc1,0xee,0x3,0x31,0xce,0x89,0x6c,0x24,0x64,0x89,0xe9,0xc1,0xc1,0xf,0x89,0xef,0xc1,0xc7,0xd,0x31,0xcf,0xc1,0xed,0xa,0x31,0xfd,0x4c,0x8b,0x54,0x24,0x50,0x44,0x3,0x54,0x24,0x8,0x41,0x1,0xf2,0x41,0x1,0xea,0x89,0xd9,0xc1,0xc1,0x1a,0x89,0xde,0xc1,0xc6,0x15,0x31,0xce,0x89,0xd9,0xc1,0xc1,0x7,0x31,0xf1,0x44,0x89,0xfe,0x31,0xd6,0x21,0xde,0x48,0x89,0x9c,0x24,0x80,0x0,0x0,0x0,0x31,0xd6,0x44,0x1,0xd0,0x44,0x89,0xc7,0xc1,0xc7,0x1e,0x1,0xf0,0x44,0x89,0xc6,0xc1,0xc6,0x13,0x1,0xc8,0x5,0xc1,0x69,0x9b,0xe4,0x44,0x89,0xc1,0x4c,0x89,0xc5,0xc1,0xc1,0xa,0x31,0xfe,0x31,0xf1,0x44,0x89,0xde,0x4c,0x89,0x74,0x24,0x58,0x44,0x21,0xf6,0x44,0x89,0xdf,0x44,0x31,0xf7,0x21,0xef]

set_option maxRecDepth 4096 in
theorem part10_bytes [Bindings] : part10.flatMap CheckedInstruction.bytes = part10Bytes  := by
  rfl

def part10Layout : List (BitVec 64 × Nat) :=
  [(0x116161, 3), (0x116164, 2), (0x116166, 3), (0x116169, 3), (0x11616c, 3), (0x11616f, 3), (0x116172, 3), (0x116175, 3), (0x116178, 3), (0x11617b, 2), (0x11617d, 5), (0x116182, 3), (0x116185, 3), (0x116188, 3), (0x11618b, 3), (0x11618e, 3), (0x116191, 2), (0x116193, 3), (0x116196, 3), (0x116199, 2), (0x11619b, 4), (0x11619f, 2), (0x1161a1, 3), (0x1161a4, 2), (0x1161a6, 3), (0x1161a9, 2), (0x1161ab, 3), (0x1161ae, 2), (0x1161b0, 5), (0x1161b5, 5), (0x1161ba, 3), (0x1161bd, 3), (0x1161c0, 2), (0x1161c2, 3), (0x1161c5, 2), (0x1161c7, 3), (0x1161ca, 2), (0x1161cc, 2), (0x1161ce, 3), (0x1161d1, 2), (0x1161d3, 3), (0x1161d6, 2), (0x1161d8, 2), (0x1161da, 8), (0x1161e2, 2), (0x1161e4, 3), (0x1161e7, 3), (0x1161ea, 3), (0x1161ed, 2), (0x1161ef, 3), (0x1161f2, 3), (0x1161f5, 2), (0x1161f7, 5), (0x1161fc, 3), (0x1161ff, 3), (0x116202, 3), (0x116205, 2), (0x116207, 2), (0x116209, 3), (0x11620c, 5), (0x116211, 3), (0x116214, 3), (0x116217, 3), (0x11621a, 2)]

theorem part10_layout [Bindings] : InstructionTrace.layout part10 = part10Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part10_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x16161 187 = part10Bytes := by
  rfl

end P256.Proofs.SHA256.Compression.Decoded
