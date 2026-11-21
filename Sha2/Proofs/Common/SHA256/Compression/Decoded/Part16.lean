import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu
import Sha2.Proofs.Common.SHA256.Compression.Accumulator

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part16 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c1b1 0x44 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c1b4 0xc1 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c1b7 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c1b9 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10c1bc 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 112)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10c1c1 0xda rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c1c3 0x45 0xcc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c1c6 0x41 0xdc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10c1c9 0x45 0xfc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c1cc 0x41 0xd4 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c1cf 0x41 0xcc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10c1d2 0x4c (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8 120)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c1d7 0x41 0xc5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c1da 0x41 0xc4 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10c1dd 1 (.sib 4 none 0 (.d32 144)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c1e4 0xc1 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10c1e7 0 (.sib 4 none 0 (.d32 148)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c1ee 0xc0 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c1f1 0xc8 rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x10c1f3 0x44 (by simp [RexNoWPrefix]) 2 (.sib 4 none 0 (.d32 152)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x10c1fb 0x41 0xea 0x3 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c1ff 0x41 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c202 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c204 0xc1 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c207 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c209 0xc0 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c20c 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c20e 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c211 0xc1 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c214 0x44 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c217 0xc2 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c21a 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c21c 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10c21f 0xe9 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c222 0xd1 rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x10c224 6 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10c227 0xf1 rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10c229 1 (.sib 4 none 0 (.d8 56)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c22d 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10c22f 0xe9 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c232 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c234 0x44 0xd5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10c237 0xcd rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10c239 0x4d 0xea (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c23c 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c23f 0xc0 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c242 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c245 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c248 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c24a 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c24d 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c250 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c252 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c255 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10c258 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c25b 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10c25e 0xef rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c260 0x44 0xe2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c263 0xc2 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10c266 0xcf rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c268 0x44 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c26b 0xc1 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10c26e 0xf8 rfl) (by x86_local),
    CheckedInstruction.register (add_eax_imm32_effect_step 0x10c270 0x2de92c6f) (by x86_local)]

def part16Bytes : List UInt8 :=
  [0x44,0x89,0xf9,0xc1,0xc1,0xa,0x31,0xd1,0x44,0x89,0xca,0x48,0x8b,0x5c,0x24,0x70,0x21,0xda,0x45,0x89,0xcc,0x41,0x31,0xdc,0x45,0x21,0xfc,0x41,0x31,0xd4,0x41,0x1,0xcc,0x4c,0x8b,0x6c,0x24,0x78,0x41,0x1,0xc5,0x41,0x1,0xc4,0x8b,0x8c,0x24,0x90,0x0,0x0,0x0,0xc1,0xc1,0x19,0x8b,0x84,0x24,0x94,0x0,0x0,0x0,0xc1,0xc0,0xe,0x31,0xc8,0x44,0x8b,0x94,0x24,0x98,0x0,0x0,0x0,0x41,0xc1,0xea,0x3,0x41,0x31,0xc2,0x89,0xf1,0xc1,0xc1,0xf,0x89,0xf0,0xc1,0xc0,0xd,0x31,0xc8,0x44,0x89,0xc1,0xc1,0xc1,0x19,0x44,0x89,0xc2,0xc1,0xc2,0xe,0x31,0xca,0x44,0x89,0xc1,0xc1,0xe9,0x3,0x31,0xd1,0x1,0x34,0x24,0x1,0xf1,0x89,0x4c,0x24,0x38,0x89,0xf1,0xc1,0xe9,0xa,0x31,0xc1,0x44,0x1,0xd5,0x1,0xcd,0x4d,0x89,0xea,0x44,0x89,0xd0,0xc1,0xc0,0x1a,0x44,0x89,0xd1,0xc1,0xc1,0x15,0x31,0xc1,0x44,0x89,0xd0,0xc1,0xc0,0x7,0x31,0xc8,0x44,0x89,0xf1,0x44,0x31,0xd9,0x44,0x21,0xd1,0x44,0x31,0xd9,0x1,0xef,0x44,0x89,0xe2,0xc1,0xc2,0x1e,0x1,0xcf,0x44,0x89,0xe1,0xc1,0xc1,0x13,0x1,0xf8,0x5,0x6f,0x2c,0xe9,0x2d]

set_option maxRecDepth 4096 in
theorem part16_bytes [Bindings] : part16.flatMap CheckedInstruction.bytes = part16Bytes  := by
  rfl

def part16Layout : List (BitVec 64 × Nat) :=
  [(0x10c1b1, 3), (0x10c1b4, 3), (0x10c1b7, 2), (0x10c1b9, 3), (0x10c1bc, 5), (0x10c1c1, 2), (0x10c1c3, 3), (0x10c1c6, 3), (0x10c1c9, 3), (0x10c1cc, 3), (0x10c1cf, 3), (0x10c1d2, 5), (0x10c1d7, 3), (0x10c1da, 3), (0x10c1dd, 7), (0x10c1e4, 3), (0x10c1e7, 7), (0x10c1ee, 3), (0x10c1f1, 2), (0x10c1f3, 8), (0x10c1fb, 4), (0x10c1ff, 3), (0x10c202, 2), (0x10c204, 3), (0x10c207, 2), (0x10c209, 3), (0x10c20c, 2), (0x10c20e, 3), (0x10c211, 3), (0x10c214, 3), (0x10c217, 3), (0x10c21a, 2), (0x10c21c, 3), (0x10c21f, 3), (0x10c222, 2), (0x10c224, 3), (0x10c227, 2), (0x10c229, 4), (0x10c22d, 2), (0x10c22f, 3), (0x10c232, 2), (0x10c234, 3), (0x10c237, 2), (0x10c239, 3), (0x10c23c, 3), (0x10c23f, 3), (0x10c242, 3), (0x10c245, 3), (0x10c248, 2), (0x10c24a, 3), (0x10c24d, 3), (0x10c250, 2), (0x10c252, 3), (0x10c255, 3), (0x10c258, 3), (0x10c25b, 3), (0x10c25e, 2), (0x10c260, 3), (0x10c263, 3), (0x10c266, 2), (0x10c268, 3), (0x10c26b, 3), (0x10c26e, 2), (0x10c270, 5)]

theorem part16_layout [Bindings] : InstructionTrace.layout part16 = part16Layout := by
  rfl

theorem part16_ordered [Bindings] : InstructionTrace.ordered 0x10c1b1 part16 = true := by
  rw [InstructionTrace.ordered_eq_layout, part16_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part16_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xc1b1 196 = part16Bytes := by
  rfl

end Sha2.Proofs.Common.SHA256.Compression.Decoded
