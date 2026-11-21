import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.SHA256.Compression.Layout
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.SHA256.Compression.MemoryAlu
import Hkdf.Proofs.Common.SHA256.Compression.Accumulator

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Instructions

def part16 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a291 0x44 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a294 0xc1 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a297 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a299 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10a29c 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 112)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10a2a1 0xda rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a2a3 0x45 0xcc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a2a6 0x41 0xdc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10a2a9 0x45 0xfc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a2ac 0x41 0xd4 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a2af 0x41 0xcc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10a2b2 0x4c (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8 120)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a2b7 0x41 0xc5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a2ba 0x41 0xc4 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10a2bd 1 (.sib 4 none 0 (.d32 144)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a2c4 0xc1 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10a2c7 0 (.sib 4 none 0 (.d32 148)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a2ce 0xc0 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a2d1 0xc8 rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x10a2d3 0x44 (by simp [RexNoWPrefix]) 2 (.sib 4 none 0 (.d32 152)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x10a2db 0x41 0xea 0x3 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a2df 0x41 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10a2e2 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a2e4 0xc1 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10a2e7 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a2e9 0xc0 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a2ec 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a2ee 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a2f1 0xc1 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a2f4 0x44 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a2f7 0xc2 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a2fa 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a2fc 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10a2ff 0xe9 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a302 0xd1 rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x10a304 6 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10a307 0xf1 rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10a309 1 (.sib 4 none 0 (.d8 56)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10a30d 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10a30f 0xe9 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a312 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a314 0x44 0xd5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10a317 0xcd rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10a319 0x4d 0xea (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a31c 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a31f 0xc0 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a322 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a325 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a328 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a32a 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a32d 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a330 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a332 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a335 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10a338 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a33b 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10a33e 0xef rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a340 0x44 0xe2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a343 0xc2 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10a346 0xcf rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a348 0x44 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a34b 0xc1 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10a34e 0xf8 rfl) (by x86_local),
    CheckedInstruction.register (add_eax_imm32_effect_step 0x10a350 0x2de92c6f) (by x86_local)]

def part16Bytes : List UInt8 :=
  [0x44,0x89,0xf9,0xc1,0xc1,0xa,0x31,0xd1,0x44,0x89,0xca,0x48,0x8b,0x5c,0x24,0x70,0x21,0xda,0x45,0x89,0xcc,0x41,0x31,0xdc,0x45,0x21,0xfc,0x41,0x31,0xd4,0x41,0x1,0xcc,0x4c,0x8b,0x6c,0x24,0x78,0x41,0x1,0xc5,0x41,0x1,0xc4,0x8b,0x8c,0x24,0x90,0x0,0x0,0x0,0xc1,0xc1,0x19,0x8b,0x84,0x24,0x94,0x0,0x0,0x0,0xc1,0xc0,0xe,0x31,0xc8,0x44,0x8b,0x94,0x24,0x98,0x0,0x0,0x0,0x41,0xc1,0xea,0x3,0x41,0x31,0xc2,0x89,0xf1,0xc1,0xc1,0xf,0x89,0xf0,0xc1,0xc0,0xd,0x31,0xc8,0x44,0x89,0xc1,0xc1,0xc1,0x19,0x44,0x89,0xc2,0xc1,0xc2,0xe,0x31,0xca,0x44,0x89,0xc1,0xc1,0xe9,0x3,0x31,0xd1,0x1,0x34,0x24,0x1,0xf1,0x89,0x4c,0x24,0x38,0x89,0xf1,0xc1,0xe9,0xa,0x31,0xc1,0x44,0x1,0xd5,0x1,0xcd,0x4d,0x89,0xea,0x44,0x89,0xd0,0xc1,0xc0,0x1a,0x44,0x89,0xd1,0xc1,0xc1,0x15,0x31,0xc1,0x44,0x89,0xd0,0xc1,0xc0,0x7,0x31,0xc8,0x44,0x89,0xf1,0x44,0x31,0xd9,0x44,0x21,0xd1,0x44,0x31,0xd9,0x1,0xef,0x44,0x89,0xe2,0xc1,0xc2,0x1e,0x1,0xcf,0x44,0x89,0xe1,0xc1,0xc1,0x13,0x1,0xf8,0x5,0x6f,0x2c,0xe9,0x2d]

set_option maxRecDepth 4096 in
theorem part16_bytes [Bindings] : part16.flatMap CheckedInstruction.bytes = part16Bytes  := by
  rfl

def part16Layout : List (BitVec 64 × Nat) :=
  [(0x10a291, 3), (0x10a294, 3), (0x10a297, 2), (0x10a299, 3), (0x10a29c, 5), (0x10a2a1, 2), (0x10a2a3, 3), (0x10a2a6, 3), (0x10a2a9, 3), (0x10a2ac, 3), (0x10a2af, 3), (0x10a2b2, 5), (0x10a2b7, 3), (0x10a2ba, 3), (0x10a2bd, 7), (0x10a2c4, 3), (0x10a2c7, 7), (0x10a2ce, 3), (0x10a2d1, 2), (0x10a2d3, 8), (0x10a2db, 4), (0x10a2df, 3), (0x10a2e2, 2), (0x10a2e4, 3), (0x10a2e7, 2), (0x10a2e9, 3), (0x10a2ec, 2), (0x10a2ee, 3), (0x10a2f1, 3), (0x10a2f4, 3), (0x10a2f7, 3), (0x10a2fa, 2), (0x10a2fc, 3), (0x10a2ff, 3), (0x10a302, 2), (0x10a304, 3), (0x10a307, 2), (0x10a309, 4), (0x10a30d, 2), (0x10a30f, 3), (0x10a312, 2), (0x10a314, 3), (0x10a317, 2), (0x10a319, 3), (0x10a31c, 3), (0x10a31f, 3), (0x10a322, 3), (0x10a325, 3), (0x10a328, 2), (0x10a32a, 3), (0x10a32d, 3), (0x10a330, 2), (0x10a332, 3), (0x10a335, 3), (0x10a338, 3), (0x10a33b, 3), (0x10a33e, 2), (0x10a340, 3), (0x10a343, 3), (0x10a346, 2), (0x10a348, 3), (0x10a34b, 3), (0x10a34e, 2), (0x10a350, 5)]

theorem part16_layout [Bindings] : InstructionTrace.layout part16 = part16Layout := by
  rfl

theorem part16_ordered [Bindings] : InstructionTrace.ordered 0x10a291 part16 = true := by
  rw [InstructionTrace.ordered_eq_layout, part16_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part16_source : Hkdf.Spec.Program.Extracted.textBytes.toListFrom 0xa291 196 = part16Bytes := by
  rfl

end Hkdf.Proofs.Common.SHA256.Compression.Decoded
