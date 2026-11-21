import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part06 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b9e3 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b9e6 0xc2 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b9e9 0xda rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10b9eb 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10b9f0 5 (.base 3 (.d8 36)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r32_effect_step 0x10b9f3 5) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10b9f5 5 (.sib 4 none 0 (.d8 8)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b9f9 0x44 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10b9fc 0xfb rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b9fe 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10ba00 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ba02 0x44 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (not_r32_effect_step 0x10ba05 0xd3 rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10ba07 0xf3 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10ba09 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10ba0b 0xc3 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ba0d 0xc3 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10ba10 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10ba12 0xc1 0x12835b01 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10ba18 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ba1a 0xc2 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10ba1d 0xda rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10ba1f 0xc3 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ba21 0xc3 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10ba24 0xd3 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ba26 0x44 0xd5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10ba29 0x44 0xdd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ba2c 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10ba2f 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10ba32 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10ba34 0xea rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10ba36 0xda rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10ba38 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ba3b 0x44 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ba3e 0xc3 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10ba41 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ba43 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ba46 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10ba49 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ba4b 0x44 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ba4e 0xc3 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10ba51 0xcb rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10ba53 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10ba58 5 (.base 1 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r32_effect_step 0x10ba5b 5) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10ba5d 5 (.sib 4 none 0 (.d8 12)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ba61 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10ba64 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10ba67 0xee rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10ba69 0xce rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ba6b 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (not_r32_effect_step 0x10ba6e 0xd1 rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10ba70 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10ba72 0xce rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_legacy_effect_step 0x10ba74 1 (.sib 3 (some 6) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10ba77 0xc1 0x243185be rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10ba7d 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ba7f 0xc6 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10ba82 0xd3 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ba84 0xc3 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10ba87 0xf3 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10ba89 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ba8b 0xc6 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10ba8e 0xde rfl) (by x86_local)]

def part06Bytes : List UInt8 :=
  [0x44,0x89,0xca,0xc1,0xc2,0x7,0x31,0xda,0x48,0x8b,0x5c,0x24,0x18,0x8b,0x6b,0x24,0xf,0xcd,0x89,0x6c,0x24,0x8,0x44,0x89,0xcb,0x21,0xfb,0x1,0xe9,0x1,0xd9,0x44,0x89,0xcb,0xf7,0xd3,0x21,0xf3,0x1,0xd9,0x89,0xc3,0xc1,0xc3,0x1e,0x1,0xd1,0x81,0xc1,0x1,0x5b,0x83,0x12,0x89,0xc2,0xc1,0xc2,0x13,0x31,0xda,0x89,0xc3,0xc1,0xc3,0xa,0x31,0xd3,0x44,0x89,0xd5,0x44,0x21,0xdd,0x44,0x89,0xd2,0x44,0x31,0xda,0x21,0xc2,0x31,0xea,0x1,0xda,0x41,0x1,0xc8,0x44,0x89,0xc3,0xc1,0xc3,0x1a,0x1,0xca,0x44,0x89,0xc1,0xc1,0xc1,0x15,0x31,0xd9,0x44,0x89,0xc3,0xc1,0xc3,0x7,0x31,0xcb,0x48,0x8b,0x4c,0x24,0x18,0x8b,0x69,0x28,0xf,0xcd,0x89,0x6c,0x24,0xc,0x44,0x89,0xc1,0x44,0x21,0xc9,0x1,0xee,0x1,0xce,0x44,0x89,0xc1,0xf7,0xd1,0x21,0xf9,0x1,0xce,0x8d,0xc,0x33,0x81,0xc1,0xbe,0x85,0x31,0x24,0x89,0xd6,0xc1,0xc6,0x1e,0x89,0xd3,0xc1,0xc3,0x13,0x31,0xf3,0x89,0xd6,0xc1,0xc6,0xa,0x31,0xde]

set_option maxRecDepth 4096 in
theorem part06_bytes [Bindings] : part06.flatMap CheckedInstruction.bytes = part06Bytes  := by
  rfl

def part06Layout : List (BitVec 64 × Nat) :=
  [(0x10b9e3, 3), (0x10b9e6, 3), (0x10b9e9, 2), (0x10b9eb, 5), (0x10b9f0, 3), (0x10b9f3, 2), (0x10b9f5, 4), (0x10b9f9, 3), (0x10b9fc, 2), (0x10b9fe, 2), (0x10ba00, 2), (0x10ba02, 3), (0x10ba05, 2), (0x10ba07, 2), (0x10ba09, 2), (0x10ba0b, 2), (0x10ba0d, 3), (0x10ba10, 2), (0x10ba12, 6), (0x10ba18, 2), (0x10ba1a, 3), (0x10ba1d, 2), (0x10ba1f, 2), (0x10ba21, 3), (0x10ba24, 2), (0x10ba26, 3), (0x10ba29, 3), (0x10ba2c, 3), (0x10ba2f, 3), (0x10ba32, 2), (0x10ba34, 2), (0x10ba36, 2), (0x10ba38, 3), (0x10ba3b, 3), (0x10ba3e, 3), (0x10ba41, 2), (0x10ba43, 3), (0x10ba46, 3), (0x10ba49, 2), (0x10ba4b, 3), (0x10ba4e, 3), (0x10ba51, 2), (0x10ba53, 5), (0x10ba58, 3), (0x10ba5b, 2), (0x10ba5d, 4), (0x10ba61, 3), (0x10ba64, 3), (0x10ba67, 2), (0x10ba69, 2), (0x10ba6b, 3), (0x10ba6e, 2), (0x10ba70, 2), (0x10ba72, 2), (0x10ba74, 3), (0x10ba77, 6), (0x10ba7d, 2), (0x10ba7f, 3), (0x10ba82, 2), (0x10ba84, 3), (0x10ba87, 2), (0x10ba89, 2), (0x10ba8b, 3), (0x10ba8e, 2)]

theorem part06_layout [Bindings] : InstructionTrace.layout part06 = part06Layout := by
  rfl

theorem part06_ordered [Bindings] : InstructionTrace.ordered 0x10b9e3 part06 = true := by
  rw [InstructionTrace.ordered_eq_layout, part06_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part06_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xb9e3 173 = part06Bytes := by
  rfl

end Sha2.Proofs.Common.SHA256.Compression.Decoded
