import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.SHA256.Compression.Layout
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Instructions

def part06 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109ac3 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109ac6 0xc2 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109ac9 0xda rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x109acb 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x109ad0 5 (.base 3 (.d8 36)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r32_effect_step 0x109ad3 5) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x109ad5 5 (.sib 4 none 0 (.d8 8)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109ad9 0x44 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x109adc 0xfb rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x109ade 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x109ae0 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109ae2 0x44 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (not_r32_effect_step 0x109ae5 0xd3 rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x109ae7 0xf3 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x109ae9 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109aeb 0xc3 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109aed 0xc3 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x109af0 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x109af2 0xc1 0x12835b01 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109af8 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109afa 0xc2 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109afd 0xda rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109aff 0xc3 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109b01 0xc3 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109b04 0xd3 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109b06 0x44 0xd5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x109b09 0x44 0xdd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109b0c 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x109b0f 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x109b12 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109b14 0xea rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x109b16 0xda rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109b18 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109b1b 0x44 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109b1e 0xc3 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x109b21 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109b23 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109b26 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109b29 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109b2b 0x44 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109b2e 0xc3 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109b31 0xcb rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x109b33 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x109b38 5 (.base 1 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r32_effect_step 0x109b3b 5) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x109b3d 5 (.sib 4 none 0 (.d8 12)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109b41 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x109b44 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x109b47 0xee rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x109b49 0xce rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109b4b 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (not_r32_effect_step 0x109b4e 0xd1 rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x109b50 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x109b52 0xce rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_legacy_effect_step 0x109b54 1 (.sib 3 (some 6) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x109b57 0xc1 0x243185be rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109b5d 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109b5f 0xc6 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109b62 0xd3 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109b64 0xc3 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109b67 0xf3 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109b69 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109b6b 0xc6 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109b6e 0xde rfl) (by x86_local)]

def part06Bytes : List UInt8 :=
  [0x44,0x89,0xca,0xc1,0xc2,0x7,0x31,0xda,0x48,0x8b,0x5c,0x24,0x18,0x8b,0x6b,0x24,0xf,0xcd,0x89,0x6c,0x24,0x8,0x44,0x89,0xcb,0x21,0xfb,0x1,0xe9,0x1,0xd9,0x44,0x89,0xcb,0xf7,0xd3,0x21,0xf3,0x1,0xd9,0x89,0xc3,0xc1,0xc3,0x1e,0x1,0xd1,0x81,0xc1,0x1,0x5b,0x83,0x12,0x89,0xc2,0xc1,0xc2,0x13,0x31,0xda,0x89,0xc3,0xc1,0xc3,0xa,0x31,0xd3,0x44,0x89,0xd5,0x44,0x21,0xdd,0x44,0x89,0xd2,0x44,0x31,0xda,0x21,0xc2,0x31,0xea,0x1,0xda,0x41,0x1,0xc8,0x44,0x89,0xc3,0xc1,0xc3,0x1a,0x1,0xca,0x44,0x89,0xc1,0xc1,0xc1,0x15,0x31,0xd9,0x44,0x89,0xc3,0xc1,0xc3,0x7,0x31,0xcb,0x48,0x8b,0x4c,0x24,0x18,0x8b,0x69,0x28,0xf,0xcd,0x89,0x6c,0x24,0xc,0x44,0x89,0xc1,0x44,0x21,0xc9,0x1,0xee,0x1,0xce,0x44,0x89,0xc1,0xf7,0xd1,0x21,0xf9,0x1,0xce,0x8d,0xc,0x33,0x81,0xc1,0xbe,0x85,0x31,0x24,0x89,0xd6,0xc1,0xc6,0x1e,0x89,0xd3,0xc1,0xc3,0x13,0x31,0xf3,0x89,0xd6,0xc1,0xc6,0xa,0x31,0xde]

set_option maxRecDepth 4096 in
theorem part06_bytes [Bindings] : part06.flatMap CheckedInstruction.bytes = part06Bytes  := by
  rfl

def part06Layout : List (BitVec 64 × Nat) :=
  [(0x109ac3, 3), (0x109ac6, 3), (0x109ac9, 2), (0x109acb, 5), (0x109ad0, 3), (0x109ad3, 2), (0x109ad5, 4), (0x109ad9, 3), (0x109adc, 2), (0x109ade, 2), (0x109ae0, 2), (0x109ae2, 3), (0x109ae5, 2), (0x109ae7, 2), (0x109ae9, 2), (0x109aeb, 2), (0x109aed, 3), (0x109af0, 2), (0x109af2, 6), (0x109af8, 2), (0x109afa, 3), (0x109afd, 2), (0x109aff, 2), (0x109b01, 3), (0x109b04, 2), (0x109b06, 3), (0x109b09, 3), (0x109b0c, 3), (0x109b0f, 3), (0x109b12, 2), (0x109b14, 2), (0x109b16, 2), (0x109b18, 3), (0x109b1b, 3), (0x109b1e, 3), (0x109b21, 2), (0x109b23, 3), (0x109b26, 3), (0x109b29, 2), (0x109b2b, 3), (0x109b2e, 3), (0x109b31, 2), (0x109b33, 5), (0x109b38, 3), (0x109b3b, 2), (0x109b3d, 4), (0x109b41, 3), (0x109b44, 3), (0x109b47, 2), (0x109b49, 2), (0x109b4b, 3), (0x109b4e, 2), (0x109b50, 2), (0x109b52, 2), (0x109b54, 3), (0x109b57, 6), (0x109b5d, 2), (0x109b5f, 3), (0x109b62, 2), (0x109b64, 3), (0x109b67, 2), (0x109b69, 2), (0x109b6b, 3), (0x109b6e, 2)]

theorem part06_layout [Bindings] : InstructionTrace.layout part06 = part06Layout := by
  rfl

theorem part06_ordered [Bindings] : InstructionTrace.ordered 0x109ac3 part06 = true := by
  rw [InstructionTrace.ordered_eq_layout, part06_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part06_source : Hkdf.Spec.Program.Extracted.textBytes.toListFrom 0x9ac3 173 = part06Bytes := by
  rfl

end Hkdf.Proofs.Common.SHA256.Compression.Decoded
