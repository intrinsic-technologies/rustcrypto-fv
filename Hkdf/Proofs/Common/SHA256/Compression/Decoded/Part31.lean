import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.SHA256.Compression.Layout
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Instructions

def part31 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (add_r32_r32_effect_step 0x10adc6 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10adc8 0x41 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10adcb 0x41 0xc1 0xf (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10adcf 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10add1 0xea rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10add3 0xc2 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10add6 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10add9 0xde rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10addb 0xc6 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10adde 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10ade1 0x41 0xc1 0xe (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10ade5 0x41 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10ade8 0xde rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10adea 0xee 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10aded 0x44 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x10adf0 5 (.sib 4 none 0 (.d32 128)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10adf7 0xee rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10adf9 6 (.sib 4 none 0 (.d8 80)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10adfd 0xee rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10adff 0xee 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10ae02 0xd6 rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x10ae04 0x44 (by simp [RexNoWPrefix]) 4 (.sib 4 none 0 (.d8 104)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10ae09 0x41 0xf4 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10ae0c 0xca rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ae0e 0xc2 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10ae11 0xce rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ae13 0xc6 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10ae16 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10ae18 0xca rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ae1a 0xc2 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10ae1d 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ae1f 0x44 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10ae22 0x44 0xee (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10ae25 0xce rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10ae27 0x44 0xee (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10ae2a 0x45 0xe3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ae2d 0x41 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10ae30 0x41 0xc1 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10ae34 0x41 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10ae37 0xc6 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ae39 0xc6 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10ae3c 0x41 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_rex_effect_step 0x10ae3f 0x41 0xc3 0x766a0abb (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10ae46 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ae48 0xc2 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10ae4b 0x44 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10ae4e 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ae50 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10ae53 0x45 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10ae56 0xfe rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10ae58 0x44 0xf6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10ae5b 0xc6 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10ae5d 0x44 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10ae60 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ae62 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10ae65 0x41 0xc1 0xf (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10ae69 0x45 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10ae6c 0xda rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ae6e 0xc2 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10ae71 0x44 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ae74 0x45 0xe3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10ae77 0x41 0xc3 0x19 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10ae7b 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ae7e 0x45 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part31Bytes : List UInt8 :=
  [0x1,0xf1,0x41,0x89,0xe9,0x41,0xc1,0xc1,0xf,0x1,0xf0,0x89,0xea,0xc1,0xc2,0xd,0x44,0x31,0xca,0x89,0xde,0xc1,0xc6,0x19,0x41,0x89,0xd9,0x41,0xc1,0xc1,0xe,0x41,0x31,0xf1,0x89,0xde,0xc1,0xee,0x3,0x44,0x31,0xce,0x1,0xac,0x24,0x80,0x0,0x0,0x0,0x1,0xee,0x89,0x74,0x24,0x50,0x89,0xee,0xc1,0xee,0xa,0x31,0xd6,0x44,0x8b,0x64,0x24,0x68,0x41,0x1,0xf4,0x89,0xca,0xc1,0xc2,0x1a,0x89,0xce,0xc1,0xc6,0x15,0x31,0xd6,0x89,0xca,0xc1,0xc2,0x7,0x31,0xf2,0x44,0x89,0xc6,0x44,0x31,0xee,0x21,0xce,0x44,0x31,0xee,0x45,0x1,0xe3,0x41,0x89,0xc1,0x41,0xc1,0xc1,0x1e,0x41,0x1,0xf3,0x89,0xc6,0xc1,0xc6,0x13,0x41,0x1,0xd3,0x41,0x81,0xc3,0xbb,0xa,0x6a,0x76,0x89,0xc2,0xc1,0xc2,0xa,0x44,0x31,0xce,0x31,0xf2,0x41,0x89,0xf9,0x45,0x21,0xf1,0x89,0xfe,0x44,0x31,0xf6,0x21,0xc6,0x44,0x31,0xce,0x1,0xd6,0x41,0x89,0xd9,0x41,0xc1,0xc1,0xf,0x45,0x1,0xda,0x89,0xda,0xc1,0xc2,0xd,0x44,0x1,0xde,0x45,0x89,0xe3,0x41,0xc1,0xc3,0x19,0x44,0x31,0xca,0x45,0x89,0xe1]

set_option maxRecDepth 4096 in
theorem part31_bytes [Bindings] : part31.flatMap CheckedInstruction.bytes = part31Bytes  := by
  rfl

def part31Layout : List (BitVec 64 × Nat) :=
  [(0x10adc6, 2), (0x10adc8, 3), (0x10adcb, 4), (0x10adcf, 2), (0x10add1, 2), (0x10add3, 3), (0x10add6, 3), (0x10add9, 2), (0x10addb, 3), (0x10adde, 3), (0x10ade1, 4), (0x10ade5, 3), (0x10ade8, 2), (0x10adea, 3), (0x10aded, 3), (0x10adf0, 7), (0x10adf7, 2), (0x10adf9, 4), (0x10adfd, 2), (0x10adff, 3), (0x10ae02, 2), (0x10ae04, 5), (0x10ae09, 3), (0x10ae0c, 2), (0x10ae0e, 3), (0x10ae11, 2), (0x10ae13, 3), (0x10ae16, 2), (0x10ae18, 2), (0x10ae1a, 3), (0x10ae1d, 2), (0x10ae1f, 3), (0x10ae22, 3), (0x10ae25, 2), (0x10ae27, 3), (0x10ae2a, 3), (0x10ae2d, 3), (0x10ae30, 4), (0x10ae34, 3), (0x10ae37, 2), (0x10ae39, 3), (0x10ae3c, 3), (0x10ae3f, 7), (0x10ae46, 2), (0x10ae48, 3), (0x10ae4b, 3), (0x10ae4e, 2), (0x10ae50, 3), (0x10ae53, 3), (0x10ae56, 2), (0x10ae58, 3), (0x10ae5b, 2), (0x10ae5d, 3), (0x10ae60, 2), (0x10ae62, 3), (0x10ae65, 4), (0x10ae69, 3), (0x10ae6c, 2), (0x10ae6e, 3), (0x10ae71, 3), (0x10ae74, 3), (0x10ae77, 4), (0x10ae7b, 3), (0x10ae7e, 3)]

theorem part31_layout [Bindings] : InstructionTrace.layout part31 = part31Layout := by
  rfl

theorem part31_ordered [Bindings] : InstructionTrace.ordered 0x10adc6 part31 = true := by
  rw [InstructionTrace.ordered_eq_layout, part31_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part31_source : Hkdf.Spec.Program.Extracted.textBytes.toListFrom 0xadc6 187 = part31Bytes := by
  rfl

end Hkdf.Proofs.Common.SHA256.Compression.Decoded
