import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part06

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part07 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e004 0x49 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e007 0x49 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e00a 0x48 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e00d 0x48 0xc2 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e011 0x48 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e014 0x48 0xc6 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e018 0x48 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e01b 0x48 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e01e 0x48 0xc2 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e022 0x48 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e025 0x48 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e028 0x4c 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e02b 0x48 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e02e 0x4c 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e031 0x48 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e034 0x48 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e037 0x48 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e03a 0x4c 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e03d 0x4d 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e040 0x4c 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e043 0x48 0xc2 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e047 0x4c 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e04a 0x48 0xc7 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e04e 0x48 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e051 0x4d 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e054 0x49 0xc2 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e058 0x49 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10e05b 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r64_effect_step 0x10e05f 14) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10e062 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e066 0x4c 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e069 0x4c 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10e06c 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 176)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _)
  ]

def part07Bytes : List UInt8 :=
  [0x49,0x1,0xf1,0x49,0x1,0xd1,0x48,0x89,0xda,0x48,0xc1,0xc2,0x24,0x48,0x89,0xde,0x48,0xc1,0xc6,0x1e,0x48,0x31,0xd6,0x48,0x89,0xda,0x48,0xc1,0xc2,0x19,0x48,0x31,0xf2,0x48,0x89,0xc7,0x4c,0x21,0xdf,0x48,0x89,0xc6,0x4c,0x31,0xde,0x48,0x21,0xde,0x48,0x31,0xfe,0x48,0x1,0xd6,0x4c,0x1,0xce,0x4d,0x1,0xf9,0x4c,0x89,0xca,0x48,0xc1,0xc2,0x32,0x4c,0x89,0xcf,0x48,0xc1,0xc7,0x2e,0x48,0x31,0xd7,0x4d,0x89,0xca,0x49,0xc1,0xc2,0x17,0x49,0x31,0xfa,0x4c,0x8b,0x34,0x24,0x49,0xf,0xce,0x4c,0x89,0x34,0x24,0x4c,0x89,0xcf,0x4c,0x21,0xc7,0x48,0x8b,0x94,0x24,0xb0,0x0,0x0,0x0]

def part07Layout : List (BitVec 64 × Nat) :=
  [(0x10e004, 3), (0x10e007, 3), (0x10e00a, 3), (0x10e00d, 4), (0x10e011, 3),
   (0x10e014, 4), (0x10e018, 3), (0x10e01b, 3), (0x10e01e, 4), (0x10e022, 3),
   (0x10e025, 3), (0x10e028, 3), (0x10e02b, 3), (0x10e02e, 3), (0x10e031, 3),
   (0x10e034, 3), (0x10e037, 3), (0x10e03a, 3), (0x10e03d, 3), (0x10e040, 3),
   (0x10e043, 4), (0x10e047, 3), (0x10e04a, 4), (0x10e04e, 3), (0x10e051, 3),
   (0x10e054, 4), (0x10e058, 3), (0x10e05b, 4), (0x10e05f, 3), (0x10e062, 4),
   (0x10e066, 3), (0x10e069, 3), (0x10e06c, 8)]

set_option maxRecDepth 4096 in
theorem part07_bytes [Bindings] : part07.flatMap CheckedInstruction.bytes = part07Bytes := by
  rfl

theorem part07_layout [Bindings] : InstructionTrace.layout part07 = part07Layout := by
  rfl

theorem part07_ordered [Bindings] : InstructionTrace.ordered 0x10e004 part07 = true := by
  rw [InstructionTrace.ordered_eq_layout, part07_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part07_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xe004 112 = part07Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
