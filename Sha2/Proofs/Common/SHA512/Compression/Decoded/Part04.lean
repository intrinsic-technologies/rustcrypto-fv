import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part03

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part04 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10df2f 0x48 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10df32 0x48 0xc2 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10df36 0x48 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10df39 0x48 0xc6 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10df3d 0x48 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10df40 0x48 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10df43 0x48 0xc2 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10df47 0x48 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (bswap_r64_effect_step 0x10df4a 13) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10df4d 0x4c (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8 112)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10df52 0x48 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10df55 0x48 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10df58 0x4d 0xe8 (by simp [RexWPrefix]) rfl) (by x86_local)
  ]

def part04Bytes : List UInt8 :=
  [0x48,0x89,0xca,0x48,0xc1,0xc2,0x32,0x48,0x89,0xce,0x48,0xc1,0xc6,0x2e,0x48,0x31,0xd6,0x48,0x89,0xca,0x48,0xc1,0xc2,0x17,0x48,0x31,0xf2,0x49,0xf,0xcd,0x4c,0x89,0x6c,0x24,0x70,0x48,0x89,0xce,0x48,0x21,0xde,0x4d,0x1,0xe8]

def part04Layout : List (BitVec 64 × Nat) :=
  [(0x10df2f, 3), (0x10df32, 4), (0x10df36, 3), (0x10df39, 4), (0x10df3d, 3),
   (0x10df40, 3), (0x10df43, 4), (0x10df47, 3), (0x10df4a, 3), (0x10df4d, 5),
   (0x10df52, 3), (0x10df55, 3), (0x10df58, 3)]

set_option maxRecDepth 4096 in
theorem part04_bytes [Bindings] : part04.flatMap CheckedInstruction.bytes = part04Bytes := by
  rfl

theorem part04_layout [Bindings] : InstructionTrace.layout part04 = part04Layout := by
  rfl

theorem part04_ordered [Bindings] : InstructionTrace.ordered 0x10df2f part04 = true := by
  rw [InstructionTrace.ordered_eq_layout, part04_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part04_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xdf2f 44 = part04Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
