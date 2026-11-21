import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part08

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part09 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e0f7 0x4c 0xe1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (add_r64_m64_effect_step 0x10e0fa 0x48 (by simp [RexWPrefix]) 1 (.rip 0xf1f1f) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e101 0x49 0xd2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e104 0x4d 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e107 0x4c 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e10a 0x49 0xd2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (not_r64_effect_step 0x10e10d 0x49 0xd2 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e110 0x4d 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e113 0x4d 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e116 0x49 0xc6 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e11a 0x4c 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e11d 0x4d 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e120 0x49 0xc2 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e124 0x48 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e127 0x4d 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e12a 0x49 0xc7 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e12e 0x4d 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e131 0x4d 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e134 0x49 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e137 0x49 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e13a 0x48 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e13d 0x48 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e140 0x4c 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e143 0x4c 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e146 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e149 0x49 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e14c 0x49 0xc6 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e150 0x4c 0xff (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e153 0x49 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e156 0x49 0xc7 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e15a 0x48 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e15d 0x49 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e160 0x49 0xc2 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e164 0x4d 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e167 0x4d 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10e16a 0x4c (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r64_effect_step 0x10e16f 13) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10e172 0x4c (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10e177 0x48 (by simp [RexWPrefix]) 1 (.rip 0xf1eaa) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e17e 0x4c 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e181 0x4c 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local)
  ]

def part09Bytes : List UInt8 :=
  [0x4c,0x1,0xe1,0x48,0x3,0xd,0x1f,0x1f,0xf,0x0,0x49,0x89,0xd2,0x4d,0x21,0xca,0x4c,0x1,0xd1,0x49,0x89,0xd2,0x49,0xf7,0xd2,0x4d,0x21,0xc2,0x4d,0x89,0xde,0x49,0xc1,0xc6,0x24,0x4c,0x1,0xd1,0x4d,0x89,0xda,0x49,0xc1,0xc2,0x1e,0x48,0x1,0xf9,0x4d,0x89,0xdf,0x49,0xc1,0xc7,0x19,0x4d,0x31,0xf2,0x4d,0x31,0xd7,0x49,0x89,0xf2,0x49,0x21,0xda,0x48,0x89,0xf7,0x48,0x31,0xdf,0x4c,0x21,0xdf,0x4c,0x31,0xd7,0x48,0x1,0xc8,0x49,0x89,0xc6,0x49,0xc1,0xc6,0x32,0x4c,0x1,0xff,0x49,0x89,0xc7,0x49,0xc1,0xc7,0x2e,0x48,0x1,0xcf,0x49,0x89,0xc2,0x49,0xc1,0xc2,0x17,0x4d,0x31,0xf7,0x4d,0x31,0xfa,0x4c,0x8b,0x6c,0x24,0x18,0x49,0xf,0xcd,0x4c,0x89,0x6c,0x24,0x18,0x48,0x8b,0xd,0xaa,0x1e,0xf,0x0,0x4c,0x1,0xe9,0x4c,0x1,0xc1]

def part09Layout : List (BitVec 64 × Nat) :=
  [(0x10e0f7, 3), (0x10e0fa, 7), (0x10e101, 3), (0x10e104, 3), (0x10e107, 3),
   (0x10e10a, 3), (0x10e10d, 3), (0x10e110, 3), (0x10e113, 3), (0x10e116, 4),
   (0x10e11a, 3), (0x10e11d, 3), (0x10e120, 4), (0x10e124, 3), (0x10e127, 3),
   (0x10e12a, 4), (0x10e12e, 3), (0x10e131, 3), (0x10e134, 3), (0x10e137, 3),
   (0x10e13a, 3), (0x10e13d, 3), (0x10e140, 3), (0x10e143, 3), (0x10e146, 3),
   (0x10e149, 3), (0x10e14c, 4), (0x10e150, 3), (0x10e153, 3), (0x10e156, 4),
   (0x10e15a, 3), (0x10e15d, 3), (0x10e160, 4), (0x10e164, 3), (0x10e167, 3),
   (0x10e16a, 5), (0x10e16f, 3), (0x10e172, 5), (0x10e177, 7), (0x10e17e, 3),
   (0x10e181, 3)]

set_option maxRecDepth 4096 in
theorem part09_bytes [Bindings] : part09.flatMap CheckedInstruction.bytes = part09Bytes := by
  rfl

theorem part09_layout [Bindings] : InstructionTrace.layout part09 = part09Layout := by
  rfl

theorem part09_ordered [Bindings] : InstructionTrace.ordered 0x10e0f7 part09 = true := by
  rw [InstructionTrace.ordered_eq_layout, part09_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part09_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xe0f7 141 = part09Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
