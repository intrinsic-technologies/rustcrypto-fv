import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part04

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part05 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.load (add_r64_m64_effect_step 0x10df5b 0x4c (by simp [RexWPrefix]) 0 (.rip 0xf20a6) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10df62 0x49 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10df65 0x48 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (not_r64_effect_step 0x10df68 0x48 0xd6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10df6b 0x48 (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d32 320)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10df73 0x48 0xee (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10df76 0x49 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10df79 0x49 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10df7c 0x48 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10df7f 0x48 0xc2 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10df83 0x48 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10df86 0x48 0xc6 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10df8a 0x48 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10df8d 0x48 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10df90 0x48 0xc2 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10df94 0x48 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10df97 0x4c 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10df9a 0x4c 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10df9d 0x4c 0xdb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10dfa0 0x4c 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10dfa3 0x4c (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 312)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10dfab 0x48 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10dfae 0x48 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10dfb1 0x48 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10dfb4 0x4c 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10dfb7 0x4d 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local)
  ]

def part05Bytes : List UInt8 :=
  [0x4c,0x3,0x5,0xa6,0x20,0xf,0x0,0x49,0x1,0xf0,0x48,0x89,0xce,0x48,0xf7,0xd6,0x48,0x89,0xac,0x24,0x40,0x1,0x0,0x0,0x48,0x21,0xee,0x49,0x1,0xf0,0x49,0x1,0xd0,0x48,0x89,0xc2,0x48,0xc1,0xc2,0x24,0x48,0x89,0xc6,0x48,0xc1,0xc6,0x1e,0x48,0x31,0xd6,0x48,0x89,0xc2,0x48,0xc1,0xc2,0x19,0x48,0x31,0xf2,0x4c,0x89,0xde,0x4c,0x21,0xfe,0x4c,0x89,0xdb,0x4c,0x31,0xfb,0x4c,0x89,0xbc,0x24,0x38,0x1,0x0,0x0,0x48,0x21,0xc3,0x48,0x31,0xf3,0x48,0x1,0xd3,0x4c,0x1,0xc3,0x4d,0x1,0xf0]

def part05Layout : List (BitVec 64 × Nat) :=
  [(0x10df5b, 7), (0x10df62, 3), (0x10df65, 3), (0x10df68, 3), (0x10df6b, 8),
   (0x10df73, 3), (0x10df76, 3), (0x10df79, 3), (0x10df7c, 3), (0x10df7f, 4),
   (0x10df83, 3), (0x10df86, 4), (0x10df8a, 3), (0x10df8d, 3), (0x10df90, 4),
   (0x10df94, 3), (0x10df97, 3), (0x10df9a, 3), (0x10df9d, 3), (0x10dfa0, 3),
   (0x10dfa3, 8), (0x10dfab, 3), (0x10dfae, 3), (0x10dfb1, 3), (0x10dfb4, 3),
   (0x10dfb7, 3)]

set_option maxRecDepth 4096 in
theorem part05_bytes [Bindings] : part05.flatMap CheckedInstruction.bytes = part05Bytes := by
  rfl

theorem part05_layout [Bindings] : InstructionTrace.layout part05 = part05Layout := by
  rfl

theorem part05_ordered [Bindings] : InstructionTrace.ordered 0x10df5b part05 = true := by
  rw [InstructionTrace.ordered_eq_layout, part05_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part05_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xdf5b 95 = part05Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
