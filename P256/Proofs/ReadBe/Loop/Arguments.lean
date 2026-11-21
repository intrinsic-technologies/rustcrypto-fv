import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.ReadBe

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure LoopArgumentsPre (s : RamState) : Prop where
  rip : s.RIP = 0x119110
  count : (Operand.reg 0 : Operand 64).read s = 8
  negative : (Operand.reg 6 : Operand 64).read s = -8

def loopArgumentsBytes : List UInt8 :=
  [0x4c,0x89,0xe9,0x48,0x29,0xc1,0x4c,0x89,0xea,0x48,0x29,0xca,
   0x4c,0x01,0xe6,0x48,0x8d,0x7c,0x24,0x10,0x48,0x29,0xd7,0x48,0x83,0xc7,0x08]

def loopArgumentsEffect (s : RamState) : Effect :=
  { rip := 0x11912b
    writes := [
      ⟨(.reg 1 : Operand 64), (Operand.reg 13 : Operand 64).read s - 8⟩,
      ⟨(.reg 2 : Operand 64), 8⟩,
      ⟨(.reg 6 : Operand 64), (Operand.reg 12 : Operand 64).read s - 8⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 16⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

set_option maxHeartbeats 800000 in
theorem loop_arguments [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary LoopArgumentsPre (codeRange 0x119110 loopArgumentsBytes)
      (Effect.post loopArgumentsEffect) := by
  have next (i : Nat) (hi : i < 118431) :
      Extracted.textAddress + BitVec.ofNat 64 i ≠ boundary.rip :=
    boundary_ne_program outside (inProgram_of_textOffset i hi)
  have h1 := next 0x19113 (by decide +kernel)
  have h2 := next 0x19116 (by decide +kernel)
  have h3 := next 0x19119 (by decide +kernel)
  have h4 := next 0x1911c (by decide +kernel)
  have h5 := next 0x1911f (by decide +kernel)
  have h6 := next 0x19124 (by decide +kernel)
  have h7 := next 0x19127 (by decide +kernel)
  have h8 := next 0x1912b (by decide +kernel)
  unfold loopArgumentsBytes
  advance_begin mov_r64_r64_effect_step 0x119110 0x4c 0xe9 (by simp [RexWPrefix]) rfl
  advance_then sub_r64_r64_effect_step 0x119113 0x48 0xc1 (by simp [RexWPrefix]) rfl
  advance_then mov_r64_r64_effect_step 0x119116 0x4c 0xea (by simp [RexWPrefix]) rfl
  advance_then sub_r64_r64_effect_step 0x119119 0x48 0xca (by simp [RexWPrefix]) rfl
  advance_then add_r64_r64_effect_step 0x11911c 0x4c 0xe6 (by simp [RexWPrefix]) rfl
  advance_then lea_r64_effect_step 0x11911f 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d8 16)) (by simp [AddrMode.Valid]) rfl rfl
  advance_then sub_r64_r64_effect_step 0x119124 0x48 0xd7 (by simp [RexWPrefix]) rfl
  advance_then add_r64_imm8_effect_step 0x119127 0x48 0xc7 8 (by simp [RexWPrefix]) rfl rfl
  case sub => exact codeRange_slice_subset 0x119110 loopArgumentsBytes 23 4
  apply AdvanceTriple.block_end
  intro s t hp hh
  apply hh.weaken
  · x86_norm [loopArgumentsEffect]
  · x86_norm [loopArgumentsEffect]
    change
      (Operand.reg 13 : Operand 64).read s - 8 =
        (Operand.reg 13 : Operand 64).read s - (Operand.reg 0 : Operand 64).read s ∧
      8 = (Operand.reg 13 : Operand 64).read s -
        ((Operand.reg 13 : Operand 64).read s - (Operand.reg 0 : Operand 64).read s) ∧
      (Operand.reg 12 : Operand 64).read s - 8 =
        (Operand.reg 6 : Operand 64).read s + (Operand.reg 12 : Operand 64).read s ∧
      stackPtr s + 16 = stackPtr s + 16 -
        ((Operand.reg 13 : Operand 64).read s -
          ((Operand.reg 13 : Operand 64).read s - (Operand.reg 0 : Operand 64).read s)) + 8
    rw [hp.count, hp.negative]
    have cancel (x : BitVec 64) : x - (x - 8) = 8 := by
      rw [BitVec.sub_eq_add_neg, BitVec.neg_sub, ← BitVec.add_assoc,
        BitVec.add_right_neg, BitVec.zero_add]
    rw [cancel, BitVec.sub_add_cancel]
    exact ⟨rfl, rfl, by rw [BitVec.sub_eq_add_neg, BitVec.add_comm], rfl⟩
  · intro i
    cases i <;> x86_norm [loopArgumentsEffect]
  · x86_norm [loopArgumentsEffect]
  all_goals first
    | exact codeRange_slice_subset 0x119110 loopArgumentsBytes 3 3
    | exact codeRange_slice_subset 0x119110 loopArgumentsBytes 6 3
    | exact codeRange_slice_subset 0x119110 loopArgumentsBytes 9 3
    | exact codeRange_slice_subset 0x119110 loopArgumentsBytes 12 3
    | exact codeRange_slice_subset 0x119110 loopArgumentsBytes 15 5
    | exact codeRange_slice_subset 0x119110 loopArgumentsBytes 20 3

end P256.Proofs.ReadBe
