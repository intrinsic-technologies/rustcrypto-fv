import P256.Proofs.Verifying.Combination.Preparation.Naf.SecondSerialize
import P256.Proofs.Verifying.Combination.Loop.Interface
import P256.Proofs.Program.CalleeStackOutput

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Output

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem local_output_disjoint [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {off len : Nat} (pre : Pre s boundary) (output : t.regValue .rdi = s.regValue .rdi)
    (ho : off ≤ 8808) (hl : len ≤ off+8) :
    (localRegion s off len).Disjoint (registerRegion t .rdi 96) := by
  intro a ha hb
  apply pre.separation 1 2 (by decide) a
  · change (registerRegion s .rdi 96).Contains a
    simpa only [registerRegion, output] using hb
  · exact localRegion_sub pre ho hl a ha

theorem multi_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (state : State s t 6560)
    (rip : t.RIP = 0x10efd0) (input : t.regValue .rsi = stackPtr s - 6240)
    (output : t.regValue .rdi = s.regValue .rdi)
    (tables : memLoad t.external (stackPtr s - 6240) 64 = stackPtr s - 3120)
    (tablesEnd : memLoad t.external (stackPtr s - 6232) 64 = stackPtr s - 1584)
    (digits : memLoad t.external (stackPtr s - 6224) 64 = stackPtr s - 4656)
    (digitsEnd : memLoad t.external (stackPtr s - 6216) 64 = stackPtr s - 4112)
    (beginIndex : memLoad t.external (stackPtr s - 6208) 64 = 0)
    (endIndex : memLoad t.external (stackPtr s - 6200) 64 = 2)
    (ret : InProgram (returnBoundary t).rip) :
    Loop.MultiPre t boundary (stackPtr s - 3120) (stackPtr s - 4656) := by
  have cp := CalleePre.of_stack_and_output pre
    (⟨6560,6240,by decide,by decide,by decide,by decide⟩ : StackBufferLayout 8808 48 1432)
    state.bindingsSupported state.machine state.directionFlag state.loaded state.allocated
    rip state.rsp input output ret
  refine ⟨cp, ?_, ?_, ?_, ?_, ?_, ?_,
    localRegion_bounded pre (offset := 3120) (by decide) (by decide),
    localRegion_allocated pre state (offset := 3120) (by decide) (by decide),
    local_output_disjoint pre output (by decide) (by decide), localRegion_stack_disjoint pre state (by decide),
    localRegion_bounded pre (offset := 4656) (by decide) (by decide),
    localRegion_allocated pre state (offset := 4656) (by decide) (by decide),
    local_output_disjoint pre output (by decide) (by decide), localRegion_stack_disjoint pre state (by decide)⟩
  · rw [input]; exact tables
  · rw [input]
    have a : stackPtr s - 6240 + 8 = stackPtr s - 6232 := by
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
    rw [a, tablesEnd]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  · rw [input]
    have a : stackPtr s - 6240 + 16 = stackPtr s - 6224 := by
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
    rw [a]; exact digits
  · rw [input]
    have a : stackPtr s - 6240 + 24 = stackPtr s - 6216 := by
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
    rw [a, digitsEnd]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  · rw [input]
    have a : stackPtr s - 6240 + 32 = stackPtr s - 6208 := by
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
    rw [a]; exact beginIndex
  · rw [input]
    have a : stackPtr s - 6240 + 40 = stackPtr s - 6200 := by
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
    rw [a]; exact endIndex

end P256.Proofs.Verifying.Combination.Output
