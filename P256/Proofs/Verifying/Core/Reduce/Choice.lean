import P256.Proofs.Verifying.Core.Reduce.Values
import P256.Proofs.Program.ScalarFrame.Choice

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Reduce

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program

def choiceFrame (s : RamState) : List Component :=
  [.reg 0, .reg 4, .flags, .rip, .mem (stackPtr s - 8) 8, .mem (stackPtr s - 9) 1]

theorem choice_call [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x113120 32 32 104) (state : FrameState s t)
    (offset : Nat) (disp : BitVec 32) (bound : offset + 5 < 118431)
    (target : branchTarget (Extracted.textAddress + BitVec.ofNat 64 offset) 5
      (disp.signExtend 64) = 0x119070)
    (bytes : Extracted.textBytes.toListFrom offset 5 = encodeCallRel32 disp)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 offset) :
    ∃ u, Advances boundary 6 t u ∧ FrameState s u ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 (offset + 5) ∧
      u.regValue .rax = ((Operand.reg 7 : Operand 8).read t).setWidth 64 ∧
      AgreesExcept (choiceFrame t) t u := by
  obtain ⟨u,run,ready,sp,ip,rax,ag⟩ := ScalarFrame.choice_step pre
    (frameOffset := 88) (by decide) (by decide)
    (readyToStep state.machine state.bindingsSupported)
    state.loaded state.allocated state.rsp offset disp bound bytes target rip
  have narrow : AgreesExcept [.reg 0,.flags,.rip,.mem (stackPtr s-96) 8,
      .mem (stackPtr s-97) 1] t u := by
    apply ag.narrow
    intro c hc hn
    simp only [ScalarFrame.choiceClobbers,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | exact sp | exact (hn (by simp)).elim
  have writes : WritesWithin [.reg 0,.flags,.rip,.mem (stackPtr s-96) 8,
      .mem (stackPtr s-97) 1] #v[registerRegion s .rdi 32,workRegion s] := by
    intro c hc a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl
    all_goals try exact ha.elim
    all_goals exact ⟨workRegion s,by simp,work_contains pre (by decide) (by decide) ha⟩
  refine ⟨u,run,state.after_effect pre (by decide) ready narrow writes (by simp),?_,rax,?_⟩
  · simpa only [BitVec.ofNat_add,BitVec.add_assoc] using ip
  · simpa [choiceFrame,ScalarFrame.choiceClobbers,state.rsp,BitVec.sub_sub] using ag

theorem choice_slot {s t : RamState} (agrees : AgreesExcept (choiceFrame s ++ [.reg 7]) s t)
    {offset : Nat} (ho : offset = 16 ∨ offset = 24 ∨ offset = 32) :
    (Operand.mem (stackPtr s + BitVec.ofNat 64 offset) : Operand 64).read t =
      (Operand.mem (stackPtr s + BitVec.ofNat 64 offset) : Operand 64).read s := by
  apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees agrees
  intro i hi c hc ha
  simp only [choiceFrame, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  all_goals obtain ⟨j,hj,he⟩ := ha
  all_goals rcases ho with rfl | rfl | rfl
  · exact OffsetsApart.ne (c₁ := -8) (c₂ := BitVec.ofNat 64 16) (len₁ := 8) (len₂ := 8)
      (by unfold OffsetsApart; decide +kernel) (stackPtr s) hj hi (by decide)
      (by simpa only [BitVec.sub_eq_add_neg] using he.symm)
  · exact OffsetsApart.ne (c₁ := -8) (c₂ := BitVec.ofNat 64 24) (len₁ := 8) (len₂ := 8)
      (by unfold OffsetsApart; decide +kernel) (stackPtr s) hj hi (by decide)
      (by simpa only [BitVec.sub_eq_add_neg] using he.symm)
  · exact OffsetsApart.ne (c₁ := -8) (c₂ := BitVec.ofNat 64 32) (len₁ := 8) (len₂ := 8)
      (by unfold OffsetsApart; decide +kernel) (stackPtr s) hj hi (by decide)
      (by simpa only [BitVec.sub_eq_add_neg] using he.symm)
  · exact OffsetsApart.ne (c₁ := -9) (c₂ := BitVec.ofNat 64 16) (len₁ := 1) (len₂ := 8)
      (by unfold OffsetsApart; decide +kernel) (stackPtr s) hj hi (by decide)
      (by simpa only [BitVec.sub_eq_add_neg] using he.symm)
  · exact OffsetsApart.ne (c₁ := -9) (c₂ := BitVec.ofNat 64 24) (len₁ := 1) (len₂ := 8)
      (by unfold OffsetsApart; decide +kernel) (stackPtr s) hj hi (by decide)
      (by simpa only [BitVec.sub_eq_add_neg] using he.symm)
  · exact OffsetsApart.ne (c₁ := -9) (c₂ := BitVec.ofNat 64 32) (len₁ := 1) (len₂ := 8)
      (by unfold OffsetsApart; decide +kernel) (stackPtr s) hj hi (by decide)
      (by simpa only [BitVec.sub_eq_add_neg] using he.symm)

end P256.Proofs.Verifying.Core.Reduce
