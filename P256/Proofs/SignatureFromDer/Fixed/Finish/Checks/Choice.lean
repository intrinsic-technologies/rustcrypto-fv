import P256.Proofs.SignatureFromDer.Fixed.FrameLemmas
import P256.Proofs.Program.ScalarFrame.Choice

set_option autoImplicit false

namespace P256.Proofs.SignatureFromDer.Fixed.Finish.Checks

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

abbrev choiceClobbers (s : RamState) := ScalarFrame.choiceClobbers s 184

theorem choice_call [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x109ac0 64 72 560) (state : Stage s t boundary)
    (offset : Nat) (disp : BitVec 32) (bound : offset + 5 < 118431)
    (bytes : Extracted.textBytes.toListFrom offset 5 = encodeCallRel32 disp)
    (target : branchTarget (Extracted.textAddress + BitVec.ofNat 64 offset) 5
      (disp.signExtend 64) = 0x119070)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 offset) :
    ∃ u, Stage s u boundary ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 offset + 5#64 ∧
      u.regValue .rax = ((Operand.reg 7 : Operand 8).read t).setWidth 64 ∧
      AgreesExcept (choiceClobbers s) t u := by
  obtain ⟨u, run, ready, rsp, ip, ax, frame⟩ := ScalarFrame.choice_step pre
    (frameOffset := 184) (by decide) (by decide)
    (readyToStep state.machine state.bindingsSupported) state.loaded state.allocated
    state.rsp offset disp bound bytes target rip
  have writes : WritesWithin (choiceClobbers s) #v[registerRegion s .rdi 72, workRegion s] := by
    intro c hc a ha
    simp only [choiceClobbers, ScalarFrame.choiceClobbers, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals exact ⟨workRegion s, by simp, ScalarFrame.Work.contains pre (by decide) (by decide) ha⟩
  exact ⟨u, state.after pre run ready frame writes (rsp.trans state.rsp)
    (by simp [ScalarFrame.choiceClobbers]), ip, ax, frame⟩

theorem choice_scalar [Bindings] {s t u : RamState} {d off : Nat}
    (state : Frame s t) (agrees : AgreesExcept (choiceClobbers s) t u)
    (bound : off + 32 ≤ 184)
    (scalar : P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At t (stackPtr t + BitVec.ofNat 64 off) d) :
    P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At u (stackPtr t + BitVec.ofNat 64 off) d := by
  have base : stackPtr t + BitVec.ofNat 64 off =
      (stackPtr s - 193#64) + BitVec.ofNat 64 (9+off) := by
    rw [state.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.ofNat_add, BitVec.add_assoc]
    rw [← BitVec.add_assoc (-193#64)]
    rfl
  refine ⟨scalar.1, fun i hi => ?_⟩
  rw [agrees.byte]
  · exact scalar.2 i hi
  · intro c hc hv
    simp only [choiceClobbers, ScalarFrame.choiceClobbers, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hv.elim
    all_goals obtain ⟨j, hj, he⟩ := hv
    all_goals rw [base] at he
    · apply RangeApart.offsets (stackPtr s - 193#64) (a := 1) (b := 9+off)
        (len := 8) (count := 32) (by decide) (by omega) (.inl (by omega)) j hj i hi
      have hbase : stackPtr s - 193#64 + 1#64 = stackPtr s - 192#64 := by
        simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
        rfl
      simpa only [hbase] using he.symm
    · apply RangeApart.offsets (stackPtr s - 193#64) (a := 0) (b := 9+off)
        (len := 1) (count := 32) (by decide) (by omega) (.inl (by omega)) j hj i hi
      simpa only [BitVec.add_zero] using he.symm

end P256.Proofs.SignatureFromDer.Fixed.Finish.Checks
