import P256.Proofs.SignatureFromDer.Fixed.Scalar.RangeState
import P256.Proofs.SignatureFromDer.Fixed.Scalar.Finish.Choice
import P256.Proofs.SignatureFromDer.Fixed.Scalar.Finish.Branch
import P256.Proofs.SignatureFromDer.Fixed.Scalar.Finish.Output
import P256.Proofs.SignatureFromDer.Fixed.Scalar.Finish.Epilogue

set_option autoImplicit false

open P256.Proofs.Program (CalleePre CalleeResult)

namespace P256.Proofs.SignatureFromDer.Fixed.Scalar

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

private theorem finish_result [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {input : ByteArray} (pre : CalleePre s boundary 0x10fa20 32 40 288)
    (state : Finish.Stage s t boundary) (rip : t.RIP = 0x10fb96)
    (result : ScalarResultAt t (s.regValue .rdi) input) :
    ∃ u, CalleeResult s u boundary 40 288 ∧ ScalarResultAt u (s.regValue .rdi) input := by
  obtain ⟨u, hu, memory⟩ := scalar_restore pre state.toFrameState state.execution rip
  refine ⟨u, hu, ?_⟩
  simpa only [ScalarResultAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, memory] using result

theorem scalar_finish [Bindings] {s u : RamState} {boundary : ReturnBoundary}
    {input : ByteArray} (pre : CalleePre s boundary 0x10fa20 32 40 288)
    (state : ComparedState s u boundary input) :
    ∃ t, CalleeResult s t boundary 40 288 ∧ ScalarResultAt t (s.regValue .rdi) input := by
  have initial : Finish.Stage s u boundary := ⟨state.toFrameState, state.execution, state.output⟩
  obtain ⟨a, ast, arip, aax, af⟩ := Finish.choice_call pre initial 0xfb74 0x94f7
    (by decide) (by decide +kernel) (by decide +kernel) state.rip
  have ax : a.regValue .rax =
      if decide (Arith.uint input < Operations.domain.n) then 1 else 0 := by
    rw [aax]
    change ((u.regValue .rdi).setWidth 8).setWidth 64 = _
    rw [state.valid]
    split <;> simp_all
  obtain ⟨b, bst, brip, bf⟩ := Finish.range_branch pre ast arip ax
  by_cases range : Arith.uint input < Operations.domain.n
  · have start : b.RIP = 0x10fb7d := by simpa only [range, decide_true, ite_true] using brip
    have bound : Arith.uint input < 2^256 :=
      Nat.lt_trans range (by decide +kernel : Operations.domain.n < 2^256)
    obtain ⟨t, st, tip, tag, scalar⟩ := Finish.accept pre bst start bound
      ((bf.read (n := 64) (r := 15) (by simp)).trans
        ((af.read (n := 64) (r := 15) (by simp [Finish.choiceClobbers])).trans state.limb0))
      ((bf.read (n := 64) (r := 12) (by simp)).trans
        ((af.read (n := 64) (r := 12) (by simp [Finish.choiceClobbers])).trans state.limb1))
      ((bf.read (n := 64) (r := 13) (by simp)).trans
        ((af.read (n := 64) (r := 13) (by simp [Finish.choiceClobbers])).trans state.limb2))
      ((bf.read (n := 64) (r := 5) (by simp)).trans
        ((af.read (n := 64) (r := 5) (by simp [Finish.choiceClobbers])).trans state.limb3))
    exact finish_result pre st tip (by simpa only [ScalarResultAt, range, ite_true] using And.intro tag scalar)
  · have start : b.RIP = 0x10fb90 := by simpa [range] using brip
    have initialTag : b.regValue .r14 = 1 :=
      (bf.read (n := 64) (r := 14) (by simp)).trans
        ((af.read (n := 64) (r := 14) (by simp [Finish.choiceClobbers])).trans state.tag)
    obtain ⟨t, st, tip, tag⟩ := Finish.reject pre bst start initialTag
    exact finish_result pre st tip (by simpa only [ScalarResultAt, range, ite_false] using tag)

end P256.Proofs.SignatureFromDer.Fixed.Scalar
