import P256.Proofs.SignatureFromDer.Fixed.FrameLemmas
import P256.Proofs.SignatureFromDer.Model
import P256.Proofs.SignatureFromDer.Fixed.Finish.Checks.Run
import P256.Proofs.SignatureFromDer.Fixed.Finish.Branch
import P256.Proofs.SignatureFromDer.Fixed.Finish.Output

set_option autoImplicit false

open P256.Proofs.Program (CalleePre CalleeResult readyToStep)

namespace P256.Proofs.SignatureFromDer.Fixed

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

theorem fixed_reject [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {input : ByteArray} (pre : CalleePre s boundary 0x109ac0 64 72 560)
    (state : Stage s t boundary) (rip : t.RIP = 0x109c57)
    (decode : Ecdsa.decodeSignature input = none) :
    ∃ u, CalleeResult s u boundary 72 560 ∧ ResultAt u (s.regValue .rdi) input := by
  obtain ⟨u, result, tag⟩ := Finish.reject pre state rip
  exact ⟨u, result, by simpa only [ResultAt, decode] using tag⟩

theorem fixed_finish [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {input : ByteArray} (pre : CalleePre s boundary 0x109ac0 64 72 560)
    (size : input.size = 64) (state : DecodedState s t boundary input) :
    ∃ u, CalleeResult s u boundary 72 560 ∧ ResultAt u (s.regValue .rdi) input := by
  obtain ⟨a, ast, arip, aax, ax, ay⟩ :=
    Finish.Checks.check pre state.toStage false state.rip state.first state.second
  simp only [Bool.false_eq_true, ite_false] at arip aax
  obtain ⟨b, runb, readyb, brip, fb⟩ := Finish.zero_branch false
    (zero := decide (Arith.uint (input.extract 0 32) = 0))
    (readyToStep ast.machine ast.bindingsSupported) ast.loaded pre.outerBoundary arip
    (by simpa only [decide_eq_true_eq] using aax)
  have bst := ast.after_registers runb readyb fb (by simp [Component.Covers]) (by simp)
  by_cases first : Arith.uint (input.extract 0 32) = 0
  · exact fixed_reject pre bst (by simpa only [first, decide_true, ite_true] using brip)
      ((decodeSignature_none_iff_zero size state.firstRange state.secondRange).2 (.inl first))
  · have bstart : b.RIP = 0x109c09 := by simpa [first] using brip
    have memory := fb.external (by simp [Component.Covers])
    have rsp : stackPtr b = stackPtr a := fb.read (n := 64) (r := 4) (by simp)
    have bx : Nat256At b (stackPtr b + 104#64)
        (Arith.uint (input.extract 0 32)) := by
      simpa only [Nat256At, memory, rsp] using ax
    have by' : Nat256At b (stackPtr b + 136#64)
        (Arith.uint (input.extract 32 64)) := by
      simpa only [Nat256At, memory, rsp] using ay
    obtain ⟨c, cst, crip, cax, cx, cy⟩ := Finish.Checks.check pre bst true bstart bx by'
    simp only [ite_true] at crip cax
    obtain ⟨d, rund, readyd, drip, fd⟩ := Finish.zero_branch true
      (zero := decide (Arith.uint (input.extract 32 64) = 0))
      (readyToStep cst.machine cst.bindingsSupported) cst.loaded pre.outerBoundary crip
      (by simpa only [decide_eq_true_eq] using cax)
    have dst := cst.after_registers rund readyd fd (by simp [Component.Covers]) (by simp)
    by_cases second : Arith.uint (input.extract 32 64) = 0
    · exact fixed_reject pre dst (by simpa only [second, decide_true, ite_true] using drip)
        ((decodeSignature_none_iff_zero size state.firstRange state.secondRange).2 (.inr second))
    · have dstart : d.RIP = 0x109c74 := by simpa [second] using drip
      have memory := fd.external (by simp [Component.Covers])
      have rsp : stackPtr d = stackPtr c := fd.read (n := 64) (r := 4) (by simp)
      have dx : Nat256At d (stackPtr d + 104#64)
          (Arith.uint (input.extract 0 32)) := by
        simpa only [Nat256At, memory, rsp] using cx
      have dy : Nat256At d (stackPtr d + 136#64)
          (Arith.uint (input.extract 32 64)) := by
        simpa only [Nat256At, memory, rsp] using cy
      obtain ⟨u, result, tag, ux, uy⟩ := Finish.accept pre dst dstart dx dy
      have decode := decodeSignature_eq size
      rw [ite_eq_left ⟨Nat.pos_of_ne_zero first, state.firstRange,
        Nat.pos_of_ne_zero second, state.secondRange⟩] at decode
      exact ⟨u, result, by simpa only [ResultAt, decode] using And.intro tag ⟨ux, uy⟩⟩

end P256.Proofs.SignatureFromDer.Fixed
