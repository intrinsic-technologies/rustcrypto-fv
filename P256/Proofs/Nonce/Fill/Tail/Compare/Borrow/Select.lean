import P256.Proofs.Nonce.Fill.Tail.Compare.Borrow.Branch
import X86Proofs.Instructions.And.Generated.R8M8.Triple
import P256.Proofs.Common.Field.SquareRoot.Exponent.ReadDigit.State

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Tail.Compare.Borrow

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Signing.Search
open P256.Proofs.Common.Instructions.ByteOps.ByteOps

open Classical in
theorem select [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {original state : Nonce.State}
    (pre : Fill.Pre initial boundary orderAddress original)
    (input : Compared initial s orderAddress state) (rip : s.RIP = 0x1076b2)
    (nonzero : (s.regValue .rax).setWidth 8 = ~~~(if (nextCandidate state).1 = 0 then 1 else 0))
    (borrow : memLoad s.external (stackPtr s + 8) 64 =
      if (nextCandidate state).1 < P256.Spec.Operations.domain.n then 1 else 0) :
    ∃ t, Advances boundary 5 s t ∧ Compared initial t orderAddress state ∧
      t.RIP = if ValidNonce (nextCandidate state).1 then 0x1076e5 else 0x1076c3 := by
  obtain ⟨a, runA, readyA, effectA⟩ := (and_r8_m8_effect_step 0x1076b2 0 (by decide) (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl).advances
    (readyToStep input.machine input.bindingsSupported)
    (programText_slice (programLoaded_codeIn input.loaded) 0x76b2 _
      (by decide) (by decide +kernel))
    ⟨rip, stack_readable pre input.toFrame (offset := 8) (len := 1) (by decide)⟩
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x76b6 (by decide)))
  have agreesA : AgreesExcept [.reg 0, .flags, .rip] s a := effectA.agrees
  have inputA := input.after_registers readyA agreesA
    (by simp [Component.Covers]) (by simp) (by simp) (by simp)
  have value : (a.regValue .rax).setWidth 8 =
      (s.regValue .rax).setWidth 8 &&& memLoad s.external (stackPtr s + 8) 8 := by
    have h := congrArg (BitVec.setWidth 8) effectA.writes
    change (a.regValue .rax).setWidth 8 =
      (mergeGPR 8 ((s.regValue .rax).setWidth 8 &&&
        memLoad s.external (stackPtr s + 8) 8) (s.regValue .rax)).setWidth 8 at h
    exact h.trans (mergeGPR_low8 _ _)
  have small : memLoad s.external (stackPtr s + 8) 8 =
      if (nextCandidate state).1 < P256.Spec.Operations.domain.n then 1 else 0 := by
    rw [← P256.Proofs.Common.Field.SquareRoot.memLoad_setWidth_of_le _ _ (m := 64) (by decide) (by decide), borrow]
    split <;> rfl
  have choice : (a.regValue .rax).setWidth 8 &&& 1 =
      if ValidNonce (nextCandidate state).1 then 1 else 0 := by
    rw [value, nonzero, small]
    unfold ValidNonce
    by_cases hz : (nextCandidate state).1 = 0
    · rw [ite_eq_left hz, ite_eq_right (by omega : ¬(0 < (nextCandidate state).1 ∧
        (nextCandidate state).1 < P256.Spec.Operations.domain.n))]
      by_cases hl : (nextCandidate state).1 < P256.Spec.Operations.domain.n
      · rw [ite_eq_left hl]; rfl
      · rw [ite_eq_right hl]; rfl
    · rw [ite_eq_right hz]
      by_cases hl : (nextCandidate state).1 < P256.Spec.Operations.domain.n
      · rw [ite_eq_left hl, ite_eq_left ⟨by omega, hl⟩]; rfl
      · rw [ite_eq_right hl, ite_eq_right (by omega : ¬(0 < (nextCandidate state).1 ∧
          (nextCandidate state).1 < P256.Spec.Operations.domain.n))]; rfl
  obtain ⟨t, runT, inputT, target⟩ := branch pre inputA effectA.rip choice
  exact ⟨t, runA.trans runT, inputT, target⟩

end P256.Proofs.Nonce.Fill.Tail.Compare.Borrow
