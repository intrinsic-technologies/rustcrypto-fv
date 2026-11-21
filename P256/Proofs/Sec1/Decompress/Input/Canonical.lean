import P256.Proofs.Sec1.Decompress.Input.Canonical.Borrow
import P256.Proofs.Common.Encoding.Serialize.Convert.SavePointer
import P256.Proofs.Sec1.Decompress.Input.Canonical.Validity
import P256.Proofs.Field.Montgomery.Reduction.CorrectionArithmetic

set_option autoImplicit false

open P256.Proofs.Field.Montgomery.Reduction (subtractModulus subtractModulus_borrow)

namespace P256.Proofs.Sec1.Decompress.Input

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem canonical_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hout : ¬ InProgram boundary.rip) (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (pre : CanonicalPre 0x10fc44 s) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      CanonicalPre 0x10fcd0 t ∧ AgreesExcept (canonicalFrame s) s t ∧
      (Operand.reg 3 : Operand 64).read t =
        (if (canonicalInput s).toNat < P256.Spec.Operations.domain.p then 1 else 0) ∧
      (Operand.mem (stackPtr s + 184#64) : Operand 64).read t =
        (Operand.reg 7 : Operand 64).read s ∧
      (Operand.reg 14 : Operand 64).read t = 0xffffffff00000001 := by
  obtain ⟨n, u, run, rd, ld, hp, hf, hv, hm, h14⟩ := canonical_borrow_correct hout ready loaded pre
  obtain ⟨m, t, run', rd', ld', hp', he, hf'⟩ :=
    canonical_run (s := u) (q := 0x10fcd0) (offset := 0xfcc5)
      (canonical_validity_correct boundary hout) (by decide +kernel) (by decide +kernel)
      rd ld hp hp.toBorrowSlotPre rfl
      (by simp [canonicalValidityEffect, Effect.components, canonicalFrame])
  refine ⟨n+m, t, run.trans run', rd', ld', hp', canonical_trans hf hf', ?_, ?_, ?_⟩
  · have hx : (subtractModulus (canonicalInput s)).2 =
        if (canonicalInput s).toNat < P256.Spec.Operations.domain.p then 1 else 0 := by
      apply BitVec.eq_of_toNat_eq
      have h := subtractModulus_borrow (canonicalInput s)
      by_cases hc : (canonicalInput s).toNat < P256.Spec.Operations.domain.p
      · rw [ite_eq_left hc]
        exact h.trans (by rw [ite_eq_left hc]; rfl)
      · rw [ite_eq_right hc]
        exact h.trans (by rw [ite_eq_right hc]; rfl)
    have hw := he.writes.2
    change (Operand.reg 3 : Operand 64).read t =
      (((Operand.reg 0 : Operand 64).read u).setWidth 8 &&& 1).setWidth 64 at hw
    rw [hv, hx] at hw
    by_cases hc : (canonicalInput s).toNat < P256.Spec.Operations.domain.p
    · rw [ite_eq_left hc] at hw ⊢
      exact hw.trans (by decide +kernel)
    · rw [ite_eq_right hc] at hw ⊢
      exact hw.trans (by decide +kernel)
  · apply Eq.trans ?_ hm
    apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees he.agrees
    intro i hi c hc
    simp only [canonicalValidityEffect, Effect.components, List.map_cons,
      Write.component_mem, Write.component_reg, List.map_nil] at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with ((rfl | rfl) | rfl) | rfl
    · rintro ⟨j, hj, hh⟩
      rw [canonical_stack hf] at hh
      apply OffsetsApart.ne (c₁ := 0#64) (len₁ := 8) (c₂ := 184#64) (len₂ := 8)
        (by unfold OffsetsApart; decide +kernel) (stackPtr s) hj hi (by decide)
      rw [BitVec.add_zero]
      exact hh.symm
    all_goals exact id

  · exact (he.agrees.read (n := 64) (r := 14)
      (by simp [canonicalValidityEffect, Effect.components])).trans h14

end P256.Proofs.Sec1.Decompress.Input
