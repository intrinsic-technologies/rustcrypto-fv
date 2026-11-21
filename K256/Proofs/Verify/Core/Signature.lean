import K256.Proofs.Verify.Core.Signature.High
import K256.Proofs.Verify.LIR.Generated.Values

namespace K256.Proofs.Verify.Core

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1

variable {fr : Activation} {a : Registers} {p : Curve.Point} {digest : ByteArray} {r s : Nat}

theorem signaturePath (e : Entry fr a p digest r s) :
    if s ≤ domain.n / 2 then
      ∃ b m, Reaches .l104f20 a fr.original .l1050c1 b m ∧ Parsed fr b m r s
    else ∃ b m, Reaches .l104f20 a fr.original .l1050ad b m ∧ Phase fr b m := by
  obtain ⟨b, m, checked, components⟩ := checkComponents e
  obtain ⟨c, t, high, parsed, test⟩ := checkHigh e components
  have validated := checked.trans high
  by_cases low : s ≤ domain.n / 2
  · rw [ite_eq_left low]
    have z : (c[0].get 64).setWidth 8 = 0 := by
      simpa only [Value.get, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64)] using test.mpr low
    have branch : ∃ v, Reaches .l1050a9 c t .l1050c1 v t ∧ Parsed fr v t r s := by
      refine ⟨?_, Semantics.Reaches.single (by
        change program.step _ _ = _
        unfold Program.step
        cfg_eval
        simp only [z, BitVec.and_self, testFlags, Option.getD_some, beq_self_eq_true, ite_true]
        rfl), ?_⟩
      exact ⟨⟨⟨parsed.sp, parsed.dst, parsed.rbp, parsed.df, parsed.mxcsr, parsed.ftw, parsed.fcw, parsed.rbx, parsed.r12, parsed.r13, parsed.r14, parsed.r15⟩, parsed.frame⟩, parsed.r9Width, parsed.atoms, parsed.rAt, parsed.sAt⟩
    obtain ⟨v, reach, h⟩ := branch
    exact ⟨v, t, validated.trans reach, h⟩
  · rw [ite_eq_right low]
    have nz : (c[0].get 64).setWidth 8 ≠ 0 := by
      simpa only [Value.get, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64)] using mt test.mp low
    have branch : ∃ v, Reaches .l1050a9 c t .l1050ad v t ∧ Phase fr v t := by
      refine ⟨?_, Semantics.Reaches.single (by
        change program.step _ _ = _
        unfold Program.step
        cfg_eval
        simp only [testFlags, BitVec.and_self, Option.getD_some, beq_eq_false_iff_ne.mpr nz]
        rfl), ?_⟩
      exact ⟨⟨parsed.sp, parsed.dst, parsed.rbp, parsed.df, parsed.mxcsr, parsed.ftw, parsed.fcw, parsed.rbx, parsed.r12, parsed.r13, parsed.r14, parsed.r15⟩, parsed.frame⟩
    obtain ⟨v, reach, h⟩ := branch
    exact ⟨v, t, validated.trans reach, h⟩

end K256.Proofs.Verify.Core
