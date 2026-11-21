import K256.Proofs.Verify.Core.Signature
import K256.Proofs.Verify.Core.Scalars
import K256.Proofs.Verify.Core.Lincomb
import K256.Proofs.Verify.Core.Affine
import K256.Proofs.Verify.Core.Return

namespace K256.Proofs.Verify.Core

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1

theorem execution {fr : Activation} {a : Registers} {p : Curve.Point} {digest : ByteArray}
    {r s : Nat} (e : Entry fr a p digest r s) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l104f20, a, fr.original⟩, []⟩ out ∧
      Result fr out (decide (s ≤ domain.n / 2) &&
        (Nat.mod (affineX (verificationPoint p digest r s)) domain.n == r)) := by
  have sig := signaturePath e
  by_cases lo : s ≤ domain.n / 2
  · rw [ite_eq_left lo] at sig
    obtain ⟨b, m, start, parsed⟩ := sig
    obtain ⟨c, n, sc, products⟩ := scalarPath e parsed
    have pos : 0 < domain.n := by decide +kernel
    obtain ⟨d, t, comb, point⟩ := lincombPath e (Nat.mod_lt _ pos) (Nat.mod_lt _ pos) products
    obtain ⟨f, w, cmp, done⟩ := comparePath e point
    change Reaches _ _ _ (if Nat.mod (affineX (verificationPoint p digest r s)) domain.n = r then
      .l10536b else .l10536f) _ _ at cmp
    by_cases eq : Nat.mod (affineX (verificationPoint p digest r s)) domain.n = r
    · rw [ite_eq_left eq] at cmp
      obtain ⟨out, run, post⟩ := returnPath e .verified done
      exact ⟨out, Program.Exec.of_sem ((start.trans (sc.trans (comb.trans cmp))).exec run.sem),
        by simpa [lo, eq, Exit.accepts] using post⟩
    · rw [ite_eq_right eq] at cmp
      obtain ⟨out, run, post⟩ := returnPath e .mismatch done
      exact ⟨out, Program.Exec.of_sem ((start.trans (sc.trans (comb.trans cmp))).exec run.sem),
        by simpa [lo, beq_eq_false_iff_ne.mpr eq, Exit.accepts] using post⟩
  · rw [ite_eq_right lo] at sig
    obtain ⟨b, m, start, done⟩ := sig
    obtain ⟨out, run, post⟩ := returnPath e .highS done
    exact ⟨out, Program.Exec.of_sem (start.exec run.sem),
      by simpa [lo, Exit.accepts] using post⟩

end K256.Proofs.Verify.Core
