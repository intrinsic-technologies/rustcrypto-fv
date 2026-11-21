import K256.Proofs.Signing.Affine.Products.Barrier
import K256.Proofs.Signing.Affine.Products.Unpack
import K256.Proofs.Signing.Affine.Products.Multiply

namespace K256.Proofs.Signing.Affine

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR
open Standards.SECG.ECC
open K256.Proofs.Generate.Generator.Affine

theorem multiplyCoordinates {fr : Activation} {a : Registers} {m : Ram} {x y z : Fin modulus}
    (s : CallState .l10ed84 fr a m)
    (h : Coordinates m fr.rsi x y z) (hi : Inverted fr m z) (nz : z.val ≠ 0) :
    ∃ b m', Reaches .l10ed84 a m .l10ee37 b m' ∧ CallState .l10ee37 fr b m' ∧
      Products fr b m' (toAffine x y z) := by
  obtain ⟨b, m₁, reach, sb, coords, loaded⟩ := loadInverse s h hi
  obtain ⟨c, m₂, call, input⟩ := unpackInverse sb coords loaded
  obtain ⟨out, run, tag, post⟩ := multiplyPoint input nz
  refine ⟨_, _, reach.trans (.step (b := ⟨⟨.l10e4c0, c, m₂⟩, [productReturn]⟩) ?_ ?_), post⟩
  · simp only [Program.sem, Program.step, call, Transfer.next]
  · exact ParseSignature.exec_reaches_resume run productReturn [] (by rw [tag]; rfl)

end K256.Proofs.Signing.Affine
