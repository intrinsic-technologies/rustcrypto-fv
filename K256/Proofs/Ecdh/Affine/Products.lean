import K256.Proofs.Ecdh.Affine.Products.Barrier
import K256.Proofs.Ecdh.Affine.Products.Unpack
import K256.Proofs.Ecdh.Affine.Products.Schedule
import K256.Proofs.Ecdh.Affine.Products.Finish

namespace K256.Proofs.Ecdh.Affine

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR
open K256.Proofs.Generate.Generator.Affine
open Standards.SECG.ECC

theorem productsExecution {fr : Activation} {a : Registers} {m : Ram} {x y z : Fin modulus}
    (s : CallState .l10ed84 fr a m) (c : Coordinates m fr.rsi x y z) (h : InverseAt fr m z) :
    ∃ b m', Reaches .l10ed84 a m .l10ee37 b m' ∧ CallState .l10ee37 fr b m' ∧
      SelectionInput fr b m' x y z := by
  obtain ⟨b, m₁, reach, sb, coords, loaded⟩ := loadEcdhInverse s c h
  obtain ⟨d, m₂, call, input⟩ := unpackLoadedInverse sb coords loaded
  obtain ⟨e, n, xl, yl, w, product, norm, slots, kept, frame, hx, _, hw⟩ :=
    ecdhCoordinateProductBlock input
  obtain ⟨o, finish, tag, state, selection⟩ :=
    finishEcdhProducts input norm slots kept frame hx hw
  have run : program.Exec (dialect Extracted.programImage) ⟨⟨.l10e4c0, d, m₂⟩, []⟩ o :=
    .next (by simp only [Program.step, product, Transfer.next]) finish
  refine ⟨_, _, reach.trans (.step (b := ⟨⟨.l10e4c0, d, m₂⟩, [productReturn]⟩) ?_ ?_), state, selection⟩
  · simp only [Program.sem, Program.step, call, Transfer.next]
  · exact ParseSignature.exec_reaches_resume run productReturn [] (by rw [tag]; rfl)

end K256.Proofs.Ecdh.Affine
