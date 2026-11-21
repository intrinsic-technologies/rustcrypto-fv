import K256.Proofs.Generate.Generator.Affine.Invert.Core
import K256.Proofs.Generate.Generator.Affine.Invert.PackCall

namespace K256.Proofs.Generate.Generator.Affine

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR
open Standards.SECG.ECC

theorem invertZ {fr : Activation} {a : Registers} {m : Ram} {x y z : Fin modulus}
    (s : State .l10ed05 fr a m)
    (h : Coordinates m fr.rsi x y z) (hn : Normalized fr m z) (nz : z.val ≠ 0) :
    ∃ b m', Reaches .l10ed05 a m .l10ed84 b m' ∧ State .l10ed84 fr b m' ∧
      Coordinates m' fr.rsi x y z ∧ Inverted fr m' z := by
  exact Invert.packedCall Invert.coreExecution s h hn nz

end K256.Proofs.Generate.Generator.Affine
