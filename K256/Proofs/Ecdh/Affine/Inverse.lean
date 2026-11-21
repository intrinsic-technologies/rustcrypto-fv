import K256.Proofs.Ecdh.Affine.Inverse.PackedCall
import K256.Proofs.Ecdh.Affine.Inverse.Zero

namespace K256.Proofs.Ecdh.Affine

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR
open K256.Proofs.Generate.Generator.Affine
open Standards.SECG.ECC

theorem inverseExecution {fr : Activation} {a : Registers} {m : Ram} {x y z : Fin modulus}
    (s : CallState .l10ed05 fr a m) (c : Coordinates m fr.rsi x y z) (n : Normalized fr m z) :
    ∃ b m', Reaches .l10ed05 a m .l10ed84 b m' ∧ CallState .l10ed84 fr b m' ∧
      Coordinates m' fr.rsi x y z ∧ InverseAt fr m' z :=
  Inverse.packedCall Inverse.zeroCoreExecution s c n

end K256.Proofs.Ecdh.Affine
