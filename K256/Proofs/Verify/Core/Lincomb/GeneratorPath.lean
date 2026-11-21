import K256.Proofs.Verify.Core.Lincomb.GeneratorPath.ZeroDigits
import K256.Proofs.Verify.Core.Lincomb.GeneratorPath.Prepare

namespace K256.Proofs.Verify.Core.Lincomb

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Affine (ProjectiveAt)

variable {fr : Activation} {a b c : Registers} {p : Curve.Point} {digest : ByteArray}
    {r s u v : Nat} {m : Ram}

theorem generatorPath (e : Entry fr a p digest r s) (h : Products fr b m u v r)
    (args : Arguments fr b c) (hu : u < domain.n) :
    ∃ d n, Reaches .l10fb20 c (push m fr) .l10fba8 d n ∧
      CallerFrame fr c d m n ∧ GeneratorPrepared fr d n u := by
  obtain ⟨x, t, path, f, regs, zeros⟩ := zeroGeneratorDigits e h args
  obtain ⟨d, n, tail, f, gen⟩ := generatorPrepare e h args hu f regs zeros
  exact ⟨d, n, path.trans tail, f, gen⟩

end K256.Proofs.Verify.Core.Lincomb
