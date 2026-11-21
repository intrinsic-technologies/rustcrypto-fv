import K256.Proofs.Verify.Core.Lincomb.Phases

namespace K256.Proofs.Verify.Core.Lincomb

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Affine (ProjectiveAt)


def PreparesPeer (fr : Activation) (x : Registers) (digits : Nat) : Prop :=
  x[3] = ⟨64, 0x12a700⟩ ∧ x[12] = ⟨64, 0x12a820⟩ ∧ x[14] = ⟨64, localSp fr + 416⟩ ∧
    x[15] = ⟨64, fr.rsi⟩ ∧ x[5] = ⟨64, slot fr digits⟩

abbrev GeneratorCopy (fr : Activation) (m : Ram) (u : Nat) :=
  Prepared m (slot fr 0xbc8) (slot fr 0x1348) domain.G u

end K256.Proofs.Verify.Core.Lincomb
