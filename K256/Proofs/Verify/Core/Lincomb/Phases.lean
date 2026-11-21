import K256.Proofs.Verify.Core.Lincomb.Stack

namespace K256.Proofs.Verify.Core.Lincomb

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Affine (ProjectiveAt)


structure GeneratorPrepared (fr : Activation) (b : Registers) (m : Ram) (u : Nat) : Prop where
  prepared : Prepared m (slot fr 0x1568) (slot fr 0x228) domain.G u
  memset : b[3] = ⟨64, 0x12a700⟩
  tablePtr : b[5] = ⟨64, slot fr 0x1568⟩
  digitsPtr : b[13] = ⟨64, slot fr 0x228⟩
  scalar : b[14] = ⟨64, localSp fr + 416⟩
  key : b[15] = ⟨64, fr.rsi⟩

structure PeerPrepared (fr : Activation) (b : Registers) (m : Ram) (p : Curve.Point) (u v : Nat) : Prop where
  generator : Prepared m (slot fr 0xbc8) (slot fr 0x1348) domain.G u
  peer : Prepared m (slot fr 0x1568) (slot fr 8) p v
  memcpy : b[12] = ⟨64, 0x12a820⟩
  tablePtr : b[13] = ⟨64, slot fr 0x1568⟩
  digitsPtr : b[5] = ⟨64, slot fr 8⟩

end K256.Proofs.Verify.Core.Lincomb
