import K256.Proofs.Generate.Generator.Multiply.Prepare.Bases.State
import K256.Proofs.Ecdh.Multiply.State

namespace K256.Proofs.Generate.Generator.Multiply.Prepare.Bases

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters.Secp256k1

abbrev peerEndoAt (fr : Activation) (m : Ram) (peer : Projective) :=
  ∃ p : Projective, p.valid ∧ p.Stored m (sp fr + 0x2b0) ∧ p.value = Curve.endomorphism peer.value

structure PeerComparedInput (fr : Activation) (a : Registers) (m : Ram) (d : Nat) (peer : Projective) : Prop extends Context fr a m where
  endo : peerEndoAt fr m peer
  r5 : a[5] = ⟨64,(u d)[0]⟩
  r3 : a[3] = ⟨64,(u d)[1]⟩
  r13 : a[13] = ⟨64,(u d)[2]⟩
  r12 : a[12] = ⟨64,(u d)[3]⟩
  r14 : a[14] = ⟨64,(v d)[0]⟩
  r15 : a[15] = ⟨64,sp fr + 0x1d0⟩
  slots : Locals fr m [(0x40,(v d)[1]),(0x10,(v d)[2]),(0x28,(v d)[3])]

structure PeerCompared (fr : Activation) (a : Registers) (m : Ram) (d : Nat) (peer : Projective) : Prop extends Context fr a m where
  endo : peerEndoAt fr m peer
  firstSign : memLoad m (sp fr + 0x30) 8 = flag (firstComponent d)
  secondSign : a[0].get 8 = flag (secondComponent d)
  r5 : a[5] = ⟨64,(v d)[3]⟩
  r12 : a[12] = ⟨64,(u d)[3]⟩
  r15 : a[15] = ⟨64,sp fr + 0x1d0⟩
  slots : Locals fr m [(0x58,(u d)[0]),(0x70,(u d)[1]),(0x50,(u d)[2]),(0xa8,(v d)[0]),
    (0x40,(v d)[1]),(0x10,(v d)[2]),(0x28,(v d)[3])]

structure PeerNegated (fr : Activation) (a : Registers) (m : Ram) (d : Nat) (peer : Projective) : Prop extends Context fr a m where
  endo : peerEndoAt fr m peer
  firstSign : memLoad m (sp fr + 0x30) 8 = flag (firstComponent d)
  secondSign : memLoad m (sp fr + 0x48) 8 = flag (secondComponent d)
  firstMagnitude : WordsAt m (sp fr + 0x270) 64 (scalarWords (firstComponent d).natAbs)
  negSecond : WordsAt m (sp fr + 0x128) 64 (negative (Curve.splitSecond d))
  r12 : a[12] = ⟨64,(v d)[0]⟩
  r13 : a[13] = ⟨64,(v d)[1]⟩
  r14 : a[14] = ⟨64,(v d)[2]⟩
  r5 : a[5] = ⟨64,(v d)[3]⟩
  r3 : a[3] = ⟨64,0x3ffffffffffffc⟩
  r15 : a[15] = ⟨64,sp fr + 0x1d0⟩

end K256.Proofs.Generate.Generator.Multiply.Prepare.Bases
