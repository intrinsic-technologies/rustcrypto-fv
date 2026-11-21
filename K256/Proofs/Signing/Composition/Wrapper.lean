import K256.Proofs.Signing.Composition.Wrapper.Decode
import K256.Proofs.Signing.Composition.Wrapper.Multiply
import K256.Proofs.Signing.Composition.Wrapper.Affine
import K256.Proofs.Signing.Composition.Wrapper.Install

namespace K256.Proofs.Signing.Composition

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1

theorem wrapper {s : RamState} {secret msg : ByteArray} {d : Nat}
    (call : ValidCall signingKeyTrySign s [secret,msg])
    (decoded : Keys.decodeSecret domain secret = some d) :
    ∃ a m, Reach ⟨LIR.lifted.locationOf .l102630 s,[]⟩ (core .l105420 a m) ∧ CoreEntry s d msg a m := by
  obtain ⟨_,_,read,hread⟩ := Wrapper.decode call decoded
  obtain ⟨_,_,projective,hprojective⟩ := Wrapper.multiply call decoded hread
  obtain ⟨_,_,affine,haffine⟩ := Wrapper.affine call decoded hprojective
  obtain ⟨a,m,entered,hentered⟩ := Wrapper.install call haffine
  exact ⟨a,m,read.trans (projective.trans (affine.trans entered)),hentered⟩

end K256.Proofs.Signing.Composition
