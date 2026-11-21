import K256.Proofs.Signing.Composition.Attempt.Inverse.Wrapper.Enter
import K256.Proofs.Signing.Composition.Attempt.Inverse.Wrapper.Choice
import K256.Proofs.Signing.Composition.Attempt.Inverse.Wrapper.Return

namespace K256.Proofs.Signing.Composition.Attempt.Inverse

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Verify.Core (Registers)
open Generate.Generator.Multiply (scalarWords)
open Generate.Generator.Affine.Invert.Core (CalleeFrame CalleeResult)

theorem invertNonce (execute : CoreExecution) {s : RamState} {secret msg : ByteArray} {d : Nat}
    (call : ValidCall signingKeyTrySign s [secret,msg]) {a : Registers} {m : Ram} {st : State} {k : Nat}
    (reduced : DigestReduced s d msg st k a m) (pos : 0 < k) (bound : k < domain.n) :
    ∃ b n, Reach (core .l105afc a m) (core .l105b23 b n) ∧ ScalarsReady s d msg st k b n := by
  obtain ⟨b,n,start,entry,regs,saved,writes⟩ := enterCore call reduced pos bound
  obtain ⟨c,t,middle,unmasked,saves,changed⟩ :=
    passInverseChoice execute call reduced entry regs saved writes
  obtain ⟨e,q,finish,ready⟩ := returnInverse call reduced unmasked saves changed
  exact ⟨e,q,start.trans (middle.trans finish),ready⟩

end K256.Proofs.Signing.Composition.Attempt.Inverse
