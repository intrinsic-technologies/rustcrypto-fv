import K256.Proofs.Signing.Nonce.Fill.Test.Range

namespace K256.Proofs.Signing.Nonce.Fill

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (scalarWords)
open Verify.Core (Registers Reaches)
open Initialize (State StateAt)

theorem test {fr : Activation} {state : State} {a : Registers} (env : Environment fr)
    {m : Ram} (decoded : Decoded fr state a m) :
    ∃ b n, Reaches .l100c8a a m (testTarget (candidate state).1) b n ∧ Tested fr state b n := by
  obtain ⟨c,p,zero,compared⟩ := testZero env decoded
  obtain ⟨b,n,range,tested⟩ := testRange env compared
  exact ⟨b,n,zero.trans range,tested⟩

end K256.Proofs.Signing.Nonce.Fill
