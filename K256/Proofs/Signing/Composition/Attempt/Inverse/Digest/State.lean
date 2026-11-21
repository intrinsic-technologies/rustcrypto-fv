import K256.Proofs.Signing.Composition.Attempt.Inverse.State

namespace K256.Proofs.Signing.Composition.Attempt.Inverse

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Verify.Core (Registers)
open Generate.Generator.Multiply (scalarWords)
open Standards.NIST.SHA2

structure DigestFilled (s : RamState) (d : Nat) (msg : ByteArray) (st : State) (k : Nat)
    (a : Registers) (m : Ram) : Prop extends LoopMemory s d msg st m,
    RegistersAt s a (sp s+456) (sp s+192) (sp s+656) (sp s+160) where
  nonce : WordsAt m (sp s+624) 64 (scalarWords k)
  digest : WordsAt m (sp s+256) 64 (scalarWords (Encoding.octetsToNat (SHA256.hashBytes msg)))

end K256.Proofs.Signing.Composition.Attempt.Inverse
