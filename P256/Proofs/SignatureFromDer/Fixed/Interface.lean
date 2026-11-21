import P256.Spec
import P256.Proofs.Program.Interface
import P256.Proofs.SecretKeyFromBytes.Scalar.Representation

set_option autoImplicit false

namespace P256.Proofs.SignatureFromDer.Fixed

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

def ResultAt (s : RamState) (address : BitVec 64) (input : ByteArray) : Prop :=
  match Ecdsa.decodeSignature input with
  | none => loadBytes s.external address 8 = .ok (1 : BitVec 64) ∧
      memLoad s.external (address + 8) 64 = 0
  | some value => loadBytes s.external address 8 = .ok (0 : BitVec 64) ∧
      Nat256At s (address + 8) value.1 ∧ Nat256At s (address + 40) value.2

end P256.Proofs.SignatureFromDer.Fixed
