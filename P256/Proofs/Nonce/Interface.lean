import P256.Proofs.Nonce.Model
import P256.Proofs.Program.Interface
import P256.Proofs.SecretKeyFromBytes.Scalar.Representation

set_option autoImplicit false

namespace P256.Proofs.Nonce

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

def DrbgAt (s : RamState) (address : BitVec 64) (state : State) : Prop :=
  ({ start := address.toNat, size := 32 } : MemoryRegion).HasBytes s.external state.key ∧
  ({ start := (address + 32).toNat, size := 32 } : MemoryRegion).HasBytes s.external state.value

def GeneratorAt (s : RamState) (address orderAddress : BitVec 64) (state : State) : Prop :=
  memLoad s.external address 64 = orderAddress ∧
  Nat256At s orderAddress P256.Spec.Operations.domain.n ∧ DrbgAt s (address + 8) state

end P256.Proofs.Nonce
