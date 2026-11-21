import P256.Proofs.Program.Interface
import P256.Proofs.SecretKeyFromBytes.Scalar.Representation
import P256.Spec.Ecdsa

set_option autoImplicit false

namespace P256.Proofs.Signing

open P256.Spec P256.Spec.Program.Routines P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure SignPre [Bindings] (s : RamState) (boundary : ReturnBoundary) : Prop extends
    CalleePre s boundary 0x10c9c0 32 65 4584 where
  digestLength : s.regValue .rcx = 32
  entropyPointer : s.regValue .r8 = 1
  entropyLength : s.regValue .r9 = 0
  digestBounded : (registerRegion s .rdx 32).Bounded
  digestAllocated : (registerRegion s .rdx 32).Allocated s.external
  digestOutput : (registerRegion s .rdx 32).Disjoint (registerRegion s .rdi 65)
  digestStack : (registerRegion s .rdx 32).Disjoint (Stack.region s 4584)

structure SignInput (s : RamState) (secret : Nat) (digest : ByteArray) : Prop where
  scalar : Nat256At s (s.regValue .rsi) secret
  digest : (registerRegion s .rdx 32).HasBytes s.external digest
  positive : 0 < secret
  canonical : secret < Operations.domain.n

def CoreContract : Prop :=
  ∀ [Bindings] {s : RamState} {boundary : ReturnBoundary} {secret : Nat}
    {digest : ByteArray}, SignPre s boundary → SignInput s secret digest →
    (∀ attempts signature, Ecdsa.rfc6979Within attempts secret digest .empty = some signature →
      ∃ t, CalleeResult s t boundary 65 4584 ∧
        Nat256At t (s.regValue .rdi) signature.1 ∧
        Nat256At t (s.regValue .rdi + 32) signature.2) ∧
    ((∀ attempts, Ecdsa.rfc6979Within attempts secret digest .empty = none) →
      Prelude.Diverges boundary s [])

def Result [bindings : Bindings] (initial : RamState) (signingKey msg bytes : ByteArray) : Prop :=
  ∃ (fuel : Nat) (final : RamState),
    UniqueExecution initial fuel final ∧
    SupportedIntegerMachineState bindings.processor final ∧
    MachineRamUnitStrideDecodable bindings final ∧
    CalleeSavedRegistersUnchanged initial final ∧
    DirectionFlagUnset final ∧
    MemoryWriteFrame initial final
      #v[outputRegion signingKeyTrySign initial [signingKey, msg], allocatorStateRegion,
        randomSourceRegion, callStack signingKeyTrySign initial] ∧
    readOutput signingKeyTrySign initial final = .ok bytes

def WrapperContract : Prop :=
  CoreContract → ∀ [bindings : Bindings] {initial : RamState} {signingKey msg : ByteArray},
    MachineRamUnitStrideDecodable bindings initial →
    SupportedIntegerMachineState bindings.processor initial →
    ValidCall signingKeyTrySign initial [signingKey, msg] →
    (∀ attempts bytes, Ecdsa.signMessageWithin attempts #[signingKey, msg] = some (some bytes) →
      Result initial signingKey msg bytes) ∧
    (Ecdsa.NeverSigns #[signingKey, msg] → NeverReturns initial)

end P256.Proofs.Signing
