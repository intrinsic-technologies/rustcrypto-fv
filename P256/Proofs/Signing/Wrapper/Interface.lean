import P256.Proofs.Signing.Interface

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Context [bindings : Bindings] (initial : RamState)
    (secret message : ByteArray) : Prop where
  bindingsSupported : MachineRamUnitStrideDecodable bindings initial
  machine : SupportedIntegerMachineState bindings.processor initial
  call : ValidCall signingKeyTrySign initial [secret, message]

structure State [bindings : Bindings] (initial s : RamState) (offset : Nat) : Prop where
  execution : ∃ fuel, Advances (returnBoundary initial) fuel initial s
  bindingsSupported : MachineRamUnitStrideDecodable bindings s
  machine : SupportedIntegerMachineState bindings.processor s
  loaded : ProgramLoaded s
  directionFlag : DirectionFlagUnset s
  rsp : stackPtr s = stackPtr initial - BitVec.ofNat 64 offset
  savedRbx : memLoad s.external (stackPtr initial - 48) 64 = initial.regValue .rbx
  savedR12 : memLoad s.external (stackPtr initial - 40) 64 = initial.regValue .r12
  savedR13 : memLoad s.external (stackPtr initial - 32) 64 = initial.regValue .r13
  savedR14 : memLoad s.external (stackPtr initial - 24) 64 = initial.regValue .r14
  savedR15 : memLoad s.external (stackPtr initial - 16) 64 = initial.regValue .r15
  savedRbp : memLoad s.external (stackPtr initial - 8) 64 = initial.regValue .rbp
  returnAddress : memLoad s.external (stackPtr initial) 64 = (returnBoundary initial).rip
  allocated : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome
  frame : MemoryWriteFrame initial s
    #v[allocatorStateRegion, randomSourceRegion, callStack signingKeyTrySign initial]

def messageRegion (s : RamState) (message : ByteArray) : MemoryRegion :=
  ⟨(memLoad s.external (s.regValue .rdi + 8) 64).toNat, message.size⟩

structure HashInput (initial s : RamState) (secret : Nat) : Prop where
  scalar : Nat256At s (stackPtr initial - 152) secret
  positive : 0 < secret
  canonical : secret < Operations.domain.n

structure HashPre [Bindings] (initial s : RamState) (secret message : ByteArray) : Prop extends
    State initial s 520 where
  context : Context initial secret message
  rip : s.RIP = 0x102720
  pointer : s.regValue .rsi = memLoad initial.external (initial.regValue .rdi + 8) 64
  length : s.regValue .rbp = BitVec.ofNat 64 message.size
  output : memLoad s.external (stackPtr initial - 208) 64 = initial.regValue .rcx
  capacity : memLoad s.external (stackPtr initial - 200) 64 = initial.regValue .r8

structure HashEntry [Bindings] (initial s : RamState) (secret message : ByteArray) : Prop extends
    HashPre initial s secret message where
  input : HashInput initial s (Ecdsa.secretValue secret)

structure SerializedInput [Bindings] (initial s : RamState) (signature : Nat × Nat) : Prop extends
    State initial s 520 where
  rip : s.RIP = 0x102a3e
  status : s.regValue .rbp = 0
  first : Nat256At s (stackPtr initial - 456) signature.1
  second : Nat256At s (stackPtr initial - 424) signature.2
  output : memLoad s.external (stackPtr initial - 208) 64 = initial.regValue .rcx
  capacity : memLoad s.external (stackPtr initial - 200) 64 = initial.regValue .r8

structure HashResult [Bindings] (initial s t : RamState) (signature : Nat × Nat) : Prop extends
    SerializedInput initial t signature where
  run : ∃ fuel, Advances (returnBoundary initial) fuel s t

def HashContract : Prop :=
  CoreContract → ∀ [Bindings] {initial s : RamState} {secret message : ByteArray},
    HashEntry initial s secret message →
    (∀ attempts signature,
      Ecdsa.rfc6979Within attempts (Ecdsa.secretValue secret)
        (Operations.hash message) .empty = some signature →
      ∃ t, HashResult initial s t signature) ∧
    ((∀ attempts, Ecdsa.rfc6979Within attempts (Ecdsa.secretValue secret)
      (Operations.hash message) .empty = none) →
      Prelude.Diverges (returnBoundary initial) s [])

def EntryContract : Prop :=
  ∀ [Bindings] {initial : RamState} {secret message : ByteArray}, Context initial secret message →
    ∃ s, HashEntry initial s secret message

def FinishContract : Prop :=
  ∀ [Bindings] {initial s : RamState} {secret message : ByteArray} {signature : Nat × Nat},
    Context initial secret message → SerializedInput initial s signature →
    Result initial secret message (Ecdsa.encodeFixed signature)

end P256.Proofs.Signing.Wrapper
