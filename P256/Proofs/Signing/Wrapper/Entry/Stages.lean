import P256.Proofs.Signing.Wrapper.Entry.Prologue

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Entry

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Decoded [Bindings] (initial s : RamState) (secret : ByteArray) : Prop extends
    State initial s 520 where
  rip : s.RIP = 0x10263e
  pointers : s.regValue .r12 = initial.regValue .rdi
  lengths : memLoad s.external (stackPtr initial - 192) 64 = initial.regValue .rdx
  count : s.regValue .r13 = 2
  scalar : Nat256At s (stackPtr initial - 520) (Ecdsa.secretValue secret)
  input : Nat256At s (stackPtr initial - 344) (Ecdsa.secretValue secret)
  output : memLoad s.external (stackPtr initial - 208) 64 = initial.regValue .rcx
  capacity : memLoad s.external (stackPtr initial - 200) 64 = initial.regValue .r8

structure Constructed [Bindings] (initial s : RamState) (secret : ByteArray) : Prop extends
    State initial s 520 where
  rip : s.RIP = 0x102706
  pointers : s.regValue .r12 = initial.regValue .rdi
  lengths : memLoad s.external (stackPtr initial - 192) 64 = initial.regValue .rdx
  scalar : Nat256At s (stackPtr initial - 152) (Ecdsa.secretValue secret)
  output : memLoad s.external (stackPtr initial - 208) 64 = initial.regValue .rcx
  capacity : memLoad s.external (stackPtr initial - 200) 64 = initial.regValue .r8

def DecodeContract : Prop :=
  ∀ [Bindings] {initial s : RamState} {secret message : ByteArray},
    Context initial secret message → GuardedEntry initial s secret →
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ Decoded initial t secret

def ConstructContract : Prop :=
  ∀ [Bindings] {initial s : RamState} {secret message : ByteArray},
    Context initial secret message → Decoded initial s secret →
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ Constructed initial t secret

def HashCallContract : Prop :=
  ∀ [Bindings] {initial s : RamState} {secret message : ByteArray},
    Context initial secret message → Constructed initial s secret →
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ HashEntry initial t secret message

end P256.Proofs.Signing.Wrapper.Entry
