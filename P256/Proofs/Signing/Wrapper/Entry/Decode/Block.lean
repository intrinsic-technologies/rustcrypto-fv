import P256.Proofs.SecretKeyFromBytes.Scalar.Borrow
import P256.Proofs.Common.EffectCompose.Memory

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Entry.Decode

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program Prelude
open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

structure BlockPre (p : BitVec 64) (reads writes : List (Nat × Nat)) (s : RamState) : Prop where
  rip : s.RIP = p
  readable : ∀ pair ∈ reads, MemReadable s (stackPtr s + BitVec.ofNat 64 pair.1) pair.2
  writable : ∀ pair ∈ writes,
    CrossPageStore.Writable s (stackPtr s + BitVec.ofNat 64 pair.1) pair.2
  codeApart : ∀ pair ∈ writes, ∀ offset len : Nat, offset + len ≤ 118431 →
    RangeApart (stackPtr s + BitVec.ofNat 64 pair.1) pair.2
      (Extracted.textAddress + BitVec.ofNat 64 offset) len

end P256.Proofs.Signing.Wrapper.Entry.Decode
