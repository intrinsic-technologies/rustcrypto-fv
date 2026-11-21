import P256.Proofs.Pkcs8.Copy.Support

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper.KeyCopy

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

structure Pre (pc : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = pc
  readable : ∀ off len : Nat, off + len ≤ 65 →
    MemReadable s (s.regValue .rdx + BitVec.ofNat 64 off) len
  writable : CrossPageStore.Writable s (stackPtr s) 65
  apart : RangeApart (stackPtr s) 65 (s.regValue .rdx) 65
  codeApart : ∀ off len : Nat, off + len ≤ 65 → ∀ offset codeLen : Nat,
    offset + codeLen ≤ 118431 → RangeApart (stackPtr s + BitVec.ofNat 64 off) len
      (Extracted.textAddress + BitVec.ofNat 64 offset) codeLen

theorem Pre.byteWritable {pc : BitVec 64} {s : RamState} (h : Pre pc s)
    (off : Nat) (bound : off + 1 ≤ 65) :
    MemWritable s (stackPtr s + BitVec.ofNat 64 off) 1 := by
  have hw := h.writable.add off bound
  exact ⟨hw.low, hw.mem, hw.tables⟩

end P256.Proofs.Verifying.Wrapper.KeyCopy
