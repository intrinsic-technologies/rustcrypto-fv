import X86Proofs.Step.Memory
import X86Proofs.Program.ReadWrite.Store

set_option autoImplicit false

namespace Base16ct.Proofs.Copied.P256.Proofs.Common.Instructions.CrossPageStore

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

structure Writable (s : RamState) (addr : BitVec 64) (len : Nat) : Prop
    extends MemReadable s addr len where
  tables : addr.toNat + len ≤ 0x1000 ∨ 0x3000 ≤ addr.toNat

theorem Writable.of_external_eq {s t : RamState} {addr : BitVec 64} {len : Nat}
    (h : Writable s addr len) (he : t.external = s.external) : Writable t addr len :=
  ⟨h.toMemReadable.of_external_eq he, h.tables⟩

structure Pre (p : BitVec 64) (codeLen : Nat) (addr : RamState → BitVec 64) (len : Nat)
    (s : RamState) : Prop where
  rip : s.RIP = p
  write : Writable s (addr s) len
  code : RangeApart (addr s) len p codeLen

end Base16ct.Proofs.Copied.P256.Proofs.Common.Instructions.CrossPageStore
