import Sha1.Spec.Program
import Sha1.Proofs.Common.Refine
import X86Proofs.Program.ReadWrite.Load
import X86Proofs.Program.ReadWrite.Stack

namespace Sha1.Proofs.Common.Instructions.StorePre

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Proofs.Refine

structure MemWritable (s : RamState) (addr : BitVec 64) (len : Nat) : Prop where
  low : addr.toNat + len ≤ 2 ^ 32
  mem : ∀ i, i < len → (s.external[addr + BitVec.ofNat 64 i]?).isSome
  tables : ∀ i, i < len → ¬ Sha1.Spec.Program.InPageTables (addr + BitVec.ofNat 64 i)

theorem MemWritable.readable {s : RamState} {addr : BitVec 64} {len : Nat}
    (h : MemWritable s addr len) : MemReadable s addr len :=
  ⟨h.low, h.mem⟩

theorem MemWritable.of_external_eq {s t : RamState} {addr : BitVec 64} {len : Nat}
    (h : MemWritable s addr len) (he : t.external = s.external) : MemWritable t addr len :=
  ⟨h.low, fun i hi ↦ he ▸ h.mem i hi, h.tables⟩

structure StorePre (p : BitVec 64) (codeLen : Nat) (addr : RamState → BitVec 64) (len : Nat)
    (s : RamState) : Prop where
  rip : s.RIP = p
  write : MemWritable s (addr s) len
  code : RangeApart (addr s) len p codeLen

abbrev PushPre (p : BitVec 64) (len : Nat) := StorePre p len pushAddr 8

structure StoreOk (code : CodeMap) (mem : Ram) (a : BitVec 64) (len : Nat) (p : BitVec 64)
    (codeLen : Nat) : Prop where
  low : a.toNat + len ≤ 2 ^ 32
  present : ∀ i, i < len → (mem[a + BitVec.ofNat 64 i]?).isSome
  tables : ∀ i, i < len → ¬ Sha1.Spec.Program.InPageTables (a + BitVec.ofNat 64 i)
  apart : RangeApart a len p codeLen
  notCode : ∀ x ∈ code, ∀ i, i < len → x.1 ≠ a + BitVec.ofNat 64 i

end Sha1.Proofs.Common.Instructions.StorePre
