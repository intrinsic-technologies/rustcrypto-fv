import P256.Proofs.Program.Memory
import P256.Proofs.Common.Instructions.CrossPageStore.Range

set_option autoImplicit false

namespace P256.Proofs.Common.Der.Memory

open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure MemWritable (s : RamState) (addr : BitVec 64) (len : Nat) : Prop where
  low : addr.toNat + len ≤ 2^32
  bytes : ∀ i < len, (s.external[addr + BitVec.ofNat 64 i]?).isSome
  tables : ∀ i < len, ¬ P256.Spec.Program.Routines.InPageTables (addr + BitVec.ofNat 64 i)

theorem MemWritable.readable {s : RamState} {addr : BitVec 64} {len : Nat}
    (h : MemWritable s addr len) : MemReadable s addr len := ⟨h.low, h.bytes⟩

theorem MemWritable.of_external_eq {s t : RamState} {addr : BitVec 64} {len : Nat}
    (h : MemWritable s addr len) (he : t.external = s.external) : MemWritable t addr len :=
  ⟨h.low, fun i hi ↦ he ▸ h.bytes i hi, h.tables⟩

theorem MemWritable.of_region {s : RamState} {addr : BitVec 64} {len : Nat}
    {region : MemoryRegion} (bounded : region.Bounded) (allocated : region.Allocated s.external)
    (tables : region.Avoids P256.Spec.Program.Routines.InPageTables)
    (start : region.start ≤ addr.toNat) (finish : addr.toNat + len ≤ region.start + region.size) :
    MemWritable s addr len := by
  have read := P256.Proofs.Program.memoryRegion_memReadable bounded allocated start finish
  exact ⟨read.low, read.mem, fun i hi ↦ tables _
    (P256.Proofs.Program.memoryRegion_contains_add bounded start finish hi)⟩

theorem MemWritable.memStore {s : RamState} {addr : BitVec 64} {len : Nat}
    (h : MemWritable s addr len) (a : BitVec 64) {n : Nat} (v : BitVec n) :
    MemWritable { s with external := memStore s.external a v } addr len :=
  ⟨h.low, fun i hi ↦ memStore_isSome _ _ _ _ (h.bytes i hi), h.tables⟩

theorem MemWritable.crossPage {s : RamState} {addr : BitVec 64} {len : Nat}
    (h : MemWritable s addr len) (positive : 0 < len) :
    P256.Proofs.Common.Instructions.CrossPageStore.Writable s addr len := by
  refine ⟨h.readable, ?_⟩
  apply PageTableEntriesApart.of_frames
  have low := h.low
  by_cases left : addr.toNat + len ≤ 0x1000
  · exact Or.inl left
  · right
    by_cases below : 12288 ≤ addr.toNat
    · exact below
    apply False.elim
    have index : 0x1000 - addr.toNat < len := by omega
    have nt := h.tables (0x1000 - addr.toNat) index
    apply nt
    unfold P256.Spec.Program.Routines.InPageTables MemoryRegion.Contains
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega

theorem MemWritable.byte {s : RamState} {addr : BitVec 64}
    (h : MemWritable s addr 1) : X86Proofs.MemWritable s addr 1 := by
  exact ⟨h.low, h.bytes, (h.crossPage (by decide)).tables⟩

structure StorePre (p : BitVec 64) (codeLen : Nat) (addr : RamState → BitVec 64) (len : Nat)
    (s : RamState) : Prop where
  rip : s.RIP = p
  write : MemWritable s (addr s) len
  code : RangeApart (addr s) len p codeLen

end P256.Proofs.Common.Der.Memory
