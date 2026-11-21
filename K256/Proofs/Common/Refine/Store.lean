import K256.Proofs.Common.Lift.IR
import K256.Proofs.Common.Refine.StoreAttr
namespace K256.Proofs.Refine

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.Lift Prelude

def InRegion (r : MemoryRegion) (a : BitVec 64) (n : Nat) : Prop :=
  r.start ≤ a.toNat ∧ a.toNat + n ≤ r.start + r.size ∧ a.toNat + n ≤ 2 ^ 64

def InRegions (regions : List MemoryRegion) (a : BitVec 64) (n : Nat) : Prop :=
  ∃ r ∈ regions, InRegion r a n

def Outside (regions : List MemoryRegion) (a : BitVec 64) (n : Nat) : Prop :=
  a.toNat + n ≤ 2 ^ 64 ∧ ∀ r ∈ regions, a.toNat + n ≤ r.start ∨ r.start + r.size ≤ a.toNat

def RegionsWithin (small big : List MemoryRegion) : Prop :=
  ∀ r ∈ small, ∃ r' ∈ big, r'.start ≤ r.start ∧ r.start + r.size ≤ r'.start + r'.size

structure RamWriteFrame (original mem : Ram) (regions : List MemoryRegion) : Prop where
  outside : ∀ x : BitVec 64, Outside regions x 1 → mem[x]? = original[x]?
  present : ∀ x : BitVec 64, (original[x]?).isSome → (mem[x]?).isSome

structure Readable (mem : Ram) (a : BitVec 64) (len : Nat) : Prop where
  low : a.toNat + len ≤ 2 ^ 32
  present : ∀ i < len, (mem[a + BitVec.ofNat 64 i]?).isSome

structure Writable (code : CodeMap) (mem : Ram) (a : BitVec 64) (len : Nat) : Prop where
  readable : Readable mem a len
  tables : PageTableEntriesApart a.toNat len
  notCode : ∀ x ∈ code, ∀ i < len, x.1 ≠ a + BitVec.ofNat 64 i

def wordAddr (base : BitVec 64) (width i : Nat) : BitVec 64 :=
  base + BitVec.ofNat 64 (width / 8 * i)

def WordsAt (mem : Ram) (base : BitVec 64) (width : Nat) {n : Nat}
    (vals : Vector (BitVec width) n) : Prop :=
  ∀ i (h : i < n), memLoad mem (wordAddr base width i) width = vals[i]

end K256.Proofs.Refine
