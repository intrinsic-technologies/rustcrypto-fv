import Base16ct.Proofs.Copied.Md5.Proofs.Block.Frame
import Base16ct.Proofs.Copied.Md5.Proofs.Memory.Basic
import Base16ct.Proofs.Copied.Md5.Proofs.MemoryRoutines.Contracts
namespace Base16ct.Proofs.Copied.Md5.Proofs.Block

open Base16ct.Proofs.Copied.Md5.Spec Base16ct.Proofs.Copied.Md5.Spec.Program Prelude X86 X86.Machine X86Proofs

theorem allocated_of_hasBytes {m : Ram} {region : MemoryRegion} {bytes : ByteArray}
    (h : region.HasBytes m bytes) : region.Allocated m := by
  intro address hContains
  have hi : address.toNat - region.start < bytes.size := by
    have hs := h.1
    unfold MemoryRegion.HasLength at hs
    obtain ⟨hl, hh⟩ := hContains
    omega
  have hb := h.2 ⟨address.toNat - region.start, hi⟩
  have he : region.start + (address.toNat - region.start) = address.toNat := by
    have hl := hContains.1
    omega
  refine ⟨bytes[address.toNat - region.start], ?_⟩
  simpa only [he, BitVec.ofNat_toNat, BitVec.setWidth_eq] using hb

theorem rangeApart_of_disjoint {a b : MemoryRegion} (ha : a.Bounded) (hb : b.Bounded)
    (hd : a.Disjoint b) :
    RangeApart (BitVec.ofNat 64 a.start) a.size (BitVec.ofNat 64 b.start) b.size := by
  intro i hi j hj he
  have hca := contains_of_mem_covers ha ⟨i, hi, rfl⟩
  have hcb := contains_of_mem_covers hb ⟨j, hj, he⟩
  exact hd _ hca hcb

theorem stack_subrange_bounds {s : RamState} {budget used : Nat}
    (h : Stack.Valid s budget) (hused : used ≤ budget) :
    (Stack.region s budget).start ≤ (stackPtr s - BitVec.ofNat 64 used).toNat ∧
      (stackPtr s - BitVec.ofNat 64 used).toNat + (used + 8) ≤
        (Stack.region s budget).start + (Stack.region s budget).size := by
  have hs : budget ≤ (stackPtr s).toNat := h.2.2.1
  have hu : used < 2^64 := by have := (stackPtr s).isLt; omega
  have hstart : (stackPtr s - BitVec.ofNat 64 used).toNat = (stackPtr s).toNat - used := by
    rw [BitVec.toNat_sub_of_le (by
      simp only [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu]
      omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu]
  rw [hstart]
  change (stackPtr s).toNat - budget ≤ (stackPtr s).toNat - used ∧
    (stackPtr s).toNat - used + (used + 8) ≤
      ((stackPtr s).toNat - budget) +
        ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - budget))
  omega

theorem contains_offset_of_subrange {region : MemoryRegion} {addr : BitVec 64} {len : Nat}
    (hb : region.Bounded) (hs : region.start ≤ addr.toNat)
    (he : addr.toNat + len ≤ region.start + region.size) (i : Nat) (hi : i < len) :
    region.Contains (addr + BitVec.ofNat 64 i).toNat := by
  have hlow : region.start + region.size < 2^32 := hb
  have hi64 : i < 2^64 := by omega
  have hsum : addr.toNat + i < 2^64 := by omega
  simp only [MemoryRegion.Contains, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hi64, Nat.mod_eq_of_lt hsum]
  omega

theorem stack_memoryWritable {s : RamState} {budget used : Nat}
    (h : Stack.Valid s budget) (hused : used ≤ budget)
    (htables : (Stack.region s budget).Avoids InPageTables) :
    Memory.MemWritable s (stackPtr s - BitVec.ofNat 64 used) (used + 8) := by
  obtain ⟨hs, he⟩ := stack_subrange_bounds h hused
  exact Memory.MemWritable.of_region h.1 h.2.1 htables hs he

end Base16ct.Proofs.Copied.Md5.Proofs.Block
