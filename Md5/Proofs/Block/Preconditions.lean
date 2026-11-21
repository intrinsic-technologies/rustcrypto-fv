import Md5.Proofs.Block.Frame
import Md5.Proofs.Memory.Basic
import Md5.Proofs.MemoryRoutines.Ranges

namespace Md5.Proofs.Block

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86Proofs

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

theorem memoryWritable_slice {s : RamState} {address : BitVec 64} {length : Nat}
    (h : Memory.MemWritable s address length) (offset count : Nat)
    (hle : offset + count ≤ length) :
    Memory.MemWritable s (address + BitVec.ofNat 64 offset) count := by
  have hr := MemoryRoutines.memReadable_slice h.readable offset count hle
  refine ⟨hr.low, hr.mem, ?_⟩
  intro i hi
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact h.tables (offset + i) (by omega)

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

theorem compression_output_writable {s : RamState} {buffer : Standards.RFC.MD5.Buffer}
    {input : ByteArray} (hBuffer : Call.Compress.ValidBuffer s buffer)
    (hSeparation : Call.Compress.MemorySeparation s input) :
    Memory.MemWritable s (s.regValue .rdi) 16 := by
  apply Memory.MemWritable.of_region hBuffer.1 (allocated_of_hasBytes hBuffer.2)
  · intro address hAddress hTable
    exact hSeparation.2 _ (by simp) address hAddress (.inr hTable)
  · exact Nat.le_refl _
  · exact Nat.le_refl _

theorem compression_stack_writable {s : RamState} {input : ByteArray}
    (hStack : Stack.Valid s Compress.minStackBytes)
    (hSeparation : Call.Compress.MemorySeparation s input) :
    Memory.MemWritable s (stackPtr s - 184) 192 := by
  apply stack_memoryWritable hStack (used := 184) (by decide +kernel)
  intro address hAddress hTable
  exact hSeparation.2 _ (by simp) address hAddress (.inr hTable)

theorem compression_stack_avoids_code {s : RamState} {input : ByteArray}
    (hStack : Stack.Valid s Compress.minStackBytes)
    (hSeparation : Call.Compress.MemorySeparation s input) :
    ∀ i < 192, ¬ InProgram (stackPtr s - 184 + BitVec.ofNat 64 i) := by
  intro i hi hCode
  obtain ⟨hs, he⟩ := stack_subrange_bounds hStack (used := 184) (by decide +kernel)
  exact hSeparation.2 _ (by simp) _
    (contains_offset_of_subrange hStack.1 hs he i hi) (.inl hCode)

theorem compression_stack_input_apart {s : RamState} {input : ByteArray}
    (hInput : Call.Compress.ValidInput s input) (hStack : Stack.Valid s Compress.minStackBytes)
    (hSeparation : Call.Compress.MemorySeparation s input) :
    RangeApart (stackPtr s - 184) 192 (s.regValue .rsi) input.size := by
  intro i hi j hj heq
  have hd : (Compress.inputRegion s input).Disjoint (Stack.region s Compress.minStackBytes) :=
    hSeparation.1 0 2 (by decide +kernel)
  have hinput : (Compress.inputRegion s input).Contains
      (s.regValue .rsi + BitVec.ofNat 64 j).toNat :=
    contains_offset_of_subrange hInput.1 (Nat.le_refl _) (Nat.le_refl _) j hj
  obtain ⟨hs, he⟩ := stack_subrange_bounds hStack (used := 184) (by decide +kernel)
  have hstack := contains_offset_of_subrange hStack.1 hs he i hi
  rw [show BitVec.ofNat 64 184 = (184 : BitVec 64) by rfl, heq] at hstack
  exact hd _ hinput hstack

theorem compression_stack_output_apart {s : RamState} {buffer : Standards.RFC.MD5.Buffer}
    {input : ByteArray} (hBuffer : Call.Compress.ValidBuffer s buffer)
    (hStack : Stack.Valid s Compress.minStackBytes)
    (hSeparation : Call.Compress.MemorySeparation s input) :
    RangeApart (stackPtr s - 184) 192 (s.regValue .rdi) 16 := by
  intro i hi j hj heq
  have hd : (Compress.outputRegion s).Disjoint (Stack.region s Compress.minStackBytes) :=
    hSeparation.1 1 2 (by decide +kernel)
  have houtput : (Compress.outputRegion s).Contains
      (s.regValue .rdi + BitVec.ofNat 64 j).toNat :=
    contains_offset_of_subrange hBuffer.1 (Nat.le_refl _) (Nat.le_refl _) j hj
  obtain ⟨hs, he⟩ := stack_subrange_bounds hStack (used := 184) (by decide +kernel)
  have hstack := contains_offset_of_subrange hStack.1 hs he i hi
  rw [show BitVec.ofNat 64 184 = (184 : BitVec 64) by rfl, heq] at hstack
  exact hd _ houtput hstack

end Md5.Proofs.Block
