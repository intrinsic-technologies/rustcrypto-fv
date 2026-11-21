import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Basic
import Base16ct.Proofs.Copied.Md5.Proofs.Buffered.Stores.Program
import Base16ct.Proofs.Copied.Md5.Proofs.Buffered.Update.Slices.Byte.Store
namespace Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine

open Base16ct.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem rangeApart_text {addr : BitVec 64} {len offset count : Nat}
    (ha : ∀ i < len, ¬ InProgram (addr + BitVec.ofNat 64 i))
    (hb : offset + count ≤ Extracted.textBytes.size) :
    RangeApart addr len (Extracted.textAddress + BitVec.ofNat 64 offset) count := by
  intro i hi j hj he
  apply ha i hi
  rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact text_address_in_program (offset + j) (by omega)

theorem store_avoids_program {e : Effect} {addr : BitVec 64} {len : Nat}
    (hc : e.components = [.mem addr len, .rip])
    (ha : ∀ i < len, ¬ InProgram (addr + BitVec.ofNat 64 i)) :
    e.Avoids Extracted.programImage := by
  intro x hx c hm hcov
  rw [hc] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · obtain ⟨i, hi, he⟩ := hcov
    exact ha i hi ⟨x.2, he ▸ hx⟩
  · exact hcov

theorem region_offset_contains {region : MemoryRegion} (h : region.Bounded)
    {i : Nat} (hi : i < region.size) :
    region.Contains ((BitVec.ofNat 64 region.start) + BitVec.ofNat 64 i).toNat := by
  have hb : region.start + region.size < 2^32 := h
  rw [← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact ⟨by omega, by omega⟩

theorem pageTables_contains_of_md5 {address : BitVec 64}
    (h : Base16ct.Proofs.Copied.Md5.Spec.Program.InPageTables address) : pageTables.Contains address.toNat := by
  obtain ⟨r, hr, hc⟩ := h
  simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · change 0x1000 ≤ address.toNat ∧ address.toNat < 0x1000 + 8 at hc
    change 0x1000 ≤ address.toNat ∧ address.toNat < 0x1000 + 0x2000
    omega
  · change 0x2000 ≤ address.toNat ∧ address.toNat < 0x2000 + 32 at hc
    change 0x1000 ≤ address.toNat ∧ address.toNat < 0x1000 + 0x2000
    omega

theorem writable_of_region {s : RamState} {region : MemoryRegion}
    (hb : region.Bounded) (ha : region.Allocated s.external)
    (ht : region.Avoids (fun a ↦ pageTables.Contains a.toNat)) :
    Base16ct.Proofs.Copied.Md5.Proofs.Memory.MemWritable s (BitVec.ofNat 64 region.start) region.size := by
  apply Base16ct.Proofs.Copied.Md5.Proofs.Memory.MemWritable.of_region hb ha
    (fun a hc hmd5 ↦ ht a hc (pageTables_contains_of_md5 hmd5))
  all_goals have hs : region.start < 2^64 := by
              have hb' : region.start + region.size < 2^32 := hb
              omega
            simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs]
            omega

theorem writable_word_of_aligned {s : RamState} {addr : BitVec 64}
    (h : Base16ct.Proofs.Copied.Md5.Proofs.Memory.MemWritable s addr 8)
    (_hAlign : addr.toNat % 8 = 0)
    (hReserved : ∀ i < 8, ¬ PageTableReserved (addr + BitVec.ofNat 64 i)) :
    X86Proofs.MemWritable s addr 8 := by
  exact X86Proofs.MemWritable.of_not_reserved (by decide) h.low h.bytes hReserved

theorem validInput_bytes {s : RamState} {input : ByteArray} (h : ValidInput s input) :
    Bytes s.external (s.regValue .rdi) input.size (fun i ↦ input[i]!) := by
  intro i hi
  have hbyte := h.2.2.2 ⟨i, hi⟩
  simpa only [inputRegion, registerRegion, BitVec.ofNat_add, BitVec.ofNat_toNat,
    BitVec.setWidth_eq, getElem!_pos input i hi] using hbyte

theorem validCall_output_writable {s : RamState} {input : ByteArray} {capacity : Nat} {lengthWritten : Prop}
    (h : ValidCall base16ctMixedDecode s input capacity (input.size / 2) lengthWritten) :
    Base16ct.Proofs.Copied.Md5.Proofs.Memory.MemWritable s (s.regValue .rcx) capacity := by
  have hav := h.separation.2.1 (outputRegion s capacity) (by simp)
  have hw := writable_of_region h.outputInMemory.2.1 h.outputInMemory.2.2
    (fun a hc ht ↦ hav a hc (.inr ht))
  simpa only [outputRegion, registerRegion, BitVec.ofNat_toNat, BitVec.setWidth_eq] using hw

theorem validCall_output_avoids {s : RamState} {input : ByteArray} {capacity : Nat} {lengthWritten : Prop}
    (h : ValidCall base16ctMixedDecode s input capacity (input.size / 2) lengthWritten) :
    ∀ i < capacity, ¬ InProgram (s.regValue .rcx + BitVec.ofNat 64 i) := by
  intro i hi
  have hc := region_offset_contains h.outputInMemory.2.1 hi
  have hav := h.separation.2.1 (outputRegion s capacity) (by simp)
  apply fun hp ↦ hav _ ?_ (.inl hp)
  simpa only [outputRegion, registerRegion, BitVec.ofNat_toNat, BitVec.setWidth_eq] using hc

end Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine
