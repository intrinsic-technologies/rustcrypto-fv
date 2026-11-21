import Base16ct.Spec.Program
import X86Proofs.Program.Entry
import X86Proofs.Program.Execution
import X86Proofs.Program.ReadWrite.WriteFrame
import X86Proofs.Program.ReadWrite.Bytes
import X86Proofs.Step.Sse

namespace Base16ct.Proofs.EncodeStr.Upper

open Base16ct.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem programSections_low : SectionsLow Extracted.programSections := by
  decide +kernel

theorem entryReady (bindings : Machine.Bindings) {s : Machine.RamState}
    (hBindings : MachineRamUnitStrideDecodable bindings s)
    (hMachine : SupportedIntegerMachineState bindings.processor s)
    (hLoaded : ProgramLoaded s) :
    @EntryReady bindings Extracted.programImage s := by
  letI := bindings
  exact EntryReady.of_sections hMachine hBindings.smrr hBindings.memoryType
    hBindings.leadingZeroCount hLoaded programSections_low

theorem supportedIntegerMachineState_of_ready [bindings : Machine.Bindings]
    {s t : Machine.RamState} {cs : List Component}
    (h : ReadyToStep t) (he : AgreesExcept cs s t)
    (hs : Prelude.SupportedSSE bindings.processor s) :
    SupportedIntegerMachineState bindings.processor t :=
  ⟨h.cpu, X86Proofs.SupportedSSE.of_agreesExcept he hs, h.memory, h.ready⟩

theorem memReadable_of_allocated {s : Machine.RamState} {region : MemoryRegion}
    {addr : BitVec 64} {len : Nat} (h : region.Allocated s.external)
    (hlow : addr.toNat + len ≤ userAddressLimit)
    (hstart : region.start ≤ addr.toNat)
    (hend : addr.toNat + len ≤ region.start + region.size) :
    MemReadable s addr len := by
  refine ⟨hlow, ?_⟩
  intro i hi
  apply Option.isSome_iff_exists.mpr
  apply h
  have hi64 : i < 2^64 := by unfold userAddressLimit at hlow; omega
  have hsum : addr.toNat + i < 2^64 := by unfold userAddressLimit at hlow; omega
  simp only [MemoryRegion.Contains, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hi64, Nat.mod_eq_of_lt hsum]
  omega

theorem stack_return_readable {s : Machine.RamState} {bytes : Nat}
    (h : Stack.Valid s bytes) : MemReadable s (stackPtr s) 8 := by
  rcases h with ⟨hb, ha, hn, _⟩
  have hstart : (Stack.region s bytes).start ≤ (stackPtr s).toNat := by
    change (s.regValue .rsp).toNat - bytes ≤ (s.regValue .rsp).toNat
    omega
  have hend : (Stack.region s bytes).start + (Stack.region s bytes).size =
      (stackPtr s).toNat + 8 := by
    change ((s.regValue .rsp).toNat - bytes) +
      ((s.regValue .rsp).toNat + 8 - ((s.regValue .rsp).toNat - bytes)) =
      (s.regValue .rsp).toNat + 8
    omega
  apply memReadable_of_allocated ha
  · change (Stack.region s bytes).start + (Stack.region s bytes).size < userAddressLimit at hb
    omega
  · exact hstart
  · omega

theorem program_text_slice {s : RamState} (hCode : CodeIn Extracted.programImage s)
    (offset count : Nat) (h : offset + count ≤ Extracted.textBytes.size) :
    CodeIn (codeRange (Extracted.textAddress + BitVec.ofNat 64 offset)
      (Extracted.textBytes.toListFrom offset count)) s :=
  hCode.slice_of_section
    (sec := ⟨Extracted.textAddress, Extracted.textBytes⟩)
    (by simp [Extracted.programSections]) offset count h

theorem text_address_in_program (offset : Nat) (h : offset < Extracted.textBytes.size) :
    InProgram (Extracted.textAddress + BitVec.ofNat 64 offset) := by
  have hLength : offset < Extracted.textBytes.toList.length := by
    rwa [chunked_toList_length]
  refine ⟨Extracted.textBytes.toList[offset], ?_⟩
  change _ ∈ Extracted.programSections.flatMap ImageSection.toCodeMap
  apply List.mem_flatMap.mpr
  refine ⟨⟨Extracted.textAddress, Extracted.textBytes⟩,
    by simp [Extracted.programSections], ?_⟩
  exact mem_codeRange _ _ offset hLength

theorem text_address_ne_return {boundary : ReturnBoundary} (hOutside : ¬ InProgram boundary.rip)
    (offset : Nat) (h : offset < Extracted.textBytes.size) :
    Extracted.textAddress + BitVec.ofNat 64 offset ≠ boundary.rip := by
  intro hEq
  exact hOutside (hEq ▸ text_address_in_program offset h)

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

theorem contains_of_mem_covers {region : MemoryRegion} (hBounded : region.Bounded)
    {address : BitVec 64}
    (hCovers : Component.Covers (.mem (BitVec.ofNat 64 region.start) region.size) address) :
    region.Contains address.toNat := by
  obtain ⟨i, hi, rfl⟩ := hCovers
  have hStart : region.start < 2^64 := by
    unfold MemoryRegion.Bounded userAddressLimit at hBounded
    omega
  have hIndex : i < 2^64 := by
    unfold MemoryRegion.Bounded userAddressLimit at hBounded
    omega
  have hSum : region.start + i < 2^64 := by
    unfold MemoryRegion.Bounded userAddressLimit at hBounded
    omega
  simp only [MemoryRegion.Contains, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hStart, Nat.mod_eq_of_lt hIndex, Nat.mod_eq_of_lt hSum]
  omega

theorem returnBoundary_rip_of_word64At {s : RamState} {address : BitVec 64}
    (h : (Stack.returnSlot s).Word64At s.external address)
    (hr : MemReadable s (stackPtr s) 8) :
    (returnBoundary s).rip = address := by
  have hb : Bytes s.external (stackPtr s) 8
      (storedByte (memLoad s.external (stackPtr s) 64)) :=
    Bytes.of_memLoad (n := 64) hr.mem
  have hload : Machine.loadBytes s.external (stackPtr s) 8 = .ok address := by
    change Machine.loadBytes s.external (s.regValue .rsp) 8 = .ok address
    simpa only [Stack.returnSlot, BitVec.ofNat_toNat, BitVec.setWidth_eq] using h.2
  exact Except.ok.inj (hb.loadBytes64.symm.trans hload)

theorem returnBoundary_valid {s : RamState} {budget : Nat}
    (hs : Stack.Valid s budget) (hr : ValidReturnAddress s) :
    (returnBoundary s).rip.toNat < userAddressLimit ∧ ¬ InProgram (returnBoundary s).rip := by
  obtain ⟨address, hw, hl, ho⟩ := hr
  rw [returnBoundary_rip_of_word64At hw (stack_return_readable hs)]
  exact ⟨hl, ho⟩

theorem nearReturn64Boundary_of_valid [Bindings] {s : RamState} {budget : Nat}
    (h : ReadyToStep s) (hs : Stack.Valid s budget) :
    Prelude.nearReturn64Boundary s = .ok (returnBoundary s) :=
  nearReturn64Boundary_eq s h.dataReady h.cpu.ss (stack_return_readable hs)

theorem memWritable_of_region {s : RamState} {addr : BitVec 64} {len : Nat}
    {region : MemoryRegion} (hb : region.Bounded) (ha : region.Allocated s.external)
    (ht : region.Avoids (fun address => pageTables.Contains address.toNat))
    (hs : region.start ≤ addr.toNat) (he : addr.toNat + len ≤ region.start + region.size)
    (_hp : addr.toNat % 4096 + len ≤ 4096) (hpos : 0 < len) :
    MemWritable s addr len := by
  have hr := memReadable_of_allocated ha (by
    have : region.start + region.size < userAddressLimit := hb
    omega) hs he
  apply MemWritable.of_not_reserved hpos hr.low hr.mem
  intro i hi
  exact ht _ (contains_offset_of_subrange hb hs he i hi)

theorem stack_memoryWritable {s : RamState} {budget back count : Nat}
    (h : Stack.Valid s budget) (hback : back ≤ budget) (hcount : count ≤ back + 8)
    (ht : (Stack.region s budget).Avoids (fun address => pageTables.Contains address.toNat))
    (hp : (stackPtr s - BitVec.ofNat 64 back).toNat % 4096 + count ≤ 4096)
    (hpos : 0 < count) :
    MemWritable s (stackPtr s - BitVec.ofNat 64 back) count := by
  obtain ⟨hs, he⟩ := stack_subrange_bounds h hback
  exact memWritable_of_region h.1 h.2.1 ht hs (by omega) hp hpos

theorem stack_slot_writable {s : RamState} {budget back : Nat}
    (h : Stack.Valid s budget) (hback : back ≤ budget) (halign : back % 8 = 0)
    (ht : (Stack.region s budget).Avoids (fun address => pageTables.Contains address.toNat)) :
    MemWritable s (stackPtr s - BitVec.ofNat 64 back) 8 := by
  apply stack_memoryWritable h hback (by omega) ht _ (by decide)
  have hno : back ≤ (stackPtr s).toNat := Nat.le_trans hback h.2.2.1
  have hsmall : back < 2^64 := Nat.lt_of_le_of_lt hno (stackPtr s).isLt
  have hsub : (stackPtr s - BitVec.ofNat 64 back).toNat = (stackPtr s).toNat - back := by
    rw [BitVec.toNat_sub_of_le (by
      simp only [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsmall]
      exact hno), BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsmall]
  rw [hsub]
  have hsp : (stackPtr s).toNat % 16 = 8 := h.2.2.2
  omega

theorem stack_avoids_program {s : RamState} {input : ByteArray} {capacity writtenLength : Nat} {lengthWritten : Prop}
    (h : MemorySeparation base16ctUpperEncodeStr s input capacity writtenLength lengthWritten) :
    (Stack.region s 160).Avoids InProgram := by
  intro address ha hp
  exact h.2.1 _ (by simp [base16ctUpperEncodeStr, Extracted.upper_encode_strStackBytes]) address ha (.inl hp)

theorem stack_avoids_pageTables {s : RamState} {input : ByteArray} {capacity writtenLength : Nat} {lengthWritten : Prop}
    (h : MemorySeparation base16ctUpperEncodeStr s input capacity writtenLength lengthWritten) :
    (Stack.region s 160).Avoids (fun address => pageTables.Contains address.toNat) := by
  intro address ha hp
  exact h.2.1 _ (by simp [base16ctUpperEncodeStr, Extracted.upper_encode_strStackBytes]) address ha (.inr hp)

theorem rangeApart_of_disjoint {a b : MemoryRegion} (ha : a.Bounded) (hb : b.Bounded)
    (hd : a.Disjoint b) :
    RangeApart (BitVec.ofNat 64 a.start) a.size (BitVec.ofNat 64 b.start) b.size := by
  intro i hi j hj he
  have hca := contains_of_mem_covers ha ⟨i, hi, rfl⟩
  have hcb := contains_of_mem_covers hb ⟨j, hj, he⟩
  exact hd _ hca hcb

theorem memWritable_of_agrees {s t : RamState} {cs : List Component}
    {addr : BitVec 64} {count : Nat} (hw : MemWritable s addr count)
    (h : AgreesExcept cs s t) : MemWritable t addr count :=
  ⟨hw.low, fun i hi => h.grow _ (hw.mem i hi), hw.tables⟩

theorem memReadable_of_agrees {s t : RamState} {cs : List Component}
    {addr : BitVec 64} {count : Nat} (hr : MemReadable s addr count)
    (h : AgreesExcept cs s t) : MemReadable t addr count :=
  ⟨hr.low, fun i hi => h.grow _ (hr.mem i hi)⟩

theorem rangeApart_of_disjoint_subranges {a b : MemoryRegion}
    {addr other : BitVec 64} {count len : Nat}
    (ha : a.Bounded) (hb : b.Bounded) (hd : a.Disjoint b)
    (has : a.start ≤ addr.toNat) (hae : addr.toNat + count ≤ a.start + a.size)
    (hbs : b.start ≤ other.toNat) (hbe : other.toNat + len ≤ b.start + b.size) :
    RangeApart addr count other len := by
  intro i hi j hj he
  have hca := contains_offset_of_subrange ha has hae i hi
  have hcb := contains_offset_of_subrange hb hbs hbe j hj
  rw [he] at hca
  exact hd _ hca hcb

theorem rangeApart_text_of_avoids {region : MemoryRegion} {addr : BitVec 64}
    {count offset len : Nat} (hb : region.Bounded) (hav : region.Avoids InProgram)
    (hs : region.start ≤ addr.toNat) (he : addr.toNat + count ≤ region.start + region.size)
    (hcode : offset + len ≤ Extracted.textBytes.size) :
    RangeApart addr count (Extracted.textAddress + BitVec.ofNat 64 offset) len := by
  intro i hi j hj heq
  apply hav _ (contains_offset_of_subrange hb hs he i hi)
  rw [heq, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact text_address_in_program _ (by omega)

theorem output_byte_writable {s : RamState} {routine : Routine}
    {input : ByteArray} {capacity offset writtenLength : Nat} {lengthWritten : Prop}
    (ho : ValidOutput s capacity) (hsep : MemorySeparation routine s input capacity writtenLength lengthWritten)
    (hoff : offset < capacity) :
    MemWritable s (s.regValue .rcx + BitVec.ofNat 64 offset) 1 := by
  have hlo : (s.regValue .rcx).toNat + capacity < 2^32 := ho.2.1
  have hoff64 : offset < 2^64 := by omega
  have hsum : (s.regValue .rcx).toNat + offset < 2^64 := by omega
  have haddr : (s.regValue .rcx + BitVec.ofNat 64 offset).toNat =
      (s.regValue .rcx).toNat + offset := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff64,
      Nat.mod_eq_of_lt hsum]
  apply memWritable_of_region ho.2.1 ho.2.2
  · intro address ha hp
    exact hsep.2.1 _ (by simp) address ha (.inr hp)
  · change (s.regValue .rcx).toNat ≤ _
    rw [haddr]
    omega
  · change _ ≤ (s.regValue .rcx).toNat + capacity
    rw [haddr]
    omega
  · omega
  · decide

def encoderComponents (initial : RamState) (capacity : Nat) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11,
   .flags, .rip, .mem (initial.regValue .rcx) capacity,
   .mem (stackPtr initial - 32) 32]

theorem encoder_memoryWriteFrame {s t : RamState} {capacity : Nat}
    (h : AgreesExcept (encoderComponents s capacity) s t)
    (ho : (outputRegion s capacity).Bounded) (hs : Stack.Valid s 32) :
    MemoryWriteFrame s t #v[outputRegion s capacity, Stack.region s 32] := by
  apply h.memoryWriteFrame
  intro c hc address hcover
  simp only [encoderComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;> try exact False.elim hcover
  · refine ⟨outputRegion s capacity, by simp, ?_⟩
    apply contains_of_mem_covers ho
    simpa only [outputRegion, registerRegion, BitVec.ofNat_toNat, BitVec.setWidth_eq] using hcover
  · obtain ⟨i, hi, rfl⟩ := hcover
    obtain ⟨hstart, hend⟩ := stack_subrange_bounds hs (used := 32) (by decide)
    refine ⟨Stack.region s 32, by simp, ?_⟩
    exact contains_offset_of_subrange hs.1 hstart (by omega) i hi

theorem stack_scratch_return_apart {s : RamState} {budget : Nat}
    (h : Stack.Valid s budget) :
    RangeApart (stackPtr s - BitVec.ofNat 64 budget) budget (stackPtr s) 8 := by
  have hn : budget ≤ (stackPtr s).toNat := h.2.2.1
  have hb : budget < 2^64 := Nat.lt_of_le_of_lt hn (stackPtr s).isLt
  have hsub : (stackPtr s - BitVec.ofNat 64 budget).toNat = (stackPtr s).toNat - budget := by
    rw [BitVec.toNat_sub_of_le (by
      simpa only [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb] using hn),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
  have hr := (stack_return_readable h).low
  apply RangeApart.of_toNat
  · rw [hsub]
    have := (stackPtr s).isLt
    omega
  · omega
  · left
    rw [hsub]
    omega

theorem encoder_returnSlot_bytes {s t : RamState} {capacity : Nat}
    (h : AgreesExcept (encoderComponents s capacity) s t)
    (ho : (outputRegion s capacity).Bounded) (hs : Stack.Valid s 32)
    (hd : (outputRegion s capacity).Disjoint (Stack.region s 32)) :
    ∀ i < 8, t.external[stackPtr s + BitVec.ofNat 64 i]? =
      s.external[stackPtr s + BitVec.ofNat 64 i]? := by
  intro i hi
  apply h.byte
  intro c hc hcover
  simp only [encoderComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;> try exact False.elim hcover
  · have ho' : (outputRegion s capacity).Contains
        (stackPtr s + BitVec.ofNat 64 i).toNat := by
      apply contains_of_mem_covers ho
      simpa only [outputRegion, registerRegion, BitVec.ofNat_toNat, BitVec.setWidth_eq] using hcover
    obtain ⟨hstart, hend⟩ := stack_subrange_bounds hs (used := 0) (by decide)
    simp only [BitVec.sub_zero, Nat.zero_add] at hstart hend
    exact hd _ ho' (contains_offset_of_subrange hs.1 hstart hend i hi)
  · obtain ⟨j, hj, he⟩ := hcover
    exact stack_scratch_return_apart hs j hj i hi he.symm

theorem encoder_returnSlot_read {s t : RamState} {capacity : Nat}
    (h : AgreesExcept (encoderComponents s capacity) s t)
    (ho : (outputRegion s capacity).Bounded) (hs : Stack.Valid s 32)
    (hd : (outputRegion s capacity).Disjoint (Stack.region s 32)) :
    (Operand.mem (stackPtr s) : Operand 64).read t =
      (Operand.mem (stackPtr s) : Operand 64).read s := by
  apply memLoad_congr
  intro i hi
  change (t.external[stackPtr s + BitVec.ofNat 64 i]?).getD 0 =
    (s.external[stackPtr s + BitVec.ofNat 64 i]?).getD 0
  rw [encoder_returnSlot_bytes h ho hs hd i hi]

theorem encoder_calleeSaved {s t : RamState} {capacity : Nat}
    (h : AgreesExcept (encoderComponents s capacity) s t)
    (hrbx : t.regValue .rbx = s.regValue .rbx) : CalleeSavedRegistersUnchanged s t := by
  intro register hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hrbx
  · exact h.read (n := 64) (r := 5) (by simp [encoderComponents])
  · exact h.read (n := 64) (r := 12) (by simp [encoderComponents])
  · exact h.read (n := 64) (r := 13) (by simp [encoderComponents])
  · exact h.read (n := 64) (r := 14) (by simp [encoderComponents])
  · exact h.read (n := 64) (r := 15) (by simp [encoderComponents])

end Base16ct.Proofs.EncodeStr.Upper
