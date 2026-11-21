import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Positive.Interface
import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Setup.Stack
import Base16ct.Proofs.Copied.Md5.Proofs.Block.Preconditions
import Base16ct.Proofs.Copied.Md5.Proofs.Streaming.Slices
namespace Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine

open Base16ct.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem validReturnAddress_boundary {s : RamState} (h : ValidReturnAddress s) :
    (returnBoundary s).rip.toNat < userAddressLimit ∧ ¬ InProgram (returnBoundary s).rip := by
  obtain ⟨address, hword, hlow, hout⟩ := h
  have hread := Base16ct.Proofs.Copied.Md5.Proofs.Streaming.word64At_memLoad hword
  have heq : (returnBoundary s).rip = address := by
    change memLoad s.external (stackPtr s) 64 = address
    simpa only [Stack.returnSlot, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      show s.regValue .rsp = stackPtr s from rfl] using hread
  rw [heq]
  exact ⟨hlow, hout⟩

theorem validCall_nearReturnBoundary [bindings : Bindings]
    {s : RamState} {input : ByteArray} {lengthWritten : Prop} {capacity : Nat}
    (h : ValidCall base16ctMixedDecode s input capacity (input.size / 2) lengthWritten)
    (hReady : ReadyToStep s) :
    Prelude.nearReturn64Boundary s = .ok (returnBoundary s) :=
  nearReturn64Boundary_eq s hReady.dataReady hReady.cpu.ss
    (Base16ct.Proofs.Copied.Md5.Proofs.stack_return_readable h.stack)

theorem validInput_readable {s : RamState} {input : ByteArray} (h : ValidInput s input) :
    MemReadable s (s.regValue .rdi) input.size := by
  apply Base16ct.Proofs.Copied.Md5.Proofs.memReadable_of_allocated (Base16ct.Proofs.Copied.Md5.Proofs.Block.allocated_of_hasBytes h.2.2)
  · have hb : (s.regValue .rdi).toNat + input.size < userAddressLimit := h.2.1
    omega
  · exact Nat.le_refl _
  · exact Nat.le_refl _

theorem validCall_length_arguments {s : RamState} {input : ByteArray} {lengthWritten : Prop} {capacity : Nat}
    (h : ValidCall base16ctMixedDecode s input capacity (input.size / 2) lengthWritten) :
    s.regValue .rsi = BitVec.ofNat 64 input.size ∧
      s.regValue .r8 = BitVec.ofNat 64 capacity := by
  have hl : (s.regValue .rsi).toNat = input.size := h.lengthArgumentMatchesInput
  have hc : (s.regValue .r8).toNat = capacity := h.capacityArgumentMatchesOutput
  simp [← hl, ← hc]

theorem validCall_input_output_apart {s : RamState} {input : ByteArray} {lengthWritten : Prop} {capacity : Nat}
    (h : ValidCall base16ctMixedDecode s input capacity (input.size / 2) lengthWritten) :
    RangeApart (s.regValue .rdi) input.size (s.regValue .rcx) capacity := by
  have hd : (inputRegion s input).Disjoint (outputRegion s capacity) :=
    h.separation.1 0 1 (by decide +kernel)
  simpa only [inputRegion, outputRegion, registerRegion, BitVec.ofNat_toNat,
    BitVec.setWidth_eq] using
    Base16ct.Proofs.Copied.Md5.Proofs.Block.rangeApart_of_disjoint h.inputInMemory.2.1 h.outputInMemory.2.1 hd

theorem validCall_stack_region {s : RamState} {input : ByteArray} {lengthWritten : Prop}
    {capacity used : Nat} (h : ValidCall base16ctMixedDecode s input capacity (input.size / 2) lengthWritten)
    (hused : used ≤ base16ctMixedDecode.minStackBytes) :
    BitVec.ofNat 64 (Stack.region s used).start = stackPtr s - BitVec.ofNat 64 used ∧
      (Stack.region s used).size = used + 8 := by
  have hn : used ≤ (stackPtr s).toNat := Nat.le_trans hused h.stack.2.2.1
  have hu : used < 2^64 := Nat.lt_of_le_of_lt hn (stackPtr s).isLt
  have hsub : (stackPtr s - BitVec.ofNat 64 used).toNat = (stackPtr s).toNat - used := by
    rw [BitVec.toNat_sub_of_le (by
      simpa only [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu] using hn),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu]
  constructor
  · change BitVec.ofNat 64 ((stackPtr s).toNat - used) = stackPtr s - BitVec.ofNat 64 used
    rw [← hsub, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · change (stackPtr s).toNat + 8 - ((stackPtr s).toNat - used) = used + 8
    omega

theorem validCall_input_stack_apart {s : RamState} {input : ByteArray} {lengthWritten : Prop}
    {capacity used : Nat} (h : ValidCall base16ctMixedDecode s input capacity (input.size / 2) lengthWritten)
    (hused : used ≤ base16ctMixedDecode.minStackBytes) :
    RangeApart (s.regValue .rdi) input.size
      (stackPtr s - BitVec.ofNat 64 used) (used + 8) := by
  obtain ⟨hs, he⟩ := Base16ct.Proofs.Copied.Md5.Proofs.Block.stack_subrange_bounds h.stack hused
  intro i hi j hj heq
  have hin := region_offset_contains h.inputInMemory.2.1 hi
  have hstack := Base16ct.Proofs.Copied.Md5.Proofs.Block.contains_offset_of_subrange h.stack.1 hs he j hj
  apply h.separation.1 0 2 (by decide +kernel)
    (s.regValue .rdi + BitVec.ofNat 64 i).toNat
  · change (inputRegion s input).Contains _
    simpa only [inputRegion, registerRegion, BitVec.ofNat_toNat, BitVec.setWidth_eq] using hin
  · rw [heq]
    exact hstack

theorem validCall_output_stack_apart {s : RamState} {input : ByteArray} {lengthWritten : Prop}
    {capacity used : Nat} (h : ValidCall base16ctMixedDecode s input capacity (input.size / 2) lengthWritten)
    (hused : used ≤ base16ctMixedDecode.minStackBytes) :
    RangeApart (s.regValue .rcx) capacity
      (stackPtr s - BitVec.ofNat 64 used) (used + 8) := by
  obtain ⟨hs, he⟩ := Base16ct.Proofs.Copied.Md5.Proofs.Block.stack_subrange_bounds h.stack hused
  intro i hi j hj heq
  have hout := region_offset_contains h.outputInMemory.2.1 hi
  have hstack := Base16ct.Proofs.Copied.Md5.Proofs.Block.contains_offset_of_subrange h.stack.1 hs he j hj
  apply h.separation.1 1 2 (by decide +kernel)
    (s.regValue .rcx + BitVec.ofNat 64 i).toNat
  · change (outputRegion s capacity).Contains _
    simpa only [outputRegion, registerRegion, BitVec.ofNat_toNat, BitVec.setWidth_eq] using hout
  · rw [heq]
    exact hstack

theorem validCall_output_return_apart {s : RamState} {input : ByteArray} {lengthWritten : Prop} {capacity : Nat}
    (h : ValidCall base16ctMixedDecode s input capacity (input.size / 2) lengthWritten) :
    RangeApart (s.regValue .rcx) capacity (stackPtr s) 8 := by
  intro i hi j hj he
  apply validCall_output_stack_apart h (used := 8) (by decide +kernel) i hi (8 + j) (by omega)
  simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, ← BitVec.add_assoc,
    BitVec.sub_add_cancel] using he

theorem validCall_return_bytes_of_agrees {s t : RamState} {input : ByteArray} {lengthWritten : Prop}
    {capacity : Nat} {changes : List Component}
    (h : ValidCall base16ctMixedDecode s input capacity (input.size / 2) lengthWritten) (hFrame : AgreesExcept changes s t)
    (hCover : ∀ address c, c ∈ changes → c.Covers address →
      (Component.mem (s.regValue .rcx) capacity).Covers address ∨
        (Component.mem (stackPtr s - 8) 8).Covers address) :
    ∀ i < 8, t.external[stackPtr s + BitVec.ofNat 64 i]? =
      s.external[stackPtr s + BitVec.ofNat 64 i]? := by
  intro i hi
  apply hFrame.byte
  intro c hc hcov
  rcases hCover _ c hc hcov with hout | hpush
  · obtain ⟨j, hj, he⟩ := hout
    exact validCall_output_return_apart h j hj i hi he.symm
  · obtain ⟨j, hj, he⟩ := hpush
    have ha := RangeApart.offsets (stackPtr s - 8) (a := 0) (b := 8)
      (len := 8) (count := 8) (by decide +kernel) (by decide +kernel)
      (.inl (by decide +kernel))
    apply ha j hj i hi
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.sub_add_cancel] using he.symm

theorem validCall_return_memLoad_of_agrees {s t : RamState} {input : ByteArray} {lengthWritten : Prop}
    {capacity : Nat} {changes : List Component}
    (h : ValidCall base16ctMixedDecode s input capacity (input.size / 2) lengthWritten) (hFrame : AgreesExcept changes s t)
    (hCover : ∀ address c, c ∈ changes → c.Covers address →
      (Component.mem (s.regValue .rcx) capacity).Covers address ∨
        (Component.mem (stackPtr s - 8) 8).Covers address) :
    memLoad t.external (stackPtr s) 64 = (returnBoundary s).rip := by
  change memLoad t.external (stackPtr s) 64 = memLoad s.external (stackPtr s) 64
  apply memLoad_congr
  intro i hi
  exact congrArg (fun byte : Option UInt8 ↦ byte.getD 0)
    (validCall_return_bytes_of_agrees h hFrame hCover i hi)

theorem validCall_return_readable_of_agrees {s t : RamState} {input : ByteArray} {lengthWritten : Prop}
    {capacity : Nat} {changes : List Component}
    (h : ValidCall base16ctMixedDecode s input capacity (input.size / 2) lengthWritten) (hFrame : AgreesExcept changes s t)
    (hCover : ∀ address c, c ∈ changes → c.Covers address →
      (Component.mem (s.regValue .rcx) capacity).Covers address ∨
        (Component.mem (stackPtr s - 8) 8).Covers address) :
    MemReadable t (stackPtr s) 8 := by
  have hr := Base16ct.Proofs.Copied.Md5.Proofs.stack_return_readable h.stack
  refine ⟨hr.low, ?_⟩
  intro i hi
  rw [validCall_return_bytes_of_agrees h hFrame hCover i hi]
  exact hr.mem i hi

theorem mixed_internal_call {s : RamState} {input : ByteArray}
    {capacity : Nat} {lengthWritten : Prop}
    (h : ValidCall base16ctMixedDecode s input capacity (input.size / 2) lengthWritten)
    (hLength : input.data.toList.length / 2 ≤ capacity →
      (∃ output, mixedDecodeList input.data.toList = some output) → lengthWritten) :
    MixedInternalCall s input.data.toList capacity (returnBoundary s) := by
  have havoid := h.separation.2.1 (Stack.region s base16ctMixedDecode.minStackBytes)
    (by simp)
  have hstack := Base16ct.Proofs.Copied.Md5.Proofs.Block.stack_memoryWritable h.stack (used := 24)
    (by decide +kernel) (fun a ha ht ↦ havoid a ha (.inr (pageTables_contains_of_md5 ht)))
  have hscontains (i : Nat) (hi : i < 32) :
      (Stack.region s base16ctMixedDecode.minStackBytes).Contains
        (stackPtr s - 24 + BitVec.ofNat 64 i).toNat := by
    obtain ⟨hs, he⟩ := Base16ct.Proofs.Copied.Md5.Proofs.Block.stack_subrange_bounds h.stack
      (used := 24) (by decide +kernel)
    exact Base16ct.Proofs.Copied.Md5.Proofs.Block.contains_offset_of_subrange h.stack.1 hs he i hi
  have hlcontains (hfit : input.data.toList.length / 2 ≤ capacity)
      (hsome : ∃ output, mixedDecodeList input.data.toList = some output) (i : Nat) (hi : i < 8) :
      (lengthOutputRegion s).Contains (s.regValue .rdx + BitVec.ofNat 64 i).toNat := by
    simpa only [lengthOutputRegion, registerRegion, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      region_offset_contains (h.lengthOutputInMemoryIfLengthWritten (hLength hfit hsome)).1 hi
  have hlstack (hfit : input.data.toList.length / 2 ≤ capacity)
      (hsome : ∃ output, mixedDecodeList input.data.toList = some output) : RangeApart (s.regValue .rdx) 8
      (stackPtr s - 24) 32 := by
    intro i hi j hj heq
    apply (h.separation.2.2 (hLength hfit hsome)).1 0 2 (by decide +kernel)
      _ (hlcontains hfit hsome i hi)
    rw [heq]
    exact hscontains j hj
  refine {
    rip := h.entry
    length := by simpa only [Array.length_toList, ← ByteArray.size_data] using h.lengthArgumentMatchesInput
    capacityArgument := h.capacityArgumentMatchesOutput
    inputBound := by
      have hb := h.inputInMemory.2.1
      change (s.regValue .rdi).toNat + input.size < userAddressLimit at hb
      simp only [Array.length_toList]
      change input.size < 2^64
      unfold userAddressLimit at hb
      omega
    source := by simpa only [Array.length_toList, ← ByteArray.size_data] using validInput_readable h.inputInMemory
    bytes := by
      intro j hj
      have hb := h.inputInMemory.2.2.2 ⟨j, by simpa using hj⟩
      simpa only [inputRegion, registerRegion, BitVec.ofNat_add, BitVec.ofNat_toNat,
        BitVec.setWidth_eq, Array.getElem_toList, ByteArray.getElem_eq_getElem_data] using hb
    output := validCall_output_writable h
    outputNonzero := by
      intro hz
      exact h.outputInMemory.1 (congrArg BitVec.toNat hz)
    stackAligned := by
      have ha := h.stack.2.2.2
      change (stackPtr s).toNat % 16 = 8 at ha
      omega
    result := by
      intro hfit hsome
      have hl := h.lengthOutputInMemoryIfLengthWritten (hLength hfit hsome)
      have hav := (h.separation.2.2 (hLength hfit hsome)).2
      simpa only [lengthOutputRegion, registerRegion, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
        writable_of_region hl.1 hl.2 (fun a ha ht ↦ hav a ha (.inr ht))
    stack := ⟨by
      have hb : (stackPtr s - 24).toNat + 32 ≤ 2^32 := hstack.low
      omega,
      fun i hi ↦ hstack.bytes i (by omega), fun i hi ↦ hstack.tables i (by omega)⟩
    outputAvoids := validCall_output_avoids h
    resultAvoids := fun hfit hsome i hi hp ↦
      (h.separation.2.2 (hLength hfit hsome)).2 _ (hlcontains hfit hsome i hi) (.inl hp)
    resultReserved := fun hfit hsome i hi hp ↦
      (h.separation.2.2 (hLength hfit hsome)).2 _ (hlcontains hfit hsome i hi) (.inr hp)
    stackReserved := fun i hi hp ↦ havoid _ (hscontains i (by omega)) (.inr hp)
    stackAvoids := fun i hi hp ↦ havoid _ (hscontains i (by omega)) (.inl hp)
    sourceOutput := by simpa only [Array.length_toList, ← ByteArray.size_data] using validCall_input_output_apart h
    sourceStack := by
      intro i hi j hj
      exact validCall_input_stack_apart h (used := 24) (by decide +kernel) i hi j (by omega)
    outputStack := by
      intro i hi j hj
      exact validCall_output_stack_apart h (used := 24) (by decide +kernel) i hi j (by omega)
    resultOutput := by
      intro hfit hsome
      have hl := h.lengthOutputInMemoryIfLengthWritten (hLength hfit hsome)
      have hb : (outputRegion s (input.size / 2)).Bounded := by
        have hb := h.outputInMemory.2.1
        change (s.regValue .rcx).toNat + capacity < userAddressLimit at hb
        change (s.regValue .rcx).toNat + input.size / 2 < userAddressLimit
        simp only [Array.length_toList] at hfit
        change input.size / 2 ≤ capacity at hfit
        omega
      simpa only [lengthOutputRegion, outputRegion, registerRegion,
        BitVec.ofNat_toNat, BitVec.setWidth_eq, Array.length_toList, ← ByteArray.size_data] using
        Base16ct.Proofs.Copied.Md5.Proofs.Block.rangeApart_of_disjoint hl.1 hb
          ((h.separation.2.2 (hLength hfit hsome)).1 0 1 (by decide +kernel))
    resultStack := by
      intro hfit hsome i hi j hj
      exact hlstack hfit hsome i hi j (by omega)
    returnRead := Base16ct.Proofs.Copied.Md5.Proofs.stack_return_readable h.stack
    returnValue := rfl
    returnStack := rfl
    returnLow := (validReturnAddress_boundary h.returnAddress).1
    returnOutside := outsideMixed_of_not_inProgram (validReturnAddress_boundary h.returnAddress).2
    returnOutput := by
      intro i hi j hj heq
      exact validCall_output_return_apart h j hj i hi heq.symm
    returnResult := by
      intro hfit hsome i hi j hj heq
      apply hlstack hfit hsome j hj (24 + i) (by omega)
      simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, ← BitVec.add_assoc,
        BitVec.sub_add_cancel] using heq.symm
    returnStackApart := by
      intro i hi j hj
      simpa [BitVec.sub_eq_add_neg] using
        (show OffsetsApart 0 8 (-24) 24 from by unfold OffsetsApart; decide +kernel).ne
          (stackPtr s) hi hj (by decide +kernel)
  }

end Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine
