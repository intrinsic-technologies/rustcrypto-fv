import Base16ct.Proofs.EncodeStr.Upper.Callee.State

namespace Base16ct.Proofs.EncodeStr.Upper

open Base16ct.Spec.Program Prelude X86 X86.Machine X86Proofs

theorem RunInvariant.input_bytes [Bindings] (c : CallContext) {s : RamState}
    (h : RunInvariant c s) :
    Bytes s.external (c.initial.regValue .rdi) c.input.length (fun i => c.input.getD i 0) := by
  intro i hi
  have hin : (inputRegion c.initial c.input.toByteArray).Contains
      (c.initial.regValue .rdi + BitVec.ofNat 64 i).toNat :=
    contains_offset_of_subrange c.valid.inputInMemory.2.1 (Nat.le_refl _) (Nat.le_refl _) i (by simpa only [inputRegion, registerRegion, List.size_toByteArray] using hi)
  have hframe := encoder_memoryWriteFrame h.agrees (show (outputRegion c.initial c.writeLength).Bounded from by
    have hb := c.valid.outputInMemory.2.1
    have := c.writeLength_le_capacity
    change (c.initial.regValue .rcx).toNat + c.writeLength < userAddressLimit
    change (c.initial.regValue .rcx).toNat + c.capacity < userAddressLimit at hb
    omega) c.stack32
  rw [hframe _ ?_]
  · have hb := c.valid.inputInMemory.2.2.2 ⟨i, by simpa using hi⟩
    simpa only [inputRegion, registerRegion, BitVec.ofNat_add, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, List.getElem_toByteArray, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi, Option.getD_some] using hb
  · intro region hr hcontains
    have hr' : region = outputRegion c.initial c.writeLength ∨
        region = Stack.region c.initial 32 := by simpa using hr
    rcases hr' with rfl | rfl
    · apply c.valid.separation.1 0 1 (by decide) _ hin
      have := c.writeLength_le_capacity
      change (outputRegion c.initial c.capacity).Contains _
      simp only [MemoryRegion.Contains, outputRegion, registerRegion] at hcontains ⊢
      omega
    · apply c.valid.separation.1 0 2 (by decide) _ hin
      change (Stack.region c.initial 160).Contains _
      simp only [MemoryRegion.Contains, Stack.region] at hcontains ⊢
      omega

theorem RunInvariant.stack_writable [Bindings] (c : CallContext) {s : RamState}
    (h : RunInvariant c s) (back : Nat) (hb : back ≤ 32) (halign : back % 8 = 0) :
    MemWritable s (stackPtr c.initial - BitVec.ofNat 64 back) 8 :=
  memWritable_of_agrees
    (stack_slot_writable c.valid.stack (by omega : back ≤ 160) halign (stack_avoids_pageTables c.valid.separation))
    h.agrees

theorem RunInvariant.stack_readable [Bindings] (c : CallContext) {s : RamState}
    (h : RunInvariant c s) (back count : Nat) (hb : back ≤ 32) (hc : count ≤ back + 8) :
    MemReadable s (stackPtr c.initial - BitVec.ofNat 64 back) count := by
  have hs : Stack.Valid c.initial 32 := c.stack32
  obtain ⟨hstart, hend⟩ := stack_subrange_bounds hs hb
  have hbound : (Stack.region c.initial 32).start + (Stack.region c.initial 32).size <
      userAddressLimit := c.stack32.1
  exact memReadable_of_agrees
    (memReadable_of_allocated hs.2.1 (by omega) hstart (by omega)) h.agrees

theorem RunInvariant.output_byte_writable [Bindings] (c : CallContext) {s : RamState}
    (h : RunInvariant c s) (offset : Nat) (hoff : offset < c.capacity) :
    MemWritable s (c.initial.regValue .rcx + BitVec.ofNat 64 offset) 1 :=
  memWritable_of_agrees
    (Base16ct.Proofs.EncodeStr.Upper.output_byte_writable
      c.valid.outputInMemory c.valid.separation hoff) h.agrees

theorem output_rangeApart_text (c : CallContext) (outputOffset offset len : Nat)
    (hout : outputOffset < c.capacity) (hcode : offset + len ≤ Extracted.textBytes.size) :
    RangeApart (c.initial.regValue .rcx + BitVec.ofNat 64 outputOffset) 1
      (Extracted.textAddress + BitVec.ofNat 64 offset) len := by
  have hbound : (c.initial.regValue .rcx).toNat + c.capacity < 2^32 := c.valid.outputInMemory.2.1
  have hoff64 : outputOffset < 2^64 := by omega
  have hsum : (c.initial.regValue .rcx).toNat + outputOffset < 2^64 := by omega
  have haddr : (c.initial.regValue .rcx + BitVec.ofNat 64 outputOffset).toNat =
      (c.initial.regValue .rcx).toNat + outputOffset := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff64,
      Nat.mod_eq_of_lt hsum]
  apply rangeApart_text_of_avoids c.valid.outputInMemory.2.1 ?_ ?_ ?_ hcode
  · intro address ha hp
    exact c.valid.separation.2.1 _ (by simp) address ha (.inl hp)
  · change (c.initial.regValue .rcx).toNat ≤ _
    rw [haddr]
    omega
  · change _ ≤ (c.initial.regValue .rcx).toNat + c.capacity
    rw [haddr]
    omega

theorem RunInvariant.input_byte_readable [Bindings] (c : CallContext) {s : RamState}
    (h : RunInvariant c s) (offset : Nat) (hoff : offset < c.input.length) :
    MemReadable s (c.initial.regValue .rdi + BitVec.ofNat 64 offset) 1 := by
  apply ((h.input_bytes c).sub offset 1 (by omega)).readable
  have hbound : (c.initial.regValue .rdi).toNat + c.input.length < 2^32 :=
    by simpa only [inputRegion, registerRegion, MemoryRegion.Bounded, userAddressLimit,
      List.size_toByteArray] using c.valid.inputInMemory.2.1
  have hoff64 : offset < 2^64 := by omega
  have hsum : (c.initial.regValue .rdi).toNat + offset < 2^64 := by omega
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff64,
    Nat.mod_eq_of_lt hsum]
  omega

theorem readOutput_of_bytes (c : CallContext) {s : RamState}
    (h : Bytes s.external (c.initial.regValue .rcx) (2 * c.input.length)
      (fun j => (encodedBytes c.input).getD j 0)) :
    readOutput c.initial s c.encoded.length = .ok c.encoded.toByteArray := by
  have he : c.encoded = encodedBytes c.input := encode_eq_encodedBytes c.input
  have hb : Bytes s.external (c.initial.regValue .rcx) c.encoded.length
      (fun j => c.encoded.getD j 0) := by
    simpa only [he, encodedBytes_length] using h
  let read (j : Nat) : Except Fault UInt8 :=
    match s.external[BitVec.ofNat 64 ((c.initial.regValue .rcx).toNat + j)]? with
    | some byte => .ok byte
    | none => .error (.unmappedMemory
        (BitVec.ofNat 64 ((c.initial.regValue .rcx).toNat + j)))
  have hr (j : Nat) (hj : j < c.encoded.length) : read j = .ok (c.encoded.getD j 0) := by
    simp only [read, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, hb j hj]
  have hm (indices : List Nat) (hi : ∀ j ∈ indices, j < c.encoded.length) :
      indices.mapM read = .ok (indices.map (fun j => c.encoded.getD j 0)) := by
    induction indices with
    | nil => rfl
    | cons j indices ih =>
      simp only [List.mapM_cons, List.map_cons, hr j (hi j (by simp)),
        ih (fun k hk => hi k (by simp [hk]))]
      rfl
  have hv : (List.range c.encoded.length).map (fun j => c.encoded.getD j 0) =
      c.encoded := by
    apply List.ext_getElem (by simp)
    intro i hi hi'
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
  change ((List.range c.encoded.length).mapM read >>= fun bytes => pure (ByteArray.mk bytes.toArray)) = .ok c.encoded.toByteArray
  rw [hm _ (fun j hj => List.mem_range.mp hj), hv]
  change Except.ok (ByteArray.mk c.encoded.toArray) = Except.ok c.encoded.toByteArray
  congr 1
  exact ByteArray.ext List.data_toByteArray.symm

end Base16ct.Proofs.EncodeStr.Upper
