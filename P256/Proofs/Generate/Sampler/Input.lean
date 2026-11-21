import P256.Proofs.Generate.Sampler.Memory

set_option autoImplicit false

namespace P256.Proofs.Generate.Sampler

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

variable [Bindings] {s t : RamState} {boundary : ReturnBoundary} {input : ByteArray}

omit [Bindings] in
theorem chunk_size {offset : Nat} (available : offset+32 ≤ input.size) :
    (input.extract offset (offset+32)).size = 32 := by
  simp only [ByteArray.size_extract,Nat.min_eq_left available]
  omega

theorem source_offset (pre : Pre s boundary input) {offset : Nat} (bound : offset ≤ input.size) :
    (source s+BitVec.ofNat 64 offset).toNat = (source s).toNat+offset := by
  have low : (source s).toNat+input.size < 2^32 := pre.bounded
  rw [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : offset < 2^64),
    Nat.mod_eq_of_lt (by omega)]

theorem State.chunk_bytes (pre : Pre s boundary input) (state : State s t)
    {offset : Nat} (available : offset+32 ≤ input.size) :
    (MemoryRegion.mk (source s+BitVec.ofNat 64 offset).toNat 32).HasBytes
      t.external (input.extract offset (offset+32)) := by
  refine ⟨chunk_size available,?_⟩
  intro i
  have hi : i.val < 32 := by simpa only [chunk_size available] using i.isLt
  have h := (state.input_bytes pre).2 ⟨offset+i.val,by omega⟩
  change t.external[BitVec.ofNat 64 ((source s+BitVec.ofNat 64 offset).toNat+i.val)]? = _
  rw [source_offset pre (by omega)]
  simpa only [inputRegion,ByteArray.getElem_extract,Nat.add_assoc] using h

theorem State.chunk_readable (pre : Pre s boundary input) (state : State s t)
    {offset : Nat} (available : offset+32 ≤ input.size) :
    MemReadable t (source s+BitVec.ofNat 64 offset) 32 := by
  apply readable_of_grow (memoryRegion_memReadable pre.bounded pre.allocatedInput ?_ ?_) state.allocated
  · rw [source_offset pre (by omega)]
    change (source s).toNat ≤ (source s).toNat+offset
    omega
  · rw [source_offset pre (by omega)]
    change (source s).toNat+offset+32 ≤ (source s).toNat+input.size
    omega

theorem State.chunk_stack_apart (pre : Pre s boundary input) (state : State s t)
    {offset stackOffset len : Nat} (available : offset+32 ≤ input.size)
    (bound : stackOffset+len ≤ 264) :
    RangeApart (stackPtr t+BitVec.ofNat 64 stackOffset) len
      (source s+BitVec.ofNat 64 offset) 32 := by
  intro i hi j hj eq
  have stk := ScalarFrame.stack_contains pre.toCalleePre (offset := 264-stackOffset)
    (len := len) (a := stackPtr t+BitVec.ofNat 64 stackOffset+BitVec.ofNat 64 i)
    (by omega) (by omega) (by
      rw [ScalarFrame.scalar_stack_address (frameOffset := 264) state.rsp (by decide) (by omega)]
      exact ⟨i,hi,rfl⟩)
  have inp := memoryRegion_contains_add pre.bounded (len := 32)
    (addr := source s+BitVec.ofNat 64 offset) (by
      rw [source_offset pre (by omega)]
      change (source s).toNat ≤ (source s).toNat+offset
      omega) (by
      rw [source_offset pre (by omega)]
      change (source s).toNat+offset+32 ≤ (source s).toNat+input.size
      omega) hj
  rw [eq] at stk
  exact pre.separateInput _ (by simp [writes]) _ inp stk

theorem State.descriptor_writable (pre : Pre s boundary input) (state : State s t)
    {offset : Nat} (bound : offset+8 ≤ 16) :
    P256.Proofs.Common.Der.Memory.MemWritable t (s.regValue .rsi+BitVec.ofNat 64 offset) 8 := by
  have low : (s.regValue .rsi).toNat+16 < 2^32 := pre.inputBounded
  have addr : (s.regValue .rsi+BitVec.ofNat 64 offset).toNat = (s.regValue .rsi).toNat+offset := by
    rw [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : offset < 2^64),
      Nat.mod_eq_of_lt (by omega)]
  apply P256.Proofs.Common.Der.Memory.MemWritable.of_region pre.inputBounded
  · intro a ha
    exact Option.isSome_iff_exists.mp (state.allocated a (Option.isSome_iff_exists.mpr (pre.inputAllocated a ha)))
  · intro a ha tables
    exact pre.descriptorAvoids a ha (.inr tables)
  · rw [addr]
    change (s.regValue .rsi).toNat ≤ (s.regValue .rsi).toNat+offset
    omega
  · rw [addr]
    change (s.regValue .rsi).toNat+offset+8 ≤ (s.regValue .rsi).toNat+16
    omega

theorem descriptor_code (pre : Pre s boundary input) {codeOffset codeLen : Nat}
    (bound : codeOffset+codeLen ≤ 118431) :
    RangeApart (s.regValue .rsi) 16
      (Extracted.textAddress+BitVec.ofNat 64 codeOffset) codeLen := by
  intro i hi j hj eq
  apply pre.descriptorAvoids (s.regValue .rsi+BitVec.ofNat 64 i)
    (memoryRegion_contains_add pre.inputBounded (Nat.le_refl _) (Nat.le_refl _) hi)
  apply Or.inl
  rw [eq,BitVec.add_assoc,←BitVec.ofNat_add]
  exact inProgram_of_textOffset (codeOffset+j) (by omega)

end P256.Proofs.Generate.Sampler
