import Base16ct.Proofs.EncodeStr.Lower.Machine.Loop.Body
import Base16ct.Proofs.EncodeStr.Lower.Machine.Loop.Tail
import Base16ct.Proofs.EncodeStr.Lower.Machine.Loop.Prefix

namespace Base16ct.Proofs.EncodeStr.Lower

open Base16ct.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def loopIterationChanges (initial : RamState) (index : Nat) : List Component :=
  .reg 8 :: loopBodyChanges initial index

private theorem loop_changes_cover (initial : RamState) (index : Nat) (address : BitVec 64) :
    (∃ c ∈ loopIterationChanges initial index, c.Covers address) ↔
      address = initial.regValue .rcx + BitVec.ofNat 64 (2 * index) ∨
      address = initial.regValue .rcx + BitVec.ofNat 64 (2 * index + 1) := by
  simp [loopIterationChanges, loopBodyChanges, Component.Covers, Nat.lt_one_iff]

private theorem loop_changes_stack {initial : RamState} {input : List UInt8}
    {capacity index offset len : Nat}
    (call : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    (hi : 2 * index + 2 ≤ capacity) (hoff : offset ≤ 32) (hlen : len ≤ offset + 8) :
    ∀ j < len, ∀ c ∈ loopIterationChanges initial index,
      ¬ c.Covers (stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 j) := by
  intro j hj c hc covers
  rcases (loop_changes_cover initial index _).mp ⟨c, hc, covers⟩ with eq | eq
  · have apart := output_stack_apart call (offset := 2 * index) (len := 1)
      (by omega) hoff hlen 0 (by decide) j hj
    apply apart
    simpa using eq.symm
  · have apart := output_stack_apart call (offset := 2 * index + 1) (len := 1)
      (by omega) hoff hlen 0 (by decide) j hj
    apply apart
    simpa using eq.symm

theorem loop_iteration [Bindings] {initial s : RamState} {input : List UInt8}
    {capacity index : Nat} (call : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    (outside : ¬ InProgram (returnBoundary initial).rip)
    (capacityFits : 2 * input.length ≤ capacity)
    (h : LoopInvariant initial input capacity index s) (hi : index < input.length) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧
      LoopInvariant initial input capacity (index + 1) t := by
  obtain ⟨bodyFuel, u, runBody, readyU, ripU, frameBody, highU, lowU⟩ :=
    loop_body call outside capacityFits h hi
  have avoids : ∀ c ∈ loopIterationChanges initial index, ∀ a b,
      (a, b) ∈ Extracted.programImage → ¬ c.Covers a := by
    intro c hc a b hab covers
    rcases (loop_changes_cover initial index a).mp ⟨c, hc, covers⟩ with eq | eq
    · apply output_avoids_program call (offset := 2 * index) (len := 1)
        (by omega) 0 (by decide)
      simpa only [BitVec.add_zero, ← eq] using (show InProgram a from ⟨b, hab⟩)
    · apply output_avoids_program call (offset := 2 * index + 1) (len := 1)
        (by omega) 0 (by decide)
      simpa only [BitVec.add_zero, ← eq] using (show InProgram a from ⟨b, hab⟩)
  have bodyCode : CodeIn Extracted.programImage u :=
    CodeIn.of_agreesExcept frameBody
      (fun pair hp c hc ↦ avoids c (List.mem_cons_of_mem _ hc) pair.1 pair.2 hp) h.code
  have lengthBound : input.length < 2 ^ 64 := by
    have bound : (initial.regValue .rdi).toNat + input.length < 2 ^ 32 := by simpa only [inputRegion, registerRegion, MemoryRegion.Bounded, userAddressLimit, List.size_toByteArray] using call.inputInMemory.2.1
    omega
  obtain ⟨t, runTail, readyT, ripT, indexT, frameTail⟩ :=
    loop_tail outside readyU bodyCode ripU hi lengthBound
      ((frameBody.read (by simp [loopBodyChanges])).trans h.indexValue)
      ((frameBody.read (by simp [loopBodyChanges])).trans h.inputLength)
  have frame : AgreesExcept (loopIterationChanges initial index) s t :=
    (frameBody.trans frameTail).mono (by simp [loopIterationChanges, loopBodyChanges])
  have written_le : (if 2 * input.length ≤ capacity then 2 * input.length else 0) ≤ capacity := by split <;> omega
  have machineT : MachineInvariant initial (if 2 * input.length ≤ capacity then 2 * input.length else 0) t := by
    apply h.toMachineInvariant.of_agreesExcept frame readyT
      (hd := by simp [loopIterationChanges, loopBodyChanges])
    · simp [PreservesCalleeSaved, loopIterationChanges, loopBodyChanges]
    · intro c hc address covers
      rcases (loop_changes_cover initial index address).mp ⟨c, hc, covers⟩ with eq | eq
      · exact ⟨outputRegion initial (if 2 * input.length ≤ capacity then 2 * input.length else 0), by simp [writableRegions],
          output_memory_contains_written call written_le (offset := 2 * index) (len := 1) (by simp only [ite_eq_left capacityFits]; omega)
            ⟨0, by decide, by simpa using eq⟩⟩
      · exact ⟨outputRegion initial (if 2 * input.length ≤ capacity then 2 * input.length else 0), by simp [writableRegions],
          output_memory_contains_written call written_le (offset := 2 * index + 1) (len := 1) (by simp only [ite_eq_left capacityFits]; omega)
            ⟨0, by decide, by simpa using eq⟩⟩
    · exact avoids
    · simpa only [BitVec.sub_zero] using
        loop_changes_stack call (index := index) (by omega) (offset := 0) (len := 8)
          (by decide) (by decide)
  have tailMemory : t.external = u.external := frameTail.external (by simp [Component.Covers])
  have highT :
      (Operand.mem (initial.regValue .rcx + BitVec.ofNat 64 (2 * index)) : Operand 8).read t =
        lowerHighDigit input[index] := by
    simpa only [Operand.read, tailMemory] using highU
  have lowT :
      (Operand.mem (initial.regValue .rcx + BitVec.ofNat 64 (2 * index + 1)) : Operand 8).read t =
        lowerLowDigit input[index] := by
    simpa only [Operand.read, tailMemory] using lowU
  have outT : readOutput initial t (2 * (index + 1)) =
      .ok (encodedBytes (input.take (index + 1))).toByteArray := by
    apply encoded_prefix_extend hi h.output
    · intro a hhigh hlow
      apply frame.byte
      intro c hc covers
      rcases (loop_changes_cover initial index a).mp ⟨c, hc, covers⟩ with eq | eq
      · exact hhigh eq
      · apply hlow
        simpa only [BitVec.ofNat_eq_ofNat, BitVec.ofNat_add, BitVec.add_assoc] using eq
    · apply byte_lookup_of_operand_read (highT.trans (lowerHighDigit_character _))
      have allocated := (output_byte_writable call h.toMachineInvariant
        (by omega : 2 * index < capacity)).mem 0 (by decide)
      apply frame.grow
      simpa only [BitVec.add_zero] using allocated
    · have lowLookup := byte_lookup_of_operand_read (lowT.trans (lowerLowDigit_character _))
        (frame.grow _ (by
          have allocated := (output_byte_writable call h.toMachineInvariant
            (by omega : 2 * index + 1 < capacity)).mem 0 (by decide)
          simpa only [BitVec.add_zero] using allocated))
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.ofNat_add, BitVec.add_assoc] using lowLookup
    · have bound : (initial.regValue .rcx).toNat + capacity < 2 ^ 32 := call.outputInMemory.2.1
      omega
  refine ⟨bodyFuel + 3, t, runBody.trans runTail,
    { toMachineInvariant := machineT
      rip := ripT
      rsp := ?_
      resultPointer := ?_
      inputPointer := ?_
      inputLength := ?_
      outputPointer := ?_
      outputLength := ?_
      indexValue := indexT
      innerReturn := ?_
      output := outT
      savedRbx := ?_
      lengthPointer := ?_ }⟩
  · exact (frame.read (r := 4) (n := 64)
      (by simp [loopIterationChanges, loopBodyChanges])).trans h.rsp
  · exact (frame.read (by simp [loopIterationChanges, loopBodyChanges])).trans h.resultPointer
  · exact (frame.read (by simp [loopIterationChanges, loopBodyChanges])).trans h.inputPointer
  · exact (frame.read (by simp [loopIterationChanges, loopBodyChanges])).trans h.inputLength
  · exact (frame.read (by simp [loopIterationChanges, loopBodyChanges])).trans h.outputPointer
  · exact (frame.read (by simp [loopIterationChanges, loopBodyChanges])).trans h.outputLength
  · apply Eq.trans (read_mem_of_agreesExcept frame _ 64 ?_) h.innerReturn
    exact loop_changes_stack call (index := index) (by omega)
      (offset := 32) (len := 8) (by decide) (by decide)
  · apply Eq.trans (read_mem_of_agreesExcept frame _ 64 ?_) h.savedRbx
    exact loop_changes_stack call (index := index) (by omega)
      (offset := 8) (len := 8) (by decide) (by decide)
  · exact (frame.read (by simp [loopIterationChanges, loopBodyChanges])).trans h.lengthPointer

theorem loop_complete [Bindings] {initial s : RamState} {input : List UInt8}
    {capacity index : Nat} (call : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    (outside : ¬ InProgram (returnBoundary initial).rip)
    (capacityFits : 2 * input.length ≤ capacity)
    (h : LoopInvariant initial input capacity index s) (bound : index ≤ input.length) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧
      LoopInvariant initial input capacity input.length t := by
  have complete : ∀ remaining index s, index + remaining = input.length →
      LoopInvariant initial input capacity index s →
      ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧
        LoopInvariant initial input capacity input.length t := by
    intro remaining
    induction remaining with
    | zero =>
      intro index s heq h
      have he : index = input.length := by omega
      subst index
      exact ⟨0, s, (advances_zero _ _ _).mpr rfl, h⟩
    | succ remaining ih =>
      intro index s heq h
      obtain ⟨fuel, t, run, ht⟩ := loop_iteration call outside capacityFits h (by omega)
      obtain ⟨fuel', u, run', hu⟩ := ih (index + 1) t (by omega) ht
      exact ⟨fuel + fuel', u, run.trans run', hu⟩
  exact complete (input.length - index) index s (by omega) h

end Base16ct.Proofs.EncodeStr.Lower
