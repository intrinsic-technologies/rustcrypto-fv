import P256.Spec
import P256.Proofs.Program.WrapperInput

set_option autoImplicit false

namespace P256.Proofs.ProjectiveWrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem call_slice_count [Bindings] {s : RamState} {point other : ByteArray}
    {slices : Array Input} (h : ValidCallWithSlices projectivePointAdd s [point, other] slices) :
    slices.size = 2 := by
  have he := congrArg Array.size h.slicesHoldInputs
  simpa only [inputBytes, Array.size_map, List.size_toArray, List.length_cons,
    List.length_nil] using he

theorem call_input_count [Bindings] {s : RamState} {point other : ByteArray}
    {slices : Array Input} (h : ValidCallWithSlices projectivePointAdd s [point, other] slices) :
    s.regValue .rsi = 2 := by
  apply BitVec.eq_of_toNat_eq
  exact h.countArgumentMatchesInputs

theorem preserved_input_at [Bindings] {routine : Routine} {s t : RamState}
    {inputs : List ByteArray} {slices : Array Input}
    (h : ValidCallWithSlices routine s inputs slices)
    (frame : MemoryWriteFrame s t (wrapperRegions routine s)) (i : Fin slices.size) :
    (slices[i].region).HasBytes t.external slices[i].bytes ∧
      MemReadable t (s.regValue .rdi + BitVec.ofNat 64 (8 * i.val)) 8 ∧
      MemReadable t (s.regValue .rdx + BitVec.ofNat 64 (8 * i.val)) 8 ∧
      memLoad t.external (s.regValue .rdi + BitVec.ofNat 64 (8 * i.val)) 64 =
        slices[i].address ∧
      memLoad t.external (s.regValue .rdx + BitVec.ofNat 64 (8 * i.val)) 64 =
        BitVec.ofNat 64 slices[i].bytes.size := by
  have ri : slices[i].region ∈ readRegions s slices := by
    simp only [readRegions, List.mem_cons]
    right; right
    simpa using (Array.mem_map.mpr ⟨slices[i], Array.getElem_mem i.isLt, rfl⟩ :
      slices[i].region ∈ slices.map Input.region)
  have table {reg : Syntax.Reg}
      (hb : (registerRegion s reg (8 * slices.size)).Bounded)
      (hr : registerRegion s reg (8 * slices.size) ∈ readRegions s slices)
      (readable : MemReadable s (s.regValue reg + BitVec.ofNat 64 (8 * i.val)) 8) :
      MemReadable t (s.regValue reg + BitVec.ofNat 64 (8 * i.val)) 8 ∧
        memLoad t.external (s.regValue reg + BitVec.ofNat 64 (8 * i.val)) 64 =
        memLoad s.external (s.regValue reg + BitVec.ofNat 64 (8 * i.val)) 64 := by
    have bound : (s.regValue reg).toNat + 8 * slices.size < 2^32 := hb
    have addr : (s.regValue reg + BitVec.ofNat 64 (8 * i.val)).toNat =
        (s.regValue reg).toNat + 8 * i.val := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    have low : (registerRegion s reg (8 * slices.size)).start ≤
        (s.regValue reg + BitVec.ofNat 64 (8 * i.val)).toNat := by
      rw [addr]
      exact Nat.le_add_right _ _
    have high : (s.regValue reg + BitVec.ofNat 64 (8 * i.val)).toNat + 64 / 8 ≤
        (registerRegion s reg (8 * slices.size)).start +
          (registerRegion s reg (8 * slices.size)).size := by
      rw [addr]
      change (s.regValue reg).toNat + 8 * i.val + 8 ≤ (s.regValue reg).toNat + 8 * slices.size
      omega
    refine ⟨⟨readable.low, ?_⟩,
      frame_memLoad frame (wrapper_read_disjoint h hr) hb low high⟩
    intro j hj
    rw [frame_read frame (wrapper_read_disjoint h hr)
      (memoryRegion_contains_add hb low high hj)]
    exact readable.mem j hj
  obtain ⟨ptrReadable, ptr⟩ := table h.inputsInMemory.pointerTableValid.2
    (by simp [readRegions, pointerTable]) (input_pointer_memReadable h.inputsInMemory i)
  obtain ⟨lenReadable, len⟩ := table h.inputsInMemory.lengthTableValid.2
    (by simp [readRegions, lengthTable]) (input_length_memReadable h.inputsInMemory i)
  exact ⟨frame_hasBytes frame (wrapper_read_disjoint h ri)
    (h.inputsInMemory.slicesValid i).2.2.2.1 (h.inputsInMemory.slicesValid i).2.2.2.2,
    ptrReadable, lenReadable, ptr.trans (input_pointer_memLoad h.inputsInMemory i),
    len.trans (input_length_memLoad h.inputsInMemory i)⟩

end P256.Proofs.ProjectiveWrapper
