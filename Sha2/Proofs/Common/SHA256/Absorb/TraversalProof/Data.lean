import Sha2.Proofs.Common.SHA256.Absorb.TraversalProof.Geometry
import Sha2.Proofs.Common.SHA256.Absorb.DirectProof.Memory

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb.Table

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

variable {l : Layout} {initial s t : RamState} {n reserve : Nat}
  {regions : Vector MemoryRegion n} {inputs : Array Input}

theorem slots_of_frame [Bindings] (wf : WellFormed l reserve)
    (stack : Stack.Valid initial reserve) (state : ExecutionState initial s regions)
    (frame : MemoryWriteFrame s t (footprint l (l.chunk.sp initial))) :
    memLoad t.external (l.chunk.sp initial + BitVec.ofNat 64 l.pointerSlot) 64 =
      memLoad s.external (l.chunk.sp initial + BitVec.ofNat 64 l.pointerSlot) 64 ∧
    memLoad t.external (l.chunk.sp initial + BitVec.ofNat 64 l.lengthSlot) 64 =
      memLoad s.external (l.chunk.sp initial + BitVec.ofNat 64 l.lengthSlot) 64 := by
  constructor
  · exact memLoad_of_frame frame
      (stack_frame_readable stack (by have := wf.chunk.capacity; omega) state.allocated wf.pointerFits)
      (slot_apart_footprint wf stack wf.pointerFits wf.pointerActive wf.pointerStored)
  · exact memLoad_of_frame frame
      (stack_frame_readable stack (by have := wf.chunk.capacity; omega) state.allocated wf.lengthFits)
      (slot_apart_footprint wf stack wf.lengthFits wf.lengthActive wf.lengthStored)

theorem CountAt.of_frame [Bindings] (wf : WellFormed l reserve)
    (stack : Stack.Valid initial reserve) (input : CountAt l (l.chunk.sp initial) s)
    (frame : MemoryWriteFrame s t (footprint l (l.chunk.sp initial))) :
    CountAt l (l.chunk.sp initial) t := by
  refine ⟨?_⟩
  intro offset equal
  exact readable_of_frame frame (input.readable offset equal)
    (slot_apart_footprint wf stack (wf.countFits offset equal)
      (wf.countActive offset equal) (wf.countStored offset equal))

theorem table_entry_of_frame {a : BitVec 64} {count index : Nat}
    {k : Nat} {written : Vector MemoryRegion k}
    (frame : MemoryWriteFrame s t written) (readable : MemReadable s a (8 * count))
    (apart : ∀ region ∈ written, (⟨a.toNat, 8 * count⟩ : MemoryRegion).Disjoint region)
    (bound : index < count) :
    memLoad t.external (a + BitVec.ofNat 64 (8 * index)) 64 =
      memLoad s.external (a + BitVec.ofNat 64 (8 * index)) 64 := by
  apply memLoad_congr
  intro i hi
  have byte := frame_byte frame readable apart (i := 8 * index + i) (by omega)
  simp only [BitVec.ofNat_add] at byte
  change (t.external[_]?).getD 0 = (s.external[_]?).getD 0
  rw [BitVec.add_assoc, byte]

theorem InputData.of_frame [Bindings] (wf : WellFormed l reserve)
    (stack : Stack.Valid initial reserve) (state : ExecutionState initial s regions)
    (input : InputData l (l.chunk.sp initial) inputs s)
    (separation : Separation l initial s reserve inputs)
    (frame : MemoryWriteFrame s t (footprint l (l.chunk.sp initial))) :
    InputData l (l.chunk.sp initial) inputs t := by
  have slots := slots_of_frame wf stack state frame
  have pointerApart : ∀ region ∈ footprint l (l.chunk.sp initial),
      (⟨(memLoad s.external (l.chunk.sp initial + BitVec.ofNat 64 l.pointerSlot) 64).toNat,
        8 * inputs.size⟩ : MemoryRegion).Disjoint region := by
    intro region member a ha hb
    exact separation.pointers a ha (footprint_subset_stack wf stack region member a hb)
  have lengthApart : ∀ region ∈ footprint l (l.chunk.sp initial),
      (⟨(memLoad s.external (l.chunk.sp initial + BitVec.ofNat 64 l.lengthSlot) 64).toNat,
        8 * inputs.size⟩ : MemoryRegion).Disjoint region := by
    intro region member a ha hb
    exact separation.lengths a ha (footprint_subset_stack wf stack region member a hb)
  refine ⟨input.sizeBound, input.messageBound, ?_, ?_, ?_, ?_, ?_, input.bounded⟩
  · rw [slots.1]
    exact readable_of_frame frame input.pointersReadable pointerApart
  · rw [slots.2]
    exact readable_of_frame frame input.lengthsReadable lengthApart
  · intro i
    rw [slots.1, table_entry_of_frame frame input.pointersReadable pointerApart i.isLt]
    exact input.pointers i
  · intro i
    rw [slots.2, table_entry_of_frame frame input.lengthsReadable lengthApart i.isLt]
    exact input.lengths i
  · intro i
    exact Common.Memory.hasBytes_of_frame (input.bytes i) (input.bounded i) frame
      (fun region member a ha hb => separation.inputApart i a ha
        (footprint_subset_stack wf stack region member a hb))

theorem Separation.of_frame [Bindings] (wf : WellFormed l reserve)
    (stack : Stack.Valid initial reserve) (state : ExecutionState initial s regions)
    (input : Separation l initial s reserve inputs)
    (frame : MemoryWriteFrame s t (footprint l (l.chunk.sp initial))) :
    Separation l initial t reserve inputs := by
  have slots := slots_of_frame wf stack state frame
  refine ⟨input.inputApart, ?_, ?_⟩
  · rw [slots.1]
    exact input.pointers
  · rw [slots.2]
    exact input.lengths

theorem count_of_chunk [Bindings] {prior : ByteArray} {input : Input}
    (wf : WellFormed l reserve) (stack : Stack.Valid initial reserve)
    (count : CountAt l (l.chunk.sp initial) s)
    (finished : Absorb.Finished l.chunk initial s t regions prior input) :
    l.count.read (l.chunk.sp initial) t = l.count.read (l.chunk.sp initial) s := by
  cases shape : l.count with
  | reg r =>
    simp only [Count.read]
    exact finished.frame.registers _ (by
      simp only [BitVec.toNat_setWidth]
      have bound := r.isLt
      omega) (wf.countRegister r shape).1
  | stack offset =>
    simp only [Count.read]
    exact memLoad_of_frame (chunk_frame finished.frame.memory)
      (count.readable offset shape)
      (slot_apart_footprint wf stack (wf.countFits offset shape)
        (wf.countActive offset shape) (wf.countStored offset shape))

end Sha2.Proofs.Common.SHA256.Absorb.Table
