import Md5.Proofs.Streaming.Update

namespace Md5.Proofs.Streaming

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Buffered

def storageOffsets (frame outputSlot pointerSlot lengthSlot : Nat) : List Nat :=
  [outputSlot, pointerSlot, lengthSlot, frame + 48] ++
    (List.range 6).map (fun i ↦ frame + 8 * i)

theorem storage_of_reads {frame context outputSlot pointerSlot lengthSlot budget : Nat}
    {outputRegister : Syntax.Reg} {initial s t : RamState}
    (h : PrologueStorage frame context outputSlot pointerSlot lengthSlot budget
      outputRegister initial s)
    (hsp : stackPtr t = stackPtr s)
    (hr : ∀ offset ∈ storageOffsets frame outputSlot pointerSlot lengthSlot,
      (Operand.mem (stackPtr t + BitVec.ofNat 64 offset) : Operand 64).read t =
        (Operand.mem (stackPtr s + BitVec.ofNat 64 offset) : Operand 64).read s) :
    PrologueStorage frame context outputSlot pointerSlot lengthSlot budget
      outputRegister initial t := by
  refine ⟨hsp.trans h.rsp, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hr _ (by
      apply List.mem_append_right
      exact List.mem_map.mpr ⟨i.val, List.mem_range.mpr i.isLt, rfl⟩)]
    exact h.saved i
  · rw [hr _ (by simp [storageOffsets])]
    exact h.output
  · rw [hr _ (by simp [storageOffsets])]
    exact h.pointer
  · rw [hr _ (by simp [storageOffsets])]
    exact h.length
  · rw [hr _ (by simp [storageOffsets])]
    exact h.returnSlot

theorem loopStorage_offset_gap {kind : LoopKind.Kind} {offset : Nat}
    (ho : offset ∈ storageOffsets (LoopKind.frame kind) (LoopKind.outputOffset kind)
      (LoopKind.pointerOffset kind).toNat (LoopKind.lengthOffset kind).toNat) :
    (offset + 8 ≤ kind.contextOffset ∨ kind.contextOffset + 88 ≤ offset) ∧
      offset + 8 ≤ LoopKind.frame kind + 56 := by
  simp only [storageOffsets, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_map, List.mem_range] at ho
  rcases ho with (rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩
  all_goals cases kind <;>
    simp only [LoopKind.frame, LoopKind.outputOffset, LoopKind.pointerOffset,
      LoopKind.lengthOffset, UpdateKind.contextOffset, BitVec.reduceToNat] <;> omega

theorem update_stackRead [Bindings] {kind : LoopKind.Kind} {boundary : ReturnBoundary}
    {initial s t : RamState} {message input : ByteArray}
    (h : LoopKind.storage kind initial s) (hs : Stack.Valid initial (LoopKind.budget kind))
    (hp : UpdatePre kind boundary message input s) (hu : UpdatePost kind boundary message input s t)
    (offset : Nat) (ho : offset + 8 ≤ LoopKind.frame kind + 56)
    (hgap : offset + 8 ≤ kind.contextOffset ∨ kind.contextOffset + 88 ≤ offset) :
    (Operand.mem (stackPtr t + BitVec.ofNat 64 offset) : Operand 64).read t =
      (Operand.mem (stackPtr s + BitVec.ofNat 64 offset) : Operand 64).read s := by
  rw [hu.rsp]
  have hb := loopStorage_bounds h hs
  have hn := loopStorage_address h hs (offset := offset) (by omega)
  apply memoryRead_of_memoryWriteFrame
    (region := ⟨(stackPtr s).toNat + offset, 8⟩)
    (hu.frame hp.scratchBounded hp.contextBounded)
  · change (stackPtr s).toNat + offset + 8 < userAddressLimit
    omega
  · rw [hn]
    exact Nat.le_refl _
  · rw [hn]
    exact Nat.le_refl _
  · intro region hr address ha hc
    simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    change (stackPtr s).toNat + offset ≤ address ∧
      address < (stackPtr s).toNat + offset + 8 at ha
    rcases hr with rfl | rfl
    · change (stackPtr s).toNat - 320 ≤ address ∧
        address < (stackPtr s).toNat - 320 + 320 at hc
      omega
    · change (kind.context s).toNat ≤ address ∧
        address < (kind.context s).toNat + 88 at hc
      rw [loopStorage_context_address h hs] at hc
      omega

theorem loopStorage_update [Bindings] {kind : LoopKind.Kind} {boundary : ReturnBoundary}
    {initial s t : RamState} {message input : ByteArray}
    (h : LoopKind.storage kind initial s) (hs : Stack.Valid initial (LoopKind.budget kind))
    (hp : UpdatePre kind boundary message input s) (hu : UpdatePost kind boundary message input s t) :
    LoopKind.storage kind initial t := by
  apply storage_of_reads h hu.rsp
  intro offset ho
  exact update_stackRead h hs hp hu offset (loopStorage_offset_gap ho).2
    (loopStorage_offset_gap ho).1

theorem loopUpdate_stackFrame [Bindings] {kind : LoopKind.Kind} {boundary : ReturnBoundary}
    {initial s t : RamState} {message input : ByteArray}
    (h : LoopKind.storage kind initial s) (hs : Stack.Valid initial (LoopKind.budget kind))
    (hp : UpdatePre kind boundary message input s) (hu : UpdatePost kind boundary message input s t) :
    MemoryWriteFrame s t #v[Stack.region initial (LoopKind.budget kind)] := by
  intro address hout
  apply hu.frame hp.scratchBounded hp.contextBounded address
  intro region hr hin
  apply hout (Stack.region initial (LoopKind.budget kind)) (by simp)
  simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl
  · exact loopStorage_scratch_contains h hs hin
  · exact loopStorage_context_contains h hs hin


theorem loopUpdate_frame [Bindings] {kind : LoopKind.Kind} {boundary : ReturnBoundary}
    {initial s t : RamState} {message input : ByteArray}
    (h : LoopKind.storage kind initial s) (hs : Stack.Valid initial (LoopKind.budget kind))
    (hp : UpdatePre kind boundary message input s) (hu : UpdatePost kind boundary message input s t) :
    MemoryWriteFrame s t (LoopKind.writable kind initial) := by
  intro a ha
  apply loopUpdate_stackFrame h hs hp hu a
  intro r hr
  simp only [Vector.mem_mk, Array.mem_singleton] at hr
  subst r
  exact ha _ (LoopKind.stack_mem_writable kind initial)

end Md5.Proofs.Streaming
