import Md5.Proofs.Streaming.Loop
import Md5.Proofs.Buffered.Finalize.Geometry

namespace Md5.Proofs.Streaming

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Buffered

def LoopKind.finalizer : LoopKind.Kind → Finalize.Kind
  | .slices => .slices
  | .updateFinalizeInto => .updateFinalizeInto
  | .finalizeResetFirst | .finalizeResetSecond => .finalizeResetSecond
  | .resetDiscardFirst | .resetDiscardSecond => .resetDiscardSecond
  | .resetFirst | .resetSecond => .resetSecond

theorem finalize_stack_contains {kind : LoopKind.Kind} {initial s : RamState}
    (h : LoopKind.storage kind initial s) (hs : Stack.Valid initial (LoopKind.budget kind))
    {address : Nat} (ha : ((LoopKind.finalizer kind).stackRegion s).Contains address) :
    (Stack.region initial (LoopKind.budget kind)).Contains address := by
  have hsize : (LoopKind.finalizer kind).stackBytes ≤ LoopKind.frame kind + 56 := by
    cases kind <;> decide +kernel
  rw [loopStorage_region h hs]
  change (stackPtr s).toNat - 320 ≤ address ∧
    address < (stackPtr s).toNat - 320 + (LoopKind.frame kind + 376)
  change (stackPtr s).toNat - 320 ≤ address ∧
    address < (stackPtr s).toNat - 320 + (320 + (LoopKind.finalizer kind).stackBytes) at ha
  constructor <;> omega

theorem streaming_finalize_pre [bindings : Bindings] {kind : LoopKind.Kind}
    {boundary : ReturnBoundary} {initial s : RamState} {message : ByteArray}
    (h : StreamingState kind initial message s) (hk : kind ≠ .resetFirst)
    (hStack : Stack.Valid initial (LoopKind.budget kind))
    (hAvoid : (Stack.region initial (LoopKind.budget kind)).Avoids
      (fun address ↦ InProgram address ∨ InPageTables address))
    (hStride : UnitStringStride bindings) (hOutside : ¬ InProgram boundary.rip)
    (hRip : s.RIP = LoopKind.finalPC kind) (hSize : message.size < 2^64)
    (hkFinalize : kind ≠ .finalizeResetFirst := by decide)
    (hkDiscard : kind ≠ .resetDiscardFirst := by decide) :
    Finalize.Pre (LoopKind.finalizer kind) boundary message s := by
  have hb := loopStorage_bounds h.storage hStack
  have hsz : (LoopKind.finalizer kind).stackBytes ≤ LoopKind.frame kind + 56 := by
    cases kind <;> decide +kernel
  refine {
    stackLow := hb.1
    stackHigh := by omega
    stackAligned := loopStorage_aligned h.storage hStack
    stackAllocated := ?_
    stackAvoids := ?_
    ready := h.ready
    code := h.code
    stride := hStride
    df := h.df
    rip := ?_
    boundaryOutside := hOutside
    absorbed := ?_
    messageBounded := hSize
    digestState := ?_
  }
  · intro a ha
    exact Option.isSome_iff_exists.mp (h.grows a (Option.isSome_iff_exists.mpr
      (hStack.2.1 a (finalize_stack_contains h.storage hStack ha))))
  · exact fun a ha ↦ hAvoid a (finalize_stack_contains h.storage hStack ha)
  · cases kind with
    | resetFirst => exact (hk rfl).elim
    | finalizeResetFirst => exact (hkFinalize rfl).elim
    | resetDiscardFirst => exact (hkDiscard rfl).elim
    | updateFinalizeInto | finalizeResetSecond | resetDiscardSecond => exact hRip
    | slices => exact hRip
    | resetSecond => exact hRip
  · cases kind <;> exact h.absorbed
  · cases kind <;> intro hh <;> cases hh

theorem storageOffset_finalizer_gap {kind : LoopKind.Kind} {offset : Nat}
    (ho : offset ∈ storageOffsets (LoopKind.frame kind) (LoopKind.outputOffset kind)
      (LoopKind.pointerOffset kind).toNat (LoopKind.lengthOffset kind).toNat) :
    match kind with
    | .slices | .updateFinalizeInto => 168 ≤ offset
    | .resetDiscardFirst | .resetDiscardSecond => offset + 8 ≤ 120 ∨ 288 ≤ offset
    | .resetFirst | .resetSecond | .finalizeResetFirst | .finalizeResetSecond =>
      (offset + 8 ≤ 96 ∨ 184 ≤ offset) ∧ (offset + 8 ≤ 216 ∨ 296 ≤ offset) := by
  simp only [storageOffsets, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_map, List.mem_range] at ho
  rcases ho with (rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩
  all_goals cases kind <;>
    simp only [LoopKind.frame, LoopKind.outputOffset, LoopKind.pointerOffset,
      LoopKind.lengthOffset, BitVec.reduceToNat] <;> omega

theorem finalize_storage [Bindings] {kind : LoopKind.Kind} {boundary : ReturnBoundary}
    {initial s t : RamState} {message : ByteArray}
    (h : LoopKind.storage kind initial s) (hs : Stack.Valid initial (LoopKind.budget kind))
    (hu : Finalize.Post (LoopKind.finalizer kind) boundary message s t) :
    LoopKind.storage kind initial t := by
  apply storage_of_reads h hu.rsp
  intro offset ho
  rw [hu.rsp]
  have hoff := (loopStorage_offset_gap ho).2
  have hgap := storageOffset_finalizer_gap ho
  have hb := loopStorage_bounds h hs
  apply memLoad_congr
  intro i hi
  have hi' : i < 8 := hi
  have haddr : (stackPtr s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat =
      (stackPtr s).toNat + offset + i := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, loopStorage_address h hs (by omega)]
    omega
  change (t.external[stackPtr s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0 =
    (s.external[stackPtr s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0
  rw [hu.agrees.byte]
  intro c hc hcover
  have hlow : ¬ Component.Covers (.mem (stackPtr s - 320) 320)
      (stackPtr s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i) := by
    intro hh
    have hn : BitVec.ofNat 64 ((stackPtr s).toNat - 320) = stackPtr s - 320 := by
      have hn' : (stackPtr s - 320).toNat = (stackPtr s).toNat - 320 := by
        rw [BitVec.toNat_sub_of_le]
        · rfl
        · exact hb.1
      rw [← hn', BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have hreg : (⟨(stackPtr s).toNat - 320, 320⟩ : MemoryRegion).Bounded := by
      change (stackPtr s).toNat - 320 + 320 < userAddressLimit
      omega
    have hc' := Block.contains_of_mem_covers hreg (by simpa only [hn] using hh)
    change (stackPtr s).toNat - 320 ≤ _ ∧
      (stackPtr s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat <
        (stackPtr s).toNat - 320 + 320 at hc'
    rw [haddr] at hc'
    omega
  have hlocal (start len : Nat) (hbound : start + len ≤ LoopKind.frame kind + 56)
      (hapart : offset + 8 ≤ start ∨ start + len ≤ offset) :
      ¬ Component.Covers (.mem (stackPtr s + BitVec.ofNat 64 start) len)
        (stackPtr s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i) := by
    intro hh
    have hreg : (⟨(stackPtr s).toNat + start, len⟩ : MemoryRegion).Bounded := by
      change (stackPtr s).toNat + start + len < userAddressLimit
      omega
    have hc' := Block.contains_of_mem_covers hreg (by
      simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using hh)
    change (stackPtr s).toNat + start ≤ _ ∧
      (stackPtr s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat <
        (stackPtr s).toNat + start + len at hc'
    rw [haddr] at hc'
    omega
  simp only [Finalize.Kind.changes, List.mem_append] at hc
  rcases hc with (hc | hc) | hc
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact hcover.elim | exact hlow hcover
  · obtain ⟨r, _, rfl⟩ := List.mem_map.mp hc
    exact hcover.elim
  · cases kind with
    | slices | updateFinalizeInto =>
      simp only [LoopKind.finalizer, Finalize.Kind.localChanges, List.mem_singleton] at hc
      subst c
      exact hlocal 0 168 (by decide +kernel) (Or.inr hgap)
        (by simpa only [BitVec.add_zero] using hcover)
    | resetFirst | finalizeResetFirst | finalizeResetSecond =>
      simp only [LoopKind.finalizer, Finalize.Kind.localChanges, List.mem_cons,
        List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact hlocal 96 88 (by decide +kernel) hgap.1 hcover
      · exact hlocal 216 80 (by decide +kernel) hgap.2 hcover
    | resetSecond =>
      simp only [LoopKind.finalizer, Finalize.Kind.localChanges, List.mem_cons,
        List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact hlocal 96 88 (by decide +kernel) hgap.1 hcover
      · exact hlocal 216 80 (by decide +kernel) hgap.2 hcover
    | resetDiscardFirst | resetDiscardSecond =>
      simp only [LoopKind.finalizer, Finalize.Kind.localChanges, List.mem_singleton] at hc
      subst c
      exact hlocal 120 168 (by decide +kernel) hgap hcover


theorem finalize_stack_frame [Bindings] {kind : LoopKind.Kind} {boundary : ReturnBoundary}
    {initial s t : RamState} {message : ByteArray}
    (h : LoopKind.storage kind initial s) (hs : Stack.Valid initial (LoopKind.budget kind))
    (hp : Finalize.Pre (LoopKind.finalizer kind) boundary message s)
    (hu : Finalize.Post (LoopKind.finalizer kind) boundary message s t) :
    MemoryWriteFrame s t #v[Stack.region initial (LoopKind.budget kind)] := by
  intro a ha
  apply hu.frame hp.toStorage a
  intro r hr hin
  simp only [Vector.mem_mk, Array.mem_singleton] at hr
  subst r
  exact ha (Stack.region initial (LoopKind.budget kind)) (by simp)
    (finalize_stack_contains h hs hin)


theorem finalize_loop_frame [Bindings] {kind : LoopKind.Kind} {boundary : ReturnBoundary}
    {initial s t : RamState} {message : ByteArray}
    (h : LoopKind.storage kind initial s) (hs : Stack.Valid initial (LoopKind.budget kind))
    (hp : Finalize.Pre (LoopKind.finalizer kind) boundary message s)
    (hu : Finalize.Post (LoopKind.finalizer kind) boundary message s t) :
    MemoryWriteFrame s t (LoopKind.writable kind initial) := by
  intro a ha
  apply finalize_stack_frame h hs hp hu a
  intro r hr
  simp only [Vector.mem_mk, Array.mem_singleton] at hr
  subst r
  exact ha _ (LoopKind.stack_mem_writable kind initial)

end Md5.Proofs.Streaming
