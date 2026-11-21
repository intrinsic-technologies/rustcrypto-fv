import Md5.Proofs.Streaming.Transport
import Md5.Proofs.Buffered.FinalizeReset.Frame

namespace Md5.Proofs.Buffered.FinalizeReset.Variant

open Md5.Spec.Program

def loopKind : Variant → Streaming.LoopKind.Kind
  | .saved => .resetFirst
  | .direct => .finalizeResetFirst

def secondLoopKind : Variant → Streaming.LoopKind.Kind
  | .saved => .resetSecond
  | .direct => .finalizeResetSecond

def routine (variant : Variant) : Routine :=
  ⟨(match variant with
    | .saved => TwoMessages.digestSlicesReset.entryAddress
    | .direct => TwoMessages.finalizeIntoResetSlices.entryAddress),
    Streaming.LoopKind.budget variant.loopKind, 32⟩

end Md5.Proofs.Buffered.FinalizeReset.Variant

namespace Md5.Proofs.Streaming

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Buffered

theorem finalizeReset_stackRegion_variant {variant : FinalizeReset.Variant} {initial s : RamState}
    (h : LoopKind.storage variant.loopKind initial s)
    (hs : Stack.Valid initial variant.routine.minStackBytes) :
    FinalizeReset.stackRegion s variant = Stack.region initial variant.routine.minStackBytes := by
  cases variant <;> exact (loopStorage_region h hs).symm

theorem finalizeReset_outputAddress_variant {variant : FinalizeReset.Variant} {initial s : RamState}
    (h : LoopKind.storage variant.loopKind initial s) :
    FinalizeReset.outputAddress s = initial.regValue .r8 := by
  cases variant <;> exact h.output

theorem finalizeReset_output_contains_variant {variant : FinalizeReset.Variant} {initial s : RamState}
    (h : LoopKind.storage variant.loopKind initial s) {address : Nat}
    (ha : (FinalizeReset.outputRegion s).Contains address) :
    ((TwoMessages.outputRegion variant.routine) initial).Contains address := by
  change (FinalizeReset.outputAddress s).toNat ≤ address ∧
    address < (FinalizeReset.outputAddress s).toNat + 16 at ha
  rw [finalizeReset_outputAddress_variant h] at ha
  change (initial.regValue .r8).toNat ≤ address ∧
    address < (initial.regValue .r8).toNat + 32
  omega

theorem streaming_finalizeReset_storage_variant {variant : FinalizeReset.Variant} [bindings : Bindings] {initial s : RamState}
    {message : ByteArray} {inputs : Array Slices.Input} {first : Nat}
    (h : StreamingState variant.loopKind initial message s)
    (hCall : (TwoMessages.ValidCall variant.routine) bindings initial inputs first) :
    FinalizeReset.Storage s variant := by
  have hb := loopStorage_bounds h.storage hCall.stackAvailable
  have hregion := finalizeReset_stackRegion_variant h.storage hCall.stackAvailable
  have hstackAvoid := (hCall.separation.2
    (Stack.region initial variant.routine.minStackBytes) (by simp)).2
  have houtAvoid := (hCall.separation.2 ((TwoMessages.outputRegion variant.routine) initial) (by simp)).2
  refine {
    stackLow := hb.1
    stackHigh := by cases variant <;> simpa only [FinalizeReset.Variant.loopKind, LoopKind.frame, FinalizeReset.Variant.stackBytes, Nat.add_assoc] using hb.2
    stackAligned := loopStorage_aligned h.storage hCall.stackAvailable
    stackAllocated := ?_
    stackAvoids := ?_
    outputBounded := ?_
    outputAllocated := ?_
    outputAvoids := ?_
    outputStack := ?_
  }
  · rw [hregion]
    intro a ha
    exact Option.isSome_iff_exists.mp (h.grows a
      (Option.isSome_iff_exists.mpr (hCall.stackAvailable.2.1 a ha)))
  · rw [hregion]
    exact hstackAvoid
  · have hbound := hCall.outputInMemory.2.1
    change (initial.regValue .r8).toNat + 32 < userAddressLimit at hbound
    change (FinalizeReset.outputAddress s).toNat + 16 < userAddressLimit
    rw [finalizeReset_outputAddress_variant h.storage]
    omega
  · intro a ha
    exact Option.isSome_iff_exists.mp (h.grows a
      (Option.isSome_iff_exists.mpr
        (hCall.outputInMemory.2.2 a (finalizeReset_output_contains_variant h.storage ha))))
  · exact fun a ha ↦ houtAvoid a (finalizeReset_output_contains_variant h.storage ha)
  · intro a ha hs
    apply hCall.separation.1 (0 : Fin 2) (1 : Fin 2) (by decide +kernel) a
      (finalizeReset_output_contains_variant h.storage ha)
    rwa [hregion] at hs

private def finalizeResetRegions (s : RamState) : Vector MemoryRegion 5 :=
  #v[FinalizeReset.outputRegion s, ⟨(stackPtr s).toNat - 320, 320⟩,
    ⟨(stackPtr s).toNat + 8, 152⟩, ⟨(stackPtr s).toNat + 232, 16⟩,
    ⟨(stackPtr s).toNat + 296, 16⟩]

private theorem finalizeReset_frame_variant {variant : FinalizeReset.Variant} {s t : RamState} (hs : FinalizeReset.Storage s variant)
    (h : AgreesExcept (FinalizeReset.changes s) s t) :
    MemoryWriteFrame s t (finalizeResetRegions s) := by
  have hsize := variant.stackBytes_bounds
  have hlo := hs.stackLow
  have hhi : (stackPtr s).toNat + variant.stackBytes < 2^32 := hs.stackHigh
  have hlocal (offset len : Nat) (he : offset + len ≤ variant.stackBytes) {address : BitVec 64}
      (hc : Component.Covers (.mem (stackPtr s + BitVec.ofNat 64 offset) len) address) :
      (⟨(stackPtr s).toNat + offset, len⟩ : MemoryRegion).Contains address.toNat := by
    obtain ⟨i, hi, rfl⟩ := hc
    rw [add_ofNat_add_ofNat, FinalizeReset.Export.stackAddress_toNat hs _ (by omega)]
    change (stackPtr s).toNat + offset ≤ _ ∧
      _ < (stackPtr s).toNat + offset + len
    omega
  apply h.memoryWriteFrame
  intro c hc address hcover
  simp only [FinalizeReset.changes, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcover.elim
  · refine ⟨⟨(stackPtr s).toNat - 320, 320⟩, by simp [finalizeResetRegions], ?_⟩
    have hn : BitVec.ofNat 64 ((stackPtr s).toNat - 320) = stackPtr s - 320 := by
      have hn' : (stackPtr s - 320).toNat = (stackPtr s).toNat - 320 :=
        BitVec.toNat_sub_of_le hs.stackLow
      rw [← hn', BitVec.ofNat_toNat, BitVec.setWidth_eq]
    apply Block.contains_of_mem_covers
      (region := ⟨(stackPtr s).toNat - 320, 320⟩)
    · change (stackPtr s).toNat - 320 + 320 < userAddressLimit
      change (stackPtr s).toNat - 320 + 320 < 2^32
      omega
    · simpa only [hn] using hcover
  · exact ⟨⟨(stackPtr s).toNat + 8, 152⟩, by simp [finalizeResetRegions],
      hlocal 8 152 (by cases variant <;> decide +kernel) hcover⟩
  · exact ⟨⟨(stackPtr s).toNat + 232, 16⟩, by simp [finalizeResetRegions],
      hlocal 232 16 (by cases variant <;> decide +kernel) hcover⟩
  · exact ⟨⟨(stackPtr s).toNat + 296, 16⟩, by simp [finalizeResetRegions],
      hlocal 296 16 (by cases variant <;> decide +kernel) hcover⟩
  · exact ⟨FinalizeReset.outputRegion s, by simp [finalizeResetRegions],
      FinalizeReset.Export.output_cover hs (offset := 0) (len := 16) (by decide +kernel)
        (by simpa only [BitVec.add_zero] using hcover)⟩

theorem finalizeReset_stackRead_variant {variant : FinalizeReset.Variant} [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {s t : RamState} (hs : FinalizeReset.Storage s variant)
    (hu : FinalizeReset.Post boundary message s t variant) (offset : Nat)
    (hgap : (160 ≤ offset ∧ offset + 8 ≤ 232) ∨ (312 ≤ offset ∧ offset + 8 ≤ variant.stackBytes)) :
    (Operand.mem (stackPtr t + BitVec.ofNat 64 offset) : Operand 64).read t =
      (Operand.mem (stackPtr s + BitVec.ofNat 64 offset) : Operand 64).read s := by
  rw [hu.rsp]
  have hsize := variant.stackBytes_bounds
  have hlo := hs.stackLow
  have hhi := hs.stackHigh
  have haddr := FinalizeReset.Export.stackAddress_toNat hs offset (by omega)
  apply memoryRead_of_memoryWriteFrame (region := ⟨(stackPtr s).toNat + offset, 8⟩)
    (finalizeReset_frame_variant hs hu.agrees)
  · change (stackPtr s).toNat + offset + 8 < userAddressLimit
    omega
  · rw [haddr]
    exact Nat.le_refl _
  · rw [haddr]
    exact Nat.le_refl _
  · intro region hr address ha hc
    simp only [finalizeResetRegions, Vector.mem_mk, List.mem_toArray, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    change (stackPtr s).toNat + offset ≤ address ∧
      address < (stackPtr s).toNat + offset + 8 at ha
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · apply hs.outputStack address hc
      change (stackPtr s).toNat - 320 ≤ address ∧
        address < (stackPtr s).toNat - 320 + (320 + variant.stackBytes)
      omega
    all_goals simp only [MemoryRegion.Contains] at hc
    all_goals omega

theorem finalizeReset_storage_variant {variant : FinalizeReset.Variant} [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {initial s t : RamState} (h : LoopKind.storage variant.loopKind initial s)
    (hs : FinalizeReset.Storage s variant) (hu : FinalizeReset.Post boundary message s t variant) :
    LoopKind.storage variant.secondLoopKind initial t := by
  have heq : LoopKind.storage variant.secondLoopKind initial t =
      LoopKind.storage variant.loopKind initial t := by cases variant <;> rfl
  rw [heq]
  apply storage_of_reads h hu.rsp
  intro offset ho
  apply finalizeReset_stackRead_variant hs hu offset
  cases variant <;>
    simp only [FinalizeReset.Variant.loopKind, FinalizeReset.Variant.stackBytes,
      storageOffsets, LoopKind.frame, LoopKind.outputOffset, LoopKind.pointerOffset,
      LoopKind.lengthOffset, BitVec.reduceToNat, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, List.mem_map, List.mem_range] at ho ⊢
  all_goals rcases ho with (rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩
  all_goals omega

theorem finalizeReset_total_variant {variant : FinalizeReset.Variant} [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {s t : RamState} (hs : FinalizeReset.Storage s variant)
    (hu : FinalizeReset.Post boundary message s t variant) : stackWord t 192 = stackWord s 192 :=
  finalizeReset_stackRead_variant hs hu 192 (by cases variant <;> decide +kernel)

theorem finalizeReset_loop_frame_variant {variant : FinalizeReset.Variant} [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {initial s t : RamState} (h : LoopKind.storage variant.loopKind initial s)
    (hStack : Stack.Valid initial variant.routine.minStackBytes)
    (hs : FinalizeReset.Storage s variant) (hu : FinalizeReset.Post boundary message s t variant) :
    MemoryWriteFrame s t (LoopKind.writable variant.secondLoopKind initial) := by
  have hsize := variant.stackBytes_bounds
  have hlo := hs.stackLow
  have hregion := finalizeReset_stackRegion_variant h hStack
  have houtMem : (TwoMessages.outputRegion variant.routine initial) ∈
      LoopKind.writable variant.secondLoopKind initial := by
    cases variant with
    | saved => exact Vector.getElem_mem (xs := LoopKind.writable .resetSecond initial) (i := 0) (by decide)
    | direct => exact Vector.getElem_mem (xs := LoopKind.writable .finalizeResetSecond initial) (i := 0) (by decide)
  have hstackMem : Stack.region initial variant.routine.minStackBytes ∈
      LoopKind.writable variant.secondLoopKind initial := by
    cases variant <;> exact LoopKind.stack_mem_writable _ _
  intro address ha
  apply finalizeReset_frame_variant hs hu.agrees address
  intro region hr hin
  simp only [finalizeResetRegions, Vector.mem_mk, List.mem_toArray, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ha ((TwoMessages.outputRegion variant.routine) initial) houtMem (finalizeReset_output_contains_variant h hin)
  all_goals
    apply ha (Stack.region initial variant.routine.minStackBytes) hstackMem
    rw [← hregion]
    change (stackPtr s).toNat - 320 ≤ address.toNat ∧
      address.toNat < (stackPtr s).toNat - 320 + (320 + variant.stackBytes)
    simp only [MemoryRegion.Contains] at hin
    omega

theorem finalizeReset_state_variant {variant : FinalizeReset.Variant} [bindings : Bindings] {boundary : ReturnBoundary}
    {initial s t : RamState} {message : ByteArray} {inputs : Array Slices.Input} {first : Nat}
    (h : StreamingState variant.loopKind initial message s)
    (hCall : (TwoMessages.ValidCall variant.routine) bindings initial inputs first)
    (hu : FinalizeReset.Post boundary message s t variant) :
    StreamingState variant.secondLoopKind initial ByteArray.empty t := by
  have hs := streaming_finalizeReset_storage_variant h hCall
  refine {
    storage := finalizeReset_storage_variant h.storage hs hu
    ready := hu.ready
    code := hu.code
    sse := SupportedSSE.of_agreesExcept hu.agrees h.sse
    df := hu.agrees.directionFlagClear (by simp [FinalizeReset.changes]) h.df
    absorbed := ?_
    grows := fun a ha ↦ hu.agrees.grow a (h.grows a ha)
    memoryFrame := ?_
  }
  · cases variant <;>
      (simp only [FinalizeReset.Variant.secondLoopKind, UpdateKind.context,
        UpdateKind.contextOffset, hu.rsp]
       exact hu.absorbed)
  · intro address ha
    rw [finalizeReset_loop_frame_variant h.storage hCall.stackAvailable hs hu address ha]
    cases variant <;> exact h.memoryFrame address ha

theorem finalizeReset_digest_variant {variant : FinalizeReset.Variant} [Bindings] {boundary : ReturnBoundary}
    {initial s t : RamState} {message : ByteArray}
    (h : LoopKind.storage variant.loopKind initial s)
    (hu : FinalizeReset.Post boundary message s t variant) :
    (⟨(initial.regValue .r8).toNat, 16⟩ : MemoryRegion).HasBytes t.external
      ⟨(Standards.RFC.MD5.messageDigest (Standards.RFC.MD5.bitsOfBytes message)).toArray⟩ := by
  simpa only [FinalizeReset.outputRegion, finalizeReset_outputAddress_variant h] using hu.digest

theorem finalizeReset_stackRegion {initial s : RamState}
    (h : LoopKind.storage .resetFirst initial s)
    (hs : Stack.Valid initial TwoMessages.digestSlicesReset.minStackBytes) :
    FinalizeReset.stackRegion s = Stack.region initial TwoMessages.digestSlicesReset.minStackBytes := by
  exact finalizeReset_stackRegion_variant (variant := .saved) h hs

theorem finalizeReset_outputAddress {initial s : RamState}
    (h : LoopKind.storage .resetFirst initial s) :
    FinalizeReset.outputAddress s = initial.regValue .r8 := by
  exact finalizeReset_outputAddress_variant (variant := .saved) h

theorem finalizeReset_output_contains {initial s : RamState}
    (h : LoopKind.storage .resetFirst initial s) {address : Nat}
    (ha : (FinalizeReset.outputRegion s).Contains address) :
    ((TwoMessages.outputRegion TwoMessages.digestSlicesReset) initial).Contains address := by
  exact finalizeReset_output_contains_variant (variant := .saved) h ha

theorem streaming_finalizeReset_storage [bindings : Bindings] {initial s : RamState}
    {message : ByteArray} {inputs : Array Slices.Input} {first : Nat}
    (h : StreamingState .resetFirst initial message s)
    (hCall : (TwoMessages.ValidCall TwoMessages.digestSlicesReset) bindings initial inputs first) :
    FinalizeReset.Storage s := by
  exact streaming_finalizeReset_storage_variant (variant := .saved) h hCall

private theorem finalizeReset_frame {s t : RamState} (hs : FinalizeReset.Storage s)
    (h : AgreesExcept (FinalizeReset.changes s) s t) :
    MemoryWriteFrame s t (finalizeResetRegions s) := by
  exact finalizeReset_frame_variant (variant := .saved) hs h

theorem finalizeReset_stackRead [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {s t : RamState} (hs : FinalizeReset.Storage s)
    (hu : FinalizeReset.Post boundary message s t) (offset : Nat)
    (hgap : (160 ≤ offset ∧ offset + 8 ≤ 232) ∨ (312 ≤ offset ∧ offset + 8 ≤ 384)) :
    (Operand.mem (stackPtr t + BitVec.ofNat 64 offset) : Operand 64).read t =
      (Operand.mem (stackPtr s + BitVec.ofNat 64 offset) : Operand 64).read s := by
  exact finalizeReset_stackRead_variant (variant := .saved) hs hu offset hgap

theorem finalizeReset_storage [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {initial s t : RamState} (h : LoopKind.storage .resetFirst initial s)
    (hs : FinalizeReset.Storage s) (hu : FinalizeReset.Post boundary message s t) :
    LoopKind.storage .resetSecond initial t := by
  exact finalizeReset_storage_variant (variant := .saved) h hs hu

theorem finalizeReset_total [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {s t : RamState} (hs : FinalizeReset.Storage s)
    (hu : FinalizeReset.Post boundary message s t) : stackWord t 192 = stackWord s 192 := by
  exact finalizeReset_total_variant (variant := .saved) hs hu

theorem finalizeReset_loop_frame [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {initial s t : RamState} (h : LoopKind.storage .resetFirst initial s)
    (hStack : Stack.Valid initial TwoMessages.digestSlicesReset.minStackBytes)
    (hs : FinalizeReset.Storage s) (hu : FinalizeReset.Post boundary message s t) :
    MemoryWriteFrame s t (LoopKind.writable .resetSecond initial) := by
  exact finalizeReset_loop_frame_variant (variant := .saved) h hStack hs hu

theorem finalizeReset_state [bindings : Bindings] {boundary : ReturnBoundary}
    {initial s t : RamState} {message : ByteArray} {inputs : Array Slices.Input} {first : Nat}
    (h : StreamingState .resetFirst initial message s)
    (hCall : (TwoMessages.ValidCall TwoMessages.digestSlicesReset) bindings initial inputs first)
    (hu : FinalizeReset.Post boundary message s t) :
    StreamingState .resetSecond initial ByteArray.empty t := by
  exact finalizeReset_state_variant (variant := .saved) h hCall hu

theorem finalizeReset_digest [Bindings] {boundary : ReturnBoundary}
    {initial s t : RamState} {message : ByteArray}
    (h : LoopKind.storage .resetFirst initial s)
    (hu : FinalizeReset.Post boundary message s t) :
    (⟨(initial.regValue .r8).toNat, 16⟩ : MemoryRegion).HasBytes t.external
      ⟨(Standards.RFC.MD5.messageDigest (Standards.RFC.MD5.bitsOfBytes message)).toArray⟩ := by
  exact finalizeReset_digest_variant (variant := .saved) h hu

end Md5.Proofs.Streaming
