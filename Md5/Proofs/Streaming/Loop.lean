import Md5.Proofs.Streaming.Transport
import Md5.Proofs.Streaming.LoopControl
import Md5.Proofs.Streaming.Execution

namespace Md5.Proofs.Streaming

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Buffered

structure LoopOperations [Bindings] (kind : LoopKind.Kind) (boundary : ReturnBoundary) : Prop where
  update : ∀ message input s, UpdatePre kind boundary message input s →
    ∃ t, UpdatePost kind boundary message input s t
  counter : ∀ s finish index, ReadyToStep s → CodeIn Extracted.programImage s →
    s.RIP ∈ kind.exits →
    (Operand.reg (LoopKind.indexRegister kind) : Operand 64).read s = BitVec.ofNat 64 index →
    LoopKind.count kind s = BitVec.ofNat 64 finish → index < finish → finish < 2^64 →
    MemReadable s (stackPtr s + LoopKind.countOffset kind) 8 → ∃ t, LoopCounterPost kind boundary finish index s t

theorem loadEffect_index {kind : LoopKind.Kind} {s t : RamState}
    (h : (LoopKind.loadEffect kind s).Holds s t) :
    (Operand.reg (LoopKind.indexRegister kind) : Operand 64).read t =
      (Operand.reg (LoopKind.indexRegister kind) : Operand 64).read s := by
  apply h.agrees.read
  cases kind <;> simp [LoopKind.loadEffect, sliceLoadEffect, Effect.components,
    LoopKind.indexRegister, UpdateKind.inputRegister, UpdateKind.sizeRegister]

theorem loadEffect_count {kind : LoopKind.Kind} {s t : RamState}
    (h : (LoopKind.loadEffect kind s).Holds s t) : LoopKind.count kind t = LoopKind.count kind s := by
  cases kind with
  | slices | updateFinalizeInto | resetDiscardFirst =>
    apply h.agrees.read (n := 64) (r := 12)
    simp [LoopKind.loadEffect, sliceLoadEffect, Effect.components,
      UpdateKind.inputRegister, UpdateKind.sizeRegister]
  | resetFirst | finalizeResetFirst =>
    apply h.agrees.read (n := 64) (r := 5)
    simp [LoopKind.loadEffect, sliceLoadEffect, Effect.components,
      UpdateKind.inputRegister, UpdateKind.sizeRegister]
  | resetSecond | finalizeResetSecond | resetDiscardSecond =>
    simp only [LoopKind.count, stackWord, loadEffect_rsp h, Operand.read, loadEffect_external h]

theorem update_loopIndex [Bindings] {kind : LoopKind.Kind} {boundary : ReturnBoundary}
    {s t : RamState} {message input : ByteArray} (h : UpdatePost kind boundary message input s t) :
    (Operand.reg (LoopKind.indexRegister kind) : Operand 64).read t =
      (Operand.reg (LoopKind.indexRegister kind) : Operand 64).read s := by
  apply h.agrees.read
  cases kind <;> simp [LoopKind.indexRegister, UpdateKind.changes, UpdateKind.workRegisters]

theorem update_loopCount [Bindings] {kind : LoopKind.Kind} {boundary : ReturnBoundary}
    {initial s t : RamState} {message input : ByteArray}
    (h : LoopKind.storage kind initial s) (hs : Stack.Valid initial (LoopKind.budget kind))
    (hp : UpdatePre kind boundary message input s) (hu : UpdatePost kind boundary message input s t) :
    LoopKind.count kind t = LoopKind.count kind s := by
  cases kind with
  | slices | updateFinalizeInto | resetDiscardFirst =>
    apply hu.agrees.read (n := 64) (r := 12)
    simp [UpdateKind.changes, UpdateKind.workRegisters]
  | resetFirst | finalizeResetFirst =>
    apply hu.agrees.read (n := 64) (r := 5)
    simp [UpdateKind.changes, UpdateKind.workRegisters]
  | resetSecond | finalizeResetSecond => exact update_stackRead h hs hp hu 192 (by decide +kernel) (by decide +kernel)
  | resetDiscardSecond => exact update_stackRead h hs hp hu 8 (by decide +kernel) (by decide +kernel)

theorem LoopCounterPost.rsp [Bindings] {kind : LoopKind.Kind} {boundary : ReturnBoundary}
    {finish index : Nat} {s t : RamState} (h : LoopCounterPost kind boundary finish index s t) :
    stackPtr t = stackPtr s := by
  apply h.agrees.read (n := 64) (r := 4)
  cases kind <;> simp [LoopKind.indexRegister]

theorem LoopCounterPost.external [Bindings] {kind : LoopKind.Kind} {boundary : ReturnBoundary}
    {finish index : Nat} {s t : RamState} (h : LoopCounterPost kind boundary finish index s t) :
    t.external = s.external := h.agrees.external (by simp [Component.Covers])

theorem LoopCounterPost.count [Bindings] {kind : LoopKind.Kind} {boundary : ReturnBoundary}
    {finish index : Nat} {s t : RamState} (h : LoopCounterPost kind boundary finish index s t) :
    LoopKind.count kind t = LoopKind.count kind s := by
  cases kind with
  | slices | updateFinalizeInto | resetDiscardFirst => exact h.agrees.read (n := 64) (r := 12) (by simp [LoopKind.indexRegister])
  | resetFirst | finalizeResetFirst => exact h.agrees.read (n := 64) (r := 5) (by simp [LoopKind.indexRegister])
  | resetSecond | finalizeResetSecond | resetDiscardSecond => simp only [LoopKind.count, stackWord, h.rsp, Operand.read, h.external]

theorem loop_iteration [bindings : Bindings] {kind : LoopKind.Kind} {boundary : ReturnBoundary}
    (operations : LoopOperations kind boundary) {initial s : RamState}
    {inputs : Array Slices.Input} {start finish index : Nat}
    (h : LoopInvariant kind initial inputs start finish index s)
    (hInputs : Slices.ValidInputs initial inputs)
    (hStack : Stack.Valid initial (LoopKind.budget kind))
    (hSep : MemorySeparation
      (LoopKind.writable kind initial)
      (Slices.readRegions initial inputs))
    (hStride : UnitStringStride bindings) (hOutside : ¬ InProgram boundary.rip)
    (hStart : start ≤ index) (hi : index < finish) (hFinish : finish ≤ inputs.size) :
    ∃ fuel t, Advances boundary fuel s t ∧
      LoopInvariant kind initial inputs start finish (index + 1) t ∧
      MemoryWriteFrame s t #v[Stack.region initial (LoopKind.budget kind)] := by
  have hi' : index < inputs.size := by omega
  obtain ⟨loadFuel, loaded, hLoad, hLoadReady, hLoadCode, he⟩ :=
    load_slice kind boundary hOutside h.ready h.code (h.loadPre hInputs hStack hSep hi' hi)
  have hp := h.updatePre hInputs hStack hSep hStride hOutside hStart hi'
    hLoadReady hLoadCode he
  have hStored := PrologueStorage.of_external_eq h.storage (loadEffect_rsp he) (loadEffect_external he)
  obtain ⟨updated, hu⟩ := operations.update _ _ loaded hp
  have hStored' := loopStorage_update hStored hStack hp hu
  have hIndex : (Operand.reg (LoopKind.indexRegister kind) : Operand 64).read updated =
      BitVec.ofNat 64 index := (update_loopIndex hu).trans ((loadEffect_index he).trans h.indexValue)
  have hCount : LoopKind.count kind updated = BitVec.ofNat 64 finish :=
    (update_loopCount hStored hStack hp hu).trans ((loadEffect_count he).trans h.countValue)
  have hGrows : ∀ address : BitVec 64, (initial.external[address]?).isSome →
      (updated.external[address]?).isSome :=
    fun a ha ↦ hu.agrees.grow a (he.agrees.grow a (h.grows a ha))
  have hCountReadable := loopStorage_readable hStored' hStack hGrows (LoopKind.countOffset kind).toNat 8
    (by cases kind <;> decide +kernel)
  obtain ⟨t, ht⟩ := operations.counter updated finish index hu.ready hu.code hu.rip hIndex hCount hi
    (by have := validInputs_size_lt hInputs; omega) (by
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using hCountReadable)
  obtain ⟨updateFuel, hUpdate⟩ := hu.advances
  obtain ⟨counterFuel, hCounter⟩ := ht.advances
  have hStackFrame : MemoryWriteFrame s t #v[Stack.region initial (LoopKind.budget kind)] := by
    intro a ha
    rw [ht.external, loopUpdate_stackFrame hStored hStack hp hu a ha, loadEffect_external he]
  refine ⟨loadFuel + updateFuel + counterFuel, t,
    (hLoad.trans hUpdate).trans hCounter, ?_, hStackFrame⟩
  refine {
    storage := PrologueStorage.of_external_eq hStored' ht.rsp ht.external
    ready := ht.ready
    code := ht.code
    rip := ht.rip
    indexValue := ht.indexValue
    countValue := ht.count.trans hCount
    sse := ?_
    df := ?_
    absorbed := ?_
    grows := ?_
    memoryFrame := ?_
    secondRegisters := ?_
    resetTotal := ?_
    discardSecondMemcpy := ?_
    discardTotal := ?_
  }
  · exact SupportedSSE.of_agreesExcept ht.agrees
      (SupportedSSE.of_agreesExcept hu.agrees (SupportedSSE.of_agreesExcept he.agrees h.sse))
  · exact ht.agrees.directionFlagClear (by simp)
      (hu.agrees.directionFlagClear (by simp [UpdateKind.changes])
        (he.agrees.directionFlagClear
          (by simp [LoopKind.loadEffect, sliceLoadEffect, Effect.components]) h.df))
  · have hc : kind.context t = kind.context loaded := by
      simp only [UpdateKind.context, ht.rsp, hu.rsp]
    rw [hc, message_extract_succ inputs start index hStart hi']
    exact absorbed_of_external_eq hu.absorbed ht.external
  · exact fun a ha ↦ ht.agrees.grow a (hGrows a ha)
  · have hf : MemoryWriteFrame initial loaded (LoopKind.writable kind initial) := by
      intro a ha
      rw [loadEffect_external he]
      exact h.memoryFrame a ha
    have hf' := memoryWriteFrame_trans hf (loopUpdate_frame hStored hStack hp hu)
    intro a ha
    rw [ht.external]
    exact hf' a ha
  · intro hk
    have htotal := h.resetTotal hk
    rcases hk with hk | hk
    all_goals
      subst kind
      have hloaded : stackWord loaded 192 = stackWord s 192 := by
        simp only [stackWord, loadEffect_rsp he, Operand.read, loadEffect_external he]
      have hupdated : stackWord updated 192 = stackWord loaded 192 :=
        update_stackRead hStored hStack hp hu 192 (by decide +kernel) (by decide +kernel)
      have hcounter : stackWord t 192 = stackWord updated 192 := by
        simp only [stackWord, ht.rsp, Operand.read, ht.external]
      exact hcounter.trans (hupdated.trans (hloaded.trans htotal))

  · intro hk
    obtain ⟨h3, h15⟩ := h.secondRegisters hk
    rcases hk with hk | hk
    all_goals
      subst kind
      have h3load := he.agrees.read (n := 64) (r := 3) (by
        simp [LoopKind.loadEffect, sliceLoadEffect, Effect.components,
          UpdateKind.inputRegister, UpdateKind.sizeRegister])
      have h15load := he.agrees.read (n := 64) (r := 15) (by
        simp [LoopKind.loadEffect, sliceLoadEffect, Effect.components,
          UpdateKind.inputRegister, UpdateKind.sizeRegister])
      have h3update := hu.agrees.read (n := 64) (r := 3) (by
        simp [UpdateKind.changes, UpdateKind.workRegisters])
      have h15update := hu.agrees.read (n := 64) (r := 15) (by
        simp [UpdateKind.changes, UpdateKind.workRegisters])
      have h3counter := ht.agrees.read (n := 64) (r := 3) (by simp [LoopKind.indexRegister])
      have h15counter := ht.agrees.read (n := 64) (r := 15) (by simp [LoopKind.indexRegister])
      refine ⟨?_, h15counter.trans (h15update.trans (h15load.trans h15))⟩
      rw [h3counter, h3update, h3load, h3]
      simp only [UpdateKind.context, ht.rsp, hu.rsp, loadEffect_rsp he]
  · intro hk
    have h15 := h.discardSecondMemcpy hk
    subst kind
    have hl := he.agrees.read (n := 64) (r := 15) (by
      simp [LoopKind.loadEffect, sliceLoadEffect, Effect.components,
        UpdateKind.inputRegister, UpdateKind.sizeRegister])
    have hu' := hu.agrees.read (n := 64) (r := 15) (by
      simp [UpdateKind.changes, UpdateKind.workRegisters])
    have ht' := ht.agrees.read (n := 64) (r := 15) (by simp [LoopKind.indexRegister])
    exact ht'.trans (hu'.trans (hl.trans h15))

  · intro hk
    have htotal := h.discardTotal hk
    subst kind
    have hloaded : stackWord loaded 8 = stackWord s 8 := by
      simp only [stackWord, loadEffect_rsp he, Operand.read, loadEffect_external he]
    have hupdated : stackWord updated 8 = stackWord loaded 8 :=
      update_stackRead hStored hStack hp hu 8 (by decide +kernel) (by decide +kernel)
    have hcounter : stackWord t 8 = stackWord updated 8 := by
      simp only [stackWord, ht.rsp, Operand.read, ht.external]
    exact hcounter.trans (hupdated.trans (hloaded.trans htotal))


theorem loop_complete [bindings : Bindings] {kind : LoopKind.Kind} {boundary : ReturnBoundary}
    (operations : LoopOperations kind boundary) {initial s : RamState}
    {inputs : Array Slices.Input} {start finish : Nat}
    (h : LoopInvariant kind initial inputs start finish start s)
    (hInputs : Slices.ValidInputs initial inputs)
    (hStack : Stack.Valid initial (LoopKind.budget kind))
    (hSep : MemorySeparation
      (LoopKind.writable kind initial)
      (Slices.readRegions initial inputs))
    (hStride : UnitStringStride bindings) (hOutside : ¬ InProgram boundary.rip)
    (hStart : start ≤ finish) (hFinish : finish ≤ inputs.size) :
    ∃ fuel t, Advances boundary fuel s t ∧ LoopInvariant kind initial inputs start finish finish t ∧
      MemoryWriteFrame s t #v[Stack.region initial (LoopKind.budget kind)] := by
  apply advances_loop (invariant := fun i t ↦
    LoopInvariant kind initial inputs start finish i t ∧
      MemoryWriteFrame s t #v[Stack.region initial (LoopKind.budget kind)])
    hStart (s := s) (hs := ⟨h, fun _ _ ↦ rfl⟩)
  intro index hstart hi state hstate
  obtain ⟨n, t, hr, ht, hf⟩ :=
    loop_iteration operations hstate.1 hInputs hStack hSep hStride hOutside hstart hi hFinish
  exact ⟨n, t, hr, ht, memoryWriteFrame_trans hstate.2 hf⟩

end Md5.Proofs.Streaming
