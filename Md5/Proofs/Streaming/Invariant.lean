import Md5.Proofs.Streaming.Prologue
import Md5.Proofs.Streaming.Load
import Md5.Proofs.Streaming.Memory

namespace Md5.Proofs.Streaming

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

namespace LoopKind

def frame : Kind → Nat
  | .slices => 296
  | .resetFirst | .resetSecond => 328
  | .updateFinalizeInto => 280
  | .finalizeResetFirst | .finalizeResetSecond | .resetDiscardFirst | .resetDiscardSecond => 312

def budget : Kind → Nat
  | .slices => OneMessage.digestSlices.minStackBytes
  | .resetFirst | .resetSecond => TwoMessages.digestSlicesReset.minStackBytes
  | .updateFinalizeInto => OneMessage.updateFinalizeInto.minStackBytes
  | .finalizeResetFirst | .finalizeResetSecond => TwoMessages.finalizeIntoResetSlices.minStackBytes
  | .resetDiscardFirst | .resetDiscardSecond => ResetThenDigest.updateResetSlices.minStackBytes

def outputOffset : Kind → Nat
  | .slices | .updateFinalizeInto => 168
  | .resetFirst | .resetSecond | .finalizeResetFirst | .finalizeResetSecond => 184
  | .resetDiscardFirst | .resetDiscardSecond => 288

def outputRegister : Kind → Syntax.Reg
  | .slices | .updateFinalizeInto => .rcx
  | _ => .r8

def outputRegion (kind : Kind) (initial : RamState) : MemoryRegion :=
  match kind with
  | .slices => (OneMessage.outputRegion OneMessage.digestSlices) initial
  | .updateFinalizeInto => (OneMessage.outputRegion OneMessage.updateFinalizeInto) initial
  | .resetFirst | .resetSecond => (TwoMessages.outputRegion TwoMessages.digestSlicesReset) initial
  | .finalizeResetFirst | .finalizeResetSecond =>
    (TwoMessages.outputRegion TwoMessages.finalizeIntoResetSlices) initial
  | .resetDiscardFirst | .resetDiscardSecond =>
    (ResetThenDigest.outputRegion ResetThenDigest.updateResetSlices) initial

def finalPC : Kind → BitVec 64
  | .slices => 0x10042b
  | .resetFirst => 0x100790
  | .resetSecond => 0x100a90
  | .updateFinalizeInto => 0x1019db
  | .finalizeResetFirst => 0x100e40
  | .finalizeResetSecond => 0x101120
  | .resetDiscardFirst => 0x1014c7
  | .resetDiscardSecond => 0x1015fd

def countOffset : Kind → BitVec 64
  | .resetDiscardSecond => 8
  | _ => 192

def count (kind : Kind) (s : RamState) : BitVec 64 :=
  match kind with
  | .slices | .updateFinalizeInto | .resetDiscardFirst => (Operand.reg 12 : Operand 64).read s
  | .resetFirst | .finalizeResetFirst => (Operand.reg 5 : Operand 64).read s
  | .resetSecond | .finalizeResetSecond => stackWord s 192
  | .resetDiscardSecond => stackWord s 8

abbrev storage (kind : Kind) (initial s : RamState) : Prop :=
  PrologueStorage (frame kind) kind.contextOffset (outputOffset kind)
    (pointerOffset kind).toNat (lengthOffset kind).toNat (budget kind)
    (outputRegister kind) initial s

def writable (kind : Kind) (initial : RamState) :
    Vector MemoryRegion (match kind with
      | .slices | .updateFinalizeInto | .resetDiscardFirst | .resetDiscardSecond => 1
      | _ => 2) :=
  match kind with
  | .slices | .updateFinalizeInto | .resetDiscardFirst | .resetDiscardSecond =>
    #v[Stack.region initial (budget kind)]
  | .resetFirst | .resetSecond | .finalizeResetFirst | .finalizeResetSecond =>
    #v[outputRegion kind initial, Stack.region initial (budget kind)]

theorem budget_eq (kind : Kind) : budget kind = frame kind + 368 := by
  cases kind <;> decide +kernel

theorem stack_mem_writable (kind : Kind) (initial : RamState) :
    Stack.region initial (budget kind) ∈ writable kind initial := by
  cases kind with
  | slices => exact Vector.getElem_mem (xs := writable .slices initial) (i := 0) (by decide)
  | resetFirst => exact Vector.getElem_mem (xs := writable .resetFirst initial) (i := 1) (by decide)
  | resetSecond => exact Vector.getElem_mem (xs := writable .resetSecond initial) (i := 1) (by decide)
  | updateFinalizeInto => exact Vector.getElem_mem (xs := writable .updateFinalizeInto initial) (i := 0) (by decide)
  | finalizeResetFirst => exact Vector.getElem_mem (xs := writable .finalizeResetFirst initial) (i := 1) (by decide)
  | finalizeResetSecond => exact Vector.getElem_mem (xs := writable .finalizeResetSecond initial) (i := 1) (by decide)
  | resetDiscardFirst => exact Vector.getElem_mem (xs := writable .resetDiscardFirst initial) (i := 0) (by decide)
  | resetDiscardSecond => exact Vector.getElem_mem (xs := writable .resetDiscardSecond initial) (i := 0) (by decide)

end LoopKind

structure StreamingState [bindings : Bindings] (kind : LoopKind.Kind) (initial : RamState)
    (message : ByteArray) (s : RamState) : Prop where
  storage : LoopKind.storage kind initial s
  ready : ReadyToStep s
  code : CodeIn Extracted.programImage s
  sse : SupportedSSE bindings.processor s
  df : Prelude.RFLAGS.DirectionFlagClear s.RFLAGS
  absorbed : Buffered.Absorbed (kind.context s) message s
  grows : ∀ address : BitVec 64, (initial.external[address]?).isSome → (s.external[address]?).isSome
  memoryFrame : MemoryWriteFrame initial s (LoopKind.writable kind initial)

structure LoopInvariant [bindings : Bindings] (kind : LoopKind.Kind) (initial : RamState)
    (inputs : Array Slices.Input) (start finish index : Nat) (s : RamState) : Prop extends
    StreamingState kind initial (Slices.message (inputs.extract start index)) s where
  rip : s.RIP = if index < finish then LoopKind.entry kind else LoopKind.finalPC kind
  indexValue : (Operand.reg (LoopKind.indexRegister kind) : Operand 64).read s =
    BitVec.ofNat 64 index
  countValue : LoopKind.count kind s = BitVec.ofNat 64 finish
  resetTotal : (kind = .resetFirst ∨ kind = .finalizeResetFirst) → stackWord s 192 = BitVec.ofNat 64 inputs.size
  secondRegisters : (kind = .resetSecond ∨ kind = .finalizeResetSecond) →
    (Operand.reg 3 : Operand 64).read s = kind.context s ∧
    (Operand.reg 15 : Operand 64).read s = 0x1024b0
  discardSecondMemcpy : kind = .resetDiscardSecond →
    (Operand.reg 15 : Operand 64).read s = 0x1024b0
  discardTotal : kind = .resetDiscardFirst → stackWord s 8 = BitVec.ofNat 64 inputs.size

theorem loopStorage_toNat {kind : LoopKind.Kind} {initial s : RamState}
    (h : LoopKind.storage kind initial s) (hs : Stack.Valid initial (LoopKind.budget kind)) :
    (stackPtr s).toNat = (stackPtr initial).toNat - (LoopKind.frame kind + 48) := by
  have hu : LoopKind.budget kind ≤ (stackPtr initial).toNat := hs.2.2.1
  rw [LoopKind.budget_eq] at hu
  have hn : 48 + LoopKind.frame kind < 2^64 := by
    have := (stackPtr initial).isLt
    omega
  rw [h.rsp, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  have := (stackPtr initial).isLt
  omega

theorem loopStorage_bounds {kind : LoopKind.Kind} {initial s : RamState}
    (h : LoopKind.storage kind initial s) (hs : Stack.Valid initial (LoopKind.budget kind)) :
    320 ≤ (stackPtr s).toNat ∧
      (stackPtr s).toNat + LoopKind.frame kind + 56 < userAddressLimit := by
  have hu : LoopKind.budget kind ≤ (stackPtr initial).toNat := hs.2.2.1
  have hb := hs.1
  change (stackPtr initial).toNat - LoopKind.budget kind +
    ((stackPtr initial).toNat + 8 - ((stackPtr initial).toNat - LoopKind.budget kind)) <
      userAddressLimit at hb
  rw [LoopKind.budget_eq] at hu hb
  rw [loopStorage_toNat h hs]
  constructor <;> omega

theorem loopStorage_region {kind : LoopKind.Kind} {initial s : RamState}
    (h : LoopKind.storage kind initial s) (hs : Stack.Valid initial (LoopKind.budget kind)) :
    Stack.region initial (LoopKind.budget kind) =
      ⟨(stackPtr s).toNat - 320, LoopKind.frame kind + 376⟩ := by
  have hu : LoopKind.budget kind ≤ (stackPtr initial).toNat := hs.2.2.1
  rw [LoopKind.budget_eq] at hu
  have hstart : (stackPtr initial).toNat - LoopKind.budget kind = (stackPtr s).toNat - 320 := by
    rw [LoopKind.budget_eq, loopStorage_toNat h hs]
    omega
  have hsize : (stackPtr initial).toNat + 8 -
      ((stackPtr initial).toNat - LoopKind.budget kind) = LoopKind.frame kind + 376 := by
    rw [LoopKind.budget_eq]
    omega
  change MemoryRegion.mk ((stackPtr initial).toNat - LoopKind.budget kind)
    ((stackPtr initial).toNat + 8 - ((stackPtr initial).toNat - LoopKind.budget kind)) = _
  rw [hsize, hstart]

theorem loopStorage_address {kind : LoopKind.Kind} {initial s : RamState}
    (h : LoopKind.storage kind initial s) (hs : Stack.Valid initial (LoopKind.budget kind))
    {offset : Nat} (ho : offset ≤ LoopKind.frame kind + 56) :
    (stackPtr s + BitVec.ofNat 64 offset).toNat = (stackPtr s).toNat + offset := by
  have hb := (loopStorage_bounds h hs).2
  change (stackPtr s).toNat + LoopKind.frame kind + 56 < 2^32 at hb
  rw [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show offset < 2^64 by omega),
    Nat.mod_eq_of_lt (show (stackPtr s).toNat + offset < 2^64 by omega)]

theorem loopStorage_readable {kind : LoopKind.Kind} {initial s : RamState}
    (h : LoopKind.storage kind initial s) (hs : Stack.Valid initial (LoopKind.budget kind))
    (hg : ∀ address : BitVec 64, (initial.external[address]?).isSome → (s.external[address]?).isSome)
    (offset len : Nat) (ho : offset + len ≤ LoopKind.frame kind + 56) :
    MemReadable s (stackPtr s + BitVec.ofNat 64 offset) len := by
  have hb := loopStorage_bounds h hs
  have ha : (Stack.region initial (LoopKind.budget kind)).Allocated s.external := by
    intro address hx
    exact Option.isSome_iff_exists.mp (hg address
      (Option.isSome_iff_exists.mpr (hs.2.1 address hx)))
  apply memReadable_of_allocated ha
  · rw [loopStorage_address h hs (by omega)]
    omega
  · rw [loopStorage_region h hs, loopStorage_address h hs (by omega)]
    dsimp only
    omega
  · rw [loopStorage_region h hs, loopStorage_address h hs (by omega)]
    dsimp only
    omega

theorem shifted_index (index : Nat) :
    (BitVec.ofNat 64 index <<< 3) = BitVec.ofNat 64 (8 * index) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 index * BitVec.ofNat 64 8 = BitVec.ofNat 64 (8 * index)
  rw [← BitVec.ofNat_mul, Nat.mul_comm]

theorem LoopInvariant.pointerAddress [Bindings] {kind : LoopKind.Kind} {initial s : RamState}
    {inputs : Array Slices.Input} {start finish index : Nat}
    (h : LoopInvariant kind initial inputs start finish index s) :
    sliceTableAddress s (LoopKind.pointerOffset kind) (LoopKind.indexRegister kind) =
      initial.regValue .rdi + BitVec.ofNat 64 (8 * index) := by
  have hp : stackWord s (LoopKind.pointerOffset kind) = initial.regValue .rdi := by
    simpa only [stackWord, BitVec.ofNat_toNat, BitVec.setWidth_eq] using h.storage.pointer
  rw [sliceTableAddress, hp, h.indexValue, shifted_index]

theorem LoopInvariant.lengthAddress [Bindings] {kind : LoopKind.Kind} {initial s : RamState}
    {inputs : Array Slices.Input} {start finish index : Nat}
    (h : LoopInvariant kind initial inputs start finish index s) :
    sliceTableAddress s (LoopKind.lengthOffset kind) (LoopKind.indexRegister kind) =
      initial.regValue .rdx + BitVec.ofNat 64 (8 * index) := by
  have hp : stackWord s (LoopKind.lengthOffset kind) = initial.regValue .rdx := by
    simpa only [stackWord, BitVec.ofNat_toNat, BitVec.setWidth_eq] using h.storage.length
  rw [sliceTableAddress, hp, h.indexValue, shifted_index]

theorem LoopInvariant.loadPre [Bindings] {kind : LoopKind.Kind} {initial s : RamState}
    {inputs : Array Slices.Input} {start finish index : Nat}
    (h : LoopInvariant kind initial inputs start finish index s)
    (hInputs : Slices.ValidInputs initial inputs)
    (hStack : Stack.Valid initial (LoopKind.budget kind))
    (hSep : MemorySeparation
      (LoopKind.writable kind initial)
      (Slices.readRegions initial inputs)) (hi : index < inputs.size) (hnext : index < finish) :
    LoopKind.loadPre kind s := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [ite_eq_left hnext] using h.rip
  · simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      loopStorage_readable h.storage hStack h.grows (LoopKind.pointerOffset kind).toNat 8
        (by cases kind <;> decide +kernel)
  · simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      loopStorage_readable h.storage hStack h.grows (LoopKind.lengthOffset kind).toNat 8
        (by cases kind <;> decide +kernel)
  · rw [h.pointerAddress]
    exact (validInputs_pointer_preserved hInputs h.memoryFrame
      (fun r hr ↦ (hSep.2 r hr).1 _ (by simp [Slices.readRegions])) ⟨index, hi⟩).2
  · rw [h.lengthAddress]
    exact (validInputs_length_preserved hInputs h.memoryFrame
      (fun r hr ↦ (hSep.2 r hr).1 _ (by simp [Slices.readRegions])) ⟨index, hi⟩).2

theorem loadEffect_rsp {kind : LoopKind.Kind} {s t : RamState}
    (h : (LoopKind.loadEffect kind s).Holds s t) : stackPtr t = stackPtr s := by
  apply h.agrees.read (n := 64) (r := 4)
  cases kind <;> simp [LoopKind.loadEffect, sliceLoadEffect, Effect.components,
    Buffered.UpdateKind.inputRegister, Buffered.UpdateKind.sizeRegister]

theorem loadEffect_external {kind : LoopKind.Kind} {s t : RamState}
    (h : (LoopKind.loadEffect kind s).Holds s t) : t.external = s.external := by
  apply h.agrees.external
  cases kind <;> simp [LoopKind.loadEffect, sliceLoadEffect, Effect.components,
    Buffered.UpdateKind.inputRegister, Buffered.UpdateKind.sizeRegister, Component.Covers]

theorem loadEffect_pointer {kind : LoopKind.Kind} {s t : RamState}
    (h : (LoopKind.loadEffect kind s).Holds s t) :
    (Operand.reg kind.inputRegister : Operand 64).read t =
      (Operand.mem (sliceTableAddress s (LoopKind.pointerOffset kind)
        (LoopKind.indexRegister kind)) : Operand 64).read s := h.writes.1

theorem loadEffect_length {kind : LoopKind.Kind} {s t : RamState}
    (h : (LoopKind.loadEffect kind s).Holds s t) :
    (Operand.reg kind.sizeRegister : Operand 64).read t =
      (Operand.mem (sliceTableAddress s (LoopKind.lengthOffset kind)
        (LoopKind.indexRegister kind)) : Operand 64).read s := h.writes.2.2

theorem LoopInvariant.load_pointer [Bindings] {kind : LoopKind.Kind} {initial s t : RamState}
    {inputs : Array Slices.Input} {start finish index : Nat}
    (h : LoopInvariant kind initial inputs start finish index s)
    (hInputs : Slices.ValidInputs initial inputs)
    (hSep : MemorySeparation
      (LoopKind.writable kind initial)
      (Slices.readRegions initial inputs)) (hi : index < inputs.size)
    (he : (LoopKind.loadEffect kind s).Holds s t) :
    (Operand.reg kind.inputRegister : Operand 64).read t = inputs[index].address := by
  rw [loadEffect_pointer he, h.pointerAddress]
  exact (validInputs_pointer_preserved hInputs h.memoryFrame
    (fun r hr ↦ (hSep.2 r hr).1 _ (by simp [Slices.readRegions])) ⟨index, hi⟩).1

theorem LoopInvariant.load_length [Bindings] {kind : LoopKind.Kind} {initial s t : RamState}
    {inputs : Array Slices.Input} {start finish index : Nat}
    (h : LoopInvariant kind initial inputs start finish index s)
    (hInputs : Slices.ValidInputs initial inputs)
    (hSep : MemorySeparation
      (LoopKind.writable kind initial)
      (Slices.readRegions initial inputs)) (hi : index < inputs.size)
    (he : (LoopKind.loadEffect kind s).Holds s t) :
    (Operand.reg kind.sizeRegister : Operand 64).read t =
      BitVec.ofNat 64 inputs[index].bytes.size := by
  rw [loadEffect_length he, h.lengthAddress]
  exact (validInputs_length_preserved hInputs h.memoryFrame
    (fun r hr ↦ (hSep.2 r hr).1 _ (by simp [Slices.readRegions])) ⟨index, hi⟩).1

end Md5.Proofs.Streaming
