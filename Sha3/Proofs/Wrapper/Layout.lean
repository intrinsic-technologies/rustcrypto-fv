import Sha3.Proofs.Variant
import X86Proofs.Program.ReadWrite.Stack

namespace Sha3.Proofs.Wrapper

open X86 X86.Machine X86Proofs Prelude Sha3.Spec.Program

inductive Mode where
  | plain | reset | finalizeReset
  | digest | finalizeFixedReset | digestFinalizeIntoReset | digestFinalizeReset
  deriving DecidableEq

namespace Mode

def entry (mode : Mode) (v : Variant) (keccak : Bool := false)
    (fullState : Bool := false) : Routine :=
  match mode with
  | .plain => v.entry keccak fullState
  | .reset => v.resetEntry keccak fullState
  | .finalizeReset => v.finalizeResetEntry keccak fullState
  | .digest => v.digestEntry keccak fullState
  | .finalizeFixedReset => v.finalizeFixedResetEntry keccak fullState
  | .digestFinalizeIntoReset => v.digestFinalizeIntoResetEntry keccak fullState
  | .digestFinalizeReset => v.digestFinalizeResetEntry keccak fullState

def frameSize (mode : Mode) (v : Variant) (_keccak : Bool := false)
    (fullState : Bool := false) : Nat :=
  match mode with
  | .plain => if fullState then 664 else match v with
    | .sha224 | .sha256 => 328 | .sha384 => 360 | .sha512 => 392
  | .digest => if fullState then 648 else match v with
    | .sha224 | .sha256 => 312 | .sha384 => 344 | .sha512 => 376
  | .reset => 264
  | .finalizeReset | .digestFinalizeIntoReset => 488
  | .finalizeFixedReset | .digestFinalizeReset => if fullState then 696 else match v with
    | .sha224 | .sha256 => 520 | .sha384 => 536 | .sha512 => 552

def stateOffset (mode : Mode) (v : Variant) (_keccak : Bool := false)
    (fullState : Bool := false) : Nat :=
  match mode with
  | .plain => if fullState then 8 else match v with
    | .sha224 | .sha256 => 72 | .sha384 => 104 | .sha512 => 136
  | .digest => if fullState then 0 else match v with
    | .sha224 | .sha256 => 72 | .sha384 => 104 | .sha512 => 136
  | .reset => 8
  | .finalizeReset | .digestFinalizeIntoReset => 24
  | .finalizeFixedReset | .digestFinalizeReset => if fullState then 32 else match v with
    | .sha224 | .sha256 => 264 | .sha384 => 280 | .sha512 => 296

def hasBeforeOutput : Mode → Bool
  | .plain | .reset | .digest => false
  | _ => true

def writeCount : Mode → Nat
  | .plain | .reset | .digest => 2
  | _ => 3

def output : Mode → Routine → RamState → MemoryRegion
  | .plain | .reset => outputRegion
  | .digest => digestOutputRegion
  | _ => secondOutputRegion

def pushCount (mode : Mode) (fullState : Bool := false) : Nat :=
  match mode with
  | .digest => if fullState then 5 else 4
  | _ => 6

abbrev savedCount := pushCount

def savedBytes (mode : Mode) (fullState : Bool := false) : Nat :=
  8 * mode.pushCount fullState

def savedRegisters (mode : Mode) (fullState : Bool := false) :
    Vector Syntax.Reg (mode.pushCount fullState) :=
  match mode, fullState with
  | .digest, false => #v[.rbx, .r12, .r14, .r15]
  | .digest, true => #v[.rbx, .r12, .r13, .r14, .r15]
  | .plain, _ | .reset, _ | .finalizeReset, _ | .finalizeFixedReset, _ |
      .digestFinalizeIntoReset, _ | .digestFinalizeReset, _ =>
    #v[.rbx, .r12, .r13, .r14, .r15, .rbp]

theorem entry_digestBytes (mode : Mode) (v : Variant) (keccak : Bool := false)
    (fullState : Bool := false) :
    (mode.entry v keccak fullState).outputBytes = v.digestBytes fullState := by
  cases mode <;> cases v <;> cases keccak <;> cases fullState <;> rfl

theorem stackBudget (mode : Mode) (v : Variant) (keccak : Bool := false)
    (fullState : Bool := false) :
    (mode.entry v keccak fullState).minStackBytes = mode.frameSize v keccak fullState + 464 := by
  cases mode <;> cases v <;> cases keccak <;> cases fullState <;> rfl

end Mode

def frameBase (initial : RamState) (v : Variant) (mode : Mode)
    (keccak : Bool := false) (fullState : Bool := false) : BitVec 64 :=
  initial.regValue .rsp - BitVec.ofNat 64 (mode.frameSize v keccak fullState)

def statePointer (initial : RamState) (v : Variant) (mode : Mode)
    (keccak : Bool := false) (fullState : Bool := false) : BitVec 64 :=
  frameBase initial v mode keccak fullState + BitVec.ofNat 64 (mode.stateOffset v keccak fullState)

def savedRegisters : Vector Syntax.Reg 6 := #v[.rbx, .r12, .r13, .r14, .r15, .rbp]

def writeRegions (initial : RamState) (v : Variant) (mode : Mode)
    (keccak : Bool := false) (fullState : Bool := false) : Vector MemoryRegion mode.writeCount :=
  match mode with
  | .plain | .reset => #v[outputRegion (mode.entry v keccak fullState) initial,
      Stack.region initial (mode.entry v keccak fullState).minStackBytes]
  | .digest => #v[digestOutputRegion (mode.entry v keccak fullState) initial,
      Stack.region initial (mode.entry v keccak fullState).minStackBytes]
  | .finalizeReset | .finalizeFixedReset | .digestFinalizeIntoReset | .digestFinalizeReset =>
    #v[outputRegion (mode.entry v keccak fullState) initial,
      secondOutputRegion (mode.entry v keccak fullState) initial,
      Stack.region initial (mode.entry v keccak fullState).minStackBytes]

def invocationReadRegions (initial : RamState) (inputs : Array Input) (mode : Mode) :
    List MemoryRegion :=
  match mode with
  | .digest => inputs.toList.map Input.region
  | _ => readRegions initial inputs

def ValidInvocation (_bindings : Bindings) (v : Variant) (mode : Mode)
    (initial : RamState) (inputs : Array Input) (split : Nat)
    (keccak : Bool := false) (fullState : Bool := false) : Prop :=
  let call :=
    match mode with
      | .plain => ValidCall (mode.entry v keccak fullState) initial inputs
      | .reset => ValidSplitCall (mode.entry v keccak fullState) initial inputs split
      | .digest => ∃ data, inputs = #[⟨initial.regValue .rdi, data⟩] ∧
          ValidDigestCall (mode.entry v keccak fullState) initial data
      | _ => ValidTwoOutputCall (mode.entry v keccak fullState) initial inputs split
  if fullState then (v = .sha256 ∧ keccak = true) ∧ call else call

namespace ValidInvocation

variable {bindings : Bindings} {v : Variant} {mode : Mode} {initial : RamState}
  {inputs : Array Input} {split : Nat} {keccak fullState : Bool}

theorem call (h : ValidInvocation bindings v mode initial inputs split keccak fullState) :
    match mode with
  | .plain => ValidCall (mode.entry v keccak fullState) initial inputs
  | .reset => ValidSplitCall (mode.entry v keccak fullState) initial inputs split
  | .digest => ∃ data, inputs = #[⟨initial.regValue .rdi, data⟩] ∧
      ValidDigestCall (mode.entry v keccak fullState) initial data
  | _ => ValidTwoOutputCall (mode.entry v keccak fullState) initial inputs split := by
  cases fullState with
  | false => cases mode <;> exact h
  | true => cases mode <;> exact h.2

theorem fullState_valid (h : ValidInvocation bindings v mode initial inputs split keccak fullState)
    (hf : fullState = true) : v = .sha256 ∧ keccak = true := by
  subst fullState
  exact h.1


theorem programLoaded (h : ValidInvocation bindings v mode initial inputs split keccak fullState) :
    ProgramLoaded initial := by
  cases mode with
  | digest => obtain ⟨data, _, hd⟩ := h.call; exact hd.programLoaded
  | _ => exact h.call.programLoaded

theorem directionFlagUnset (h : ValidInvocation bindings v mode initial inputs split keccak fullState) :
    DirectionFlagUnset initial := by
  cases mode with
  | digest => obtain ⟨data, _, hd⟩ := h.call; exact hd.directionFlagUnset
  | _ => exact h.call.directionFlagUnset

theorem atEntryPoint (h : ValidInvocation bindings v mode initial inputs split keccak fullState) :
    initial.RIP = (mode.entry v keccak fullState).entryAddress := by
  cases mode with
  | digest => obtain ⟨data, _, hd⟩ := h.call; exact hd.atEntryPoint
  | _ => exact h.call.atEntryPoint

theorem stackAvailable (h : ValidInvocation bindings v mode initial inputs split keccak fullState) :
    Stack.Valid initial (mode.entry v keccak fullState).minStackBytes := by
  cases mode with
  | digest => obtain ⟨data, _, hd⟩ := h.call; exact hd.stackAvailable
  | _ => exact h.call.stackAvailable

theorem returnAddress (h : ValidInvocation bindings v mode initial inputs split keccak fullState) :
    ValidReturnAddress initial := by
  cases mode with
  | digest => obtain ⟨data, _, hd⟩ := h.call; exact hd.returnAddress
  | _ => exact h.call.returnAddress

theorem inputSlices (h : ValidInvocation bindings v mode initial inputs split keccak fullState)
    (hmode : mode ≠ .digest := by decide) : ValidInputSlices initial inputs := by
  cases mode with
  | digest => exact False.elim (hmode rfl)
  | _ => exact h.call.inputSlices

theorem outputWritable (h : ValidInvocation bindings v mode initial inputs split keccak fullState) :
    ValidOutput initial (mode.output (mode.entry v keccak fullState) initial) := by
  cases mode with
  | digest => obtain ⟨data, _, hd⟩ := h.call; exact hd.outputInMemory
  | plain | reset => exact h.call.outputInMemory
  | _ => exact h.call.secondOutputInMemory

theorem separation (h : ValidInvocation bindings v mode initial inputs split keccak fullState) :
    MemorySeparation (invocationReadRegions initial inputs mode)
      (writeRegions initial v mode keccak fullState) := by
  cases mode with
  | digest =>
    obtain ⟨data, rfl, hd⟩ := h.call
    exact hd.separation
  | _ => exact h.call.separation

theorem sliceSeparation (h : ValidInvocation bindings v mode initial inputs split keccak fullState)
    (hmode : mode ≠ .digest := by decide) :
    MemorySeparation (readRegions initial inputs) (writeRegions initial v mode keccak fullState) := by
  cases mode with
  | digest => exact False.elim (hmode rfl)
  | _ => exact h.call.separation

end ValidInvocation

structure SavedFrame (initial s : RamState) (mode : Mode := .plain)
    (fullState : Bool := false) : Prop where
  saved : ∀ i : Fin (mode.pushCount fullState),
    (Operand.mem (initial.regValue .rsp - BitVec.ofNat 64 (mode.savedBytes fullState) +
      BitVec.ofNat 64 (8 * i.val)) : Operand 64).read s =
      initial.regValue (mode.savedRegisters fullState)[i]
  returnSlot : (Operand.mem (initial.regValue .rsp) : Operand 64).read s =
    (Operand.mem (initial.regValue .rsp) : Operand 64).read initial

theorem stack_mem_writeRegions (initial : RamState) (v : Variant) (mode : Mode)
    (keccak : Bool := false) (fullState : Bool := false) :
    Stack.region initial (mode.entry v keccak fullState).minStackBytes ∈
      writeRegions initial v mode keccak fullState := by
  cases mode with
  | plain | reset | digest => exact Vector.mem_iff_getElem.mpr ⟨1, by decide, rfl⟩
  | _ => exact Vector.mem_iff_getElem.mpr ⟨2, by decide, rfl⟩

end Sha3.Proofs.Wrapper
