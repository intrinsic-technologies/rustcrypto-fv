import Sha3.Proofs.Wrapper.Layout
import Sha3.Proofs.Machine
import Sha3.Proofs.Outcome
import Sha3.Proofs.Run

namespace Sha3.Proofs.Wrapper

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

structure Invariant [Bindings] (initial : RamState) (v : Variant) (mode : Mode)
    (s : RamState) (keccak : Bool := false) (fullState : Bool := false) : Prop where
  ready : ReadyToStep s
  loaded : ProgramLoaded s
  sse : SupportedSSE Bindings.processor s
  frame : MemoryWriteFrame initial s (writeRegions initial v mode keccak fullState)
  grows : ∀ address : BitVec 64, (initial.external[address]?).isSome →
    (s.external[address]?).isSome
  direction : DirectionFlagUnset s

theorem Invariant.initial [bindings : Bindings] {s : RamState} {v : Variant} {mode : Mode}
    {inputs : Array Input} {split : Nat} {keccak fullState : Bool}
    (hMachine : SupportedIntegerMachineState bindings.processor s)
    (hEnvironment : MachineRamUnitStrideDecodable bindings s)
    (hCall : ValidInvocation bindings v mode s inputs split keccak fullState) : Invariant s v mode s keccak fullState :=
  ⟨machineRamUnitStrideDecodable_readyToStep hMachine hEnvironment, hCall.programLoaded,
    hMachine.sse, memoryWriteFrame_refl _ _, fun _ h ↦ h, hCall.directionFlagUnset⟩

theorem writeRegions_avoid [bindings : Bindings] {initial : RamState} {v : Variant}
    {mode : Mode} {inputs : Array Input} {split : Nat} {keccak fullState : Bool}
    (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState) :
    ∀ region ∈ writeRegions initial v mode keccak fullState,
      region.Avoids (fun address ↦ InProgram address ∨ InPageTables address) := by
  intro region hr
  exact (hCall.separation.2 region hr).2

theorem Invariant.of_agreesExcept [bindings : Bindings] {initial s t : RamState}
    {v : Variant} {mode : Mode} {inputs : Array Input} {split : Nat} {keccak fullState : Bool}
    {components : List Component}
    (h : Invariant initial v mode s keccak fullState)
    (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState)
    (hready : ReadyToStep t) (hframe : AgreesExcept components s t)
    (hwrites : WritesWithin components (writeRegions initial v mode keccak fullState))
    (hd : .df ∉ components := by first | rfl | decide | simp (config := { decide := true }) [x86_compose]) :
    Invariant initial v mode t keccak fullState := by
  have hmemory := hframe.memoryWriteFrame hwrites
  refine ⟨hready, ?_, SupportedSSE.of_agreesExcept hframe h.sse,
    memoryWriteFrame_trans h.frame hmemory,
    fun address ha ↦ hframe.grow address (h.grows address ha),
    hframe.directionFlagClear h.direction hd⟩
  apply programLoaded_of_memoryWriteFrame hmemory _ h.loaded
  intro region hr address ha hp
  exact writeRegions_avoid hCall region hr address ha (.inl hp)

theorem Invariant.code [Bindings] {initial s : RamState} {v : Variant} {mode : Mode} {keccak fullState : Bool}
    (h : Invariant initial v mode s keccak fullState) : CodeIn Extracted.programImage s :=
  CodeIn.of_loaded h.loaded (SectionsLow.codeLow programSections_low)

theorem Invariant.stackAllocated [Bindings] {initial s : RamState} {v : Variant} {mode : Mode} {keccak fullState : Bool}
    (h : Invariant initial v mode s keccak fullState) (hStack : Stack.Valid initial (mode.entry v keccak fullState).minStackBytes) :
    (Stack.region initial (mode.entry v keccak fullState).minStackBytes).Allocated s.external := by
  intro address ha
  exact Option.isSome_iff_exists.mp
    (h.grows address (Option.isSome_iff_exists.mpr (hStack.2.1 address ha)))

end Sha3.Proofs.Wrapper
