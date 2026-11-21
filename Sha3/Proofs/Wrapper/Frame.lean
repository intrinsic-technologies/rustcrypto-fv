import Sha3.Proofs.Wrapper.Invariant
import Sha3.Proofs.PermutationCall
import Sha3.Proofs.Calls

namespace Sha3.Proofs.Wrapper

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

theorem stack_return_readable {initial : RamState} {budget : Nat}
    (hStack : Stack.Valid initial budget) : MemReadable initial (stackPtr initial) 8 := by
  apply memReadable_of_region hStack.1 hStack.2.1
  · change (initial.regValue .rsp).toNat - budget ≤ (initial.regValue .rsp).toNat
    omega
  · have hu := hStack.2.2.1
    change budget ≤ (initial.regValue .rsp).toNat at hu
    change (initial.regValue .rsp).toNat + 8 ≤
      (initial.regValue .rsp).toNat - budget +
        ((initial.regValue .rsp).toNat + 8 - ((initial.regValue .rsp).toNat - budget))
    omega

theorem validInvocation_returnBoundary_with_options [bindings : Bindings] {initial : RamState}
    {v : Variant} {mode : Mode} {keccak fullState : Bool} {inputs : Array Input} {split : Nat}
    (h : ReadyToStep initial) (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState) :
    nearReturn64Boundary initial = .ok (returnBoundary initial) :=
  nearReturn64Boundary_eq initial h.dataReady h.cpu.ss
    (stack_return_readable hCall.stackAvailable)

theorem validInvocation_returnBoundary [bindings : Bindings] {initial : RamState}
    {v : Variant} {mode : Mode} {inputs : Array Input} {split : Nat}
    (h : ReadyToStep initial) (hCall : ValidInvocation bindings v mode initial inputs split) :
    nearReturn64Boundary initial = .ok (returnBoundary initial) :=
  validInvocation_returnBoundary_with_options h hCall

theorem validInvocation_returnBoundary_bounds [bindings : Bindings] {initial : RamState}
    {v : Variant} {mode : Mode} {keccak fullState : Bool} {inputs : Array Input} {split : Nat}
    (_h : ReadyToStep initial) (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState) :
    (stackTop initial).toNat < 2^32 ∧ ¬ InProgram (returnBoundary initial).rip := by
  obtain ⟨address, hword, hLow, hOutside⟩ := hCall.returnAddress
  have heq := returnBoundary_rip_of_word64At hword
  change (returnBoundary initial).rip.toNat < 2^32 ∧ ¬ InProgram (returnBoundary initial).rip
  rw [heq]
  exact ⟨hLow, hOutside⟩

theorem frameBase_bounds {initial : RamState} {v : Variant} {mode : Mode} {keccak fullState : Bool} {budget : Nat}
    (hStack : Stack.Valid initial budget) (hBudget : (mode.frameSize v keccak fullState) ≤ budget) :
    (Stack.region initial budget).start ≤ (frameBase initial v mode keccak fullState).toNat ∧
      (frameBase initial v mode keccak fullState).toNat + (mode.frameSize v keccak fullState) + 8 ≤
        (Stack.region initial budget).start + (Stack.region initial budget).size := by
  have hMin : budget ≤ (initial.regValue .rsp).toNat := hStack.2.2.1
  have hBase : (frameBase initial v mode keccak fullState).toNat =
      (initial.regValue .rsp).toNat - (mode.frameSize v keccak fullState) :=
    stack_sub_toNat hStack.2.2.1 hBudget
  simp only [hBase, Stack.region, Stack.returnAddressBytes]
  constructor <;> omega

theorem frameAddress_toNat {initial : RamState} {v : Variant} {mode : Mode} {keccak fullState : Bool} {budget offset : Nat}
    (hStack : Stack.Valid initial budget) (hBudget : (mode.frameSize v keccak fullState) ≤ budget)
    (hOffset : offset ≤ (mode.frameSize v keccak fullState) + 8) :
    (frameBase initial v mode keccak fullState + BitVec.ofNat 64 offset).toNat =
      (frameBase initial v mode keccak fullState).toNat + offset := by
  obtain ⟨_, hEnd⟩ := frameBase_bounds hStack hBudget
  have hBound : (Stack.region initial budget).start +
      (Stack.region initial budget).size < 2^32 := hStack.1
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem Invariant.frameReadable [Bindings] {initial s : RamState} {v : Variant} {mode : Mode} {keccak fullState : Bool}
    (h : Invariant initial v mode s keccak fullState)
    (hStack : Stack.Valid initial (mode.entry v keccak fullState).minStackBytes)
    {offset count : Nat} (hRange : offset + count ≤ (mode.frameSize v keccak fullState) + 8) :
    MemReadable s (frameBase initial v mode keccak fullState + BitVec.ofNat 64 offset) count := by
  have hBudget : (mode.frameSize v keccak fullState) ≤ (mode.entry v keccak fullState).minStackBytes := by
    rw [Mode.stackBudget mode v keccak fullState]
    omega
  obtain ⟨hStart, hEnd⟩ := frameBase_bounds hStack hBudget
  have hAddress := frameAddress_toNat hStack hBudget (by omega : offset ≤ (mode.frameSize v keccak fullState) + 8)
  apply memReadable_of_region hStack.1 (h.stackAllocated hStack)
  · rw [hAddress]
    omega
  · rw [hAddress]
    omega

theorem frameAddress_contains {initial : RamState} {v : Variant} {mode : Mode} {keccak fullState : Bool} {budget offset : Nat}
    (hStack : Stack.Valid initial budget) (hBudget : (mode.frameSize v keccak fullState) ≤ budget)
    (hOffset : offset < (mode.frameSize v keccak fullState) + 8) :
    (Stack.region initial budget).Contains
      (frameBase initial v mode keccak fullState + BitVec.ofNat 64 offset).toNat := by
  obtain ⟨hStart, hEnd⟩ := frameBase_bounds hStack hBudget
  rw [frameAddress_toNat hStack hBudget (Nat.le_of_lt hOffset)]
  exact ⟨by omega, by omega⟩

theorem Invariant.of_callResult [bindings : Bindings] {initial s t : RamState}
    {v : Variant} {mode : Mode} {keccak fullState : Bool} {inputs : Array Input} {split : Nat}
    {regions : Vector MemoryRegion n}
    (h : Invariant initial v mode s keccak fullState)
    (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState)
    (hready : ReadyToStep t) (hframe : MemoryWriteFrame s t regions)
    (hcover : ∀ region ∈ regions, ∀ address, region.Contains address →
      ∃ target ∈ writeRegions initial v mode keccak fullState, target.Contains address)
    (hgrows : ∀ address : BitVec 64, (s.external[address]?).isSome →
      (t.external[address]?).isSome)
    (hrest : scalarFrame t = scalarFrame s) : Invariant initial v mode t keccak fullState := by
  have hmemory := memoryWriteFrame_mono hframe hcover
  refine ⟨hready, ?_, SupportedSSE.of_sameControls (SameControls.of_fixedPart (congrArg ScalarFrame.rest hrest)) h.sse,
    memoryWriteFrame_trans h.frame hmemory,
    fun address ha ↦ hgrows address (h.grows address ha), ?_⟩
  · apply programLoaded_of_memoryWriteFrame hmemory _ h.loaded
    intro region hr address ha hp
    exact writeRegions_avoid hCall region hr address ha (.inl hp)
  · exact ⟨(congrArg ScalarFrame.direction hrest).trans h.direction.df⟩

end Sha3.Proofs.Wrapper
