import Sha3.Proofs.Wrapper.Finish.Call
import Sha3.Proofs.Finalize.Contract
import Sha3.Proofs.Finalize.Frame

namespace Sha3.Proofs.Wrapper.Finish

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

theorem finalizeCallPre [bindings : Bindings] {initial s : RamState} {v : Variant} {keccak fullState : Bool}
    {mode : Mode} {inputs : Array Input} {split offset : Nat} {reset : Bool}
    {state : Incremental.State} {out : BitVec 64}
    (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState)
    (hInv : Invariant initial v mode s keccak fullState)
    (hOffset : offset + 201 ≤ (mode.frameSize v keccak fullState) - 8 * mode.pushCount fullState) (hAligned : offset % 8 = 0)
    (hRip : s.RIP = Finalize.entryAddress v reset keccak fullState)
    (hRsp : s.regValue .rsp = frameBase initial v mode keccak fullState - 8)
    (hRdi : s.regValue .rdi = frameBase initial v mode keccak fullState + BitVec.ofNat 64 offset)
    (hRsi : s.regValue .rsi = out)
    (hOut : ValidOutput initial ⟨out.toNat, (v.digestBytes fullState)⟩)
    (hOutputContains : ∀ i < (v.digestBytes fullState), ∃ region ∈ writeRegions initial v mode keccak fullState,
      region.Contains (out + BitVec.ofNat 64 i).toNat)
    (hOutputStack : RangeApart out (v.digestBytes fullState) (Finalize.frameBase s) 304)
    (hOutputState : RangeApart out (v.digestBytes fullState)
      (frameBase initial v mode keccak fullState + BitVec.ofNat 64 offset) 201)
    (hCursor : state.cursor < v.rate)
    (hMetadata : (Operand.mem (frameBase initial v mode keccak fullState + BitVec.ofNat 64 offset + 200) :
      Operand 8).read s = BitVec.ofNat 8 state.cursor)
    (hLanes : Permutation.memoryLanes (frameBase initial v mode keccak fullState + BitVec.ofNat 64 offset) s =
      state.lanes)
    (hTarget : InProgram (stackTop s)) :
    Finalize.CallPre (returnBoundary initial) v reset state s keccak fullState := by
  have hBudget : (mode.frameSize v keccak fullState) ≤ (mode.entry v keccak fullState).minStackBytes := by
    rw [Mode.stackBudget mode v keccak fullState]
    omega
  have hSize : (mode.frameSize v keccak fullState) + 8 + 296 ≤ (mode.entry v keccak fullState).minStackBytes := by
    rw [Mode.stackBudget mode v keccak fullState]
    omega
  have hSize16 : ((mode.frameSize v keccak fullState) + 8) % 16 = 0 := by cases keccak <;> cases fullState <;> cases mode <;> cases v <;> decide +kernel
  have hSp : s.regValue .rsp = initial.regValue .rsp -
      BitVec.ofNat 64 ((mode.frameSize v keccak fullState) + 8) := by
    rw [hRsp, frameBase, BitVec.sub_sub, BitVec.ofNat_add]
    rfl
  have hNested := stackValid_nested hCall.stackAvailable hSize hSize16 hSp hInv.grows
  have hframe : Finalize.frameBase s = frameBase initial v mode keccak fullState - 304 := by
    simp only [Finalize.frameBase, hRsp, BitVec.sub_sub]
    rfl
  refine {
    valid := hCall.fullState_valid
    rip := hRip
    stack := hNested
    stackAvoid := ?_
    stateRead := ?_
    outputRead := ?_
    stateAvoid := ?_
    outputAvoid := ?_
    stateStack := ?_
    outputStack := ?_
    outputState := ?_
    aligned := ?_
    cursor := hCursor
    metadata := by rw [hRdi]; exact hMetadata
    lanes := by rw [hRdi]; exact hLanes
    target := hTarget
    boundary := by
      rw [hRsp, frameBase, BitVec.sub_sub, BitVec.sub_sub]
      apply stackSub_ne_returnBoundary
      cases keccak <;> cases fullState <;> cases mode <;> cases v <;> decide +kernel
    direction := hInv.direction
    resetBoundary := by
      intro _
      rw [hRsp, frameBase, BitVec.sub_sub]
      apply stackSub_ne_returnBoundary
      cases keccak <;> cases fullState <;> cases mode <;> cases v <;> decide +kernel }
  · intro address ha
    exact writeRegions_avoid hCall _ (stack_mem_writeRegions initial v mode keccak fullState) address
      (stackRegion_nested hCall.stackAvailable.2.2.1 hSize hSp ha)
  · rw [hRdi]
    exact hInv.frameReadable hCall.stackAvailable (by omega)
  · rw [hRsi]
    apply memReadable_of_region hOut.2.1 _ (Nat.le_refl _) (Nat.le_refl _)
    intro address ha
    exact Option.isSome_iff_exists.mp
      (hInv.grows address (Option.isSome_iff_exists.mpr (hOut.2.2 address ha)))
  · intro i hi
    rw [hRdi]
    apply writeRegions_avoid hCall _ (stack_mem_writeRegions initial v mode keccak fullState)
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact frameAddress_contains hCall.stackAvailable hBudget (by omega)
  · intro i hi
    rw [hRsi]
    obtain ⟨region, hMember, hContains⟩ := hOutputContains i hi
    exact writeRegions_avoid hCall region hMember _ hContains
  · rw [hRdi, hframe]
    have hPtr : frameBase initial v mode keccak fullState + BitVec.ofNat 64 offset =
        (frameBase initial v mode keccak fullState - 304) + BitVec.ofNat 64 (304 + offset) := by
      rw [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, ← BitVec.add_assoc, BitVec.sub_add_cancel]
    rw [hPtr]
    have hFrameBound : (mode.frameSize v keccak fullState) ≤ 1200 := by cases keccak <;> cases fullState <;> cases mode <;> cases v <;> decide +kernel
    simpa only [BitVec.add_zero] using
      RangeApart.offsets (frameBase initial v mode keccak fullState - 304) (a := 304 + offset) (len := 201)
        (b := 0) (count := 304) (by omega) (by decide) (.inr (by omega))
  · rw [hRsi]
    exact hOutputStack
  · rw [hRsi, hRdi]
    exact hOutputState
  · rw [hRdi, frameAddress_toNat hCall.stackAvailable hBudget (by omega)]
    unfold frameBase
    rw [stack_sub_toNat hCall.stackAvailable.2.2.1 hBudget]
    have hu := hCall.stackAvailable.2.2.1
    have hm := hCall.stackAvailable.2.2.2
    change (mode.entry v keccak fullState).minStackBytes ≤ (initial.regValue .rsp).toNat at hu
    change (initial.regValue .rsp).toNat % 16 = 8 at hm
    cases keccak <;> cases fullState <;> cases mode <;> cases v <;> simp only [Mode.frameSize] at * <;> omega

theorem finalizeWrites_cover {initial s : RamState} {v : Variant} {keccak fullState : Bool} {mode : Mode}
    {offset : Nat} {out : BitVec 64} {regions : Vector MemoryRegion n}
    (hStack : Stack.Valid initial (mode.entry v keccak fullState).minStackBytes)
    (hOffset : offset + 201 ≤ (mode.frameSize v keccak fullState) - 8 * mode.pushCount fullState)
    (hRsp : s.regValue .rsp = frameBase initial v mode keccak fullState - 8)
    (hRdi : s.regValue .rdi = frameBase initial v mode keccak fullState + BitVec.ofNat 64 offset)
    (hRsi : s.regValue .rsi = out)
    (hStackMember : Stack.region initial (mode.entry v keccak fullState).minStackBytes ∈ regions)
    (hMember : (⟨out.toNat, (v.digestBytes fullState)⟩ : MemoryRegion) ∈ regions) :
    ∀ region ∈ Finalize.writeRegions v s fullState, ∀ address, region.Contains address →
      ∃ target ∈ regions, target.Contains address := by
  have hBudget : (mode.frameSize v keccak fullState) ≤ (mode.entry v keccak fullState).minStackBytes := by
    rw [Mode.stackBudget mode v keccak fullState]
    omega
  have hSp : s.regValue .rsp = initial.regValue .rsp -
      BitVec.ofNat 64 ((mode.frameSize v keccak fullState) + 8) := by
    rw [hRsp, frameBase, BitVec.sub_sub, BitVec.ofNat_add]
    rfl
  intro region hr address ha
  obtain ⟨i, hi, rfl⟩ := Vector.mem_iff_getElem.mp hr
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi' with rfl | rfl | rfl
  · refine ⟨_, hStackMember, ?_⟩
    change (Stack.region s 296).Contains address at ha
    exact stackRegion_nested hStack.2.2.1 (by rw [Mode.stackBudget mode v keccak fullState]; omega) hSp ha
  · refine ⟨_, hStackMember, ?_⟩
    change (⟨(s.regValue .rdi).toNat, 201⟩ : MemoryRegion).Contains address at ha
    rw [hRdi, frameAddress_toNat hStack hBudget (by omega)] at ha
    obtain ⟨hLo, hHi⟩ := frameBase_bounds hStack hBudget
    have hf : (frameBase initial v mode keccak fullState).toNat =
        (initial.regValue .rsp).toNat - (mode.frameSize v keccak fullState) :=
      stack_sub_toNat hStack.2.2.1 hBudget
    have hu := hStack.2.2.1
    change (mode.entry v keccak fullState).minStackBytes ≤ (initial.regValue .rsp).toNat at hu
    simp only [MemoryRegion.Contains] at ha ⊢
    rw [hf] at ha
    simp only [Stack.region, Stack.returnAddressBytes]
    constructor <;> omega
  · refine ⟨_, hMember, ?_⟩
    change (⟨(s.regValue .rsi).toNat, (v.digestBytes fullState)⟩ : MemoryRegion).Contains address at ha
    simpa only [hRsi] using ha

theorem finalizeMemory_saved {initial s t : RamState} {v : Variant} {keccak fullState : Bool} {mode : Mode}
    {offset : Nat} {out : BitVec 64}
    (hStack : Stack.Valid initial (mode.entry v keccak fullState).minStackBytes)
    (hOffset : offset + 201 ≤ (mode.frameSize v keccak fullState) - 8 * mode.pushCount fullState)
    (hRsp : s.regValue .rsp = frameBase initial v mode keccak fullState - 8)
    (hRdi : s.regValue .rdi = frameBase initial v mode keccak fullState + BitVec.ofNat 64 offset)
    (hRsi : s.regValue .rsi = out)
    (hApart : (⟨out.toNat, (v.digestBytes fullState)⟩ : MemoryRegion).Disjoint
      (Stack.region initial (mode.entry v keccak fullState).minStackBytes) ∨
      out.toNat + (v.digestBytes fullState) ≤ (initial.regValue .rsp).toNat - 8 * mode.pushCount fullState)
    (hMemory : MemoryWriteFrame s t (Finalize.writeRegions v s fullState))
    (hSaved : Wrapper.SavedFrame initial s mode fullState) : Wrapper.SavedFrame initial t mode fullState := by
  have hBudget : (mode.frameSize v keccak fullState) ≤ (mode.entry v keccak fullState).minStackBytes := by
    rw [Mode.stackBudget mode v keccak fullState]
    omega
  have hFrameSize : 8 * mode.pushCount fullState ≤ (mode.frameSize v keccak fullState) := by cases keccak <;> cases fullState <;> cases mode <;> cases v <;> decide +kernel
  have hUnder : (mode.entry v keccak fullState).minStackBytes ≤ (initial.regValue .rsp).toNat := hStack.2.2.1
  have hLow : (initial.regValue .rsp).toNat + 8 < 2^32 := by
    have hb := hStack.1
    simp only [Stack.region, Stack.returnAddressBytes, MemoryRegion.Bounded,
      userAddressLimit] at hb
    omega
  have hSpNat : (s.regValue .rsp).toNat = (initial.regValue .rsp).toNat - ((mode.frameSize v keccak fullState) + 8) := by
    rw [hRsp, frameBase, BitVec.sub_sub]
    rw [show BitVec.ofNat 64 (mode.frameSize v keccak fullState) + 8 = BitVec.ofNat 64 ((mode.frameSize v keccak fullState) + 8) by
      rw [BitVec.ofNat_add]; rfl]
    exact stack_sub_toNat hStack.2.2.1 (by rw [Mode.stackBudget mode v keccak fullState]; omega)
  have hStateNat : (s.regValue .rdi).toNat =
      (initial.regValue .rsp).toNat - (mode.frameSize v keccak fullState) + offset := by
    rw [hRdi, frameAddress_toNat hStack hBudget (by omega)]
    rw [show (frameBase initial v mode keccak fullState).toNat =
      (initial.regValue .rsp).toNat - (mode.frameSize v keccak fullState) from
      stack_sub_toNat hStack.2.2.1 hBudget]
  have hBytes : ∀ j < 8 * mode.pushCount fullState + 8,
      t.external[initial.regValue .rsp - BitVec.ofNat 64 (8 * mode.pushCount fullState) + BitVec.ofNat 64 j]? =
        s.external[initial.regValue .rsp - BitVec.ofNat 64 (8 * mode.pushCount fullState) + BitVec.ofNat 64 j]? := by
    intro j hj
    apply hMemory
    intro region hr ha
    have hAddr : (initial.regValue .rsp - BitVec.ofNat 64 (8 * mode.pushCount fullState) + BitVec.ofNat 64 j).toNat =
        (initial.regValue .rsp).toNat - 8 * mode.pushCount fullState + j := by
      rw [BitVec.toNat_add,
        stack_sub_toNat hStack.2.2.1 (by omega), BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    obtain ⟨i, hi, rfl⟩ := Vector.mem_iff_getElem.mp hr
    have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hi' with rfl | rfl | rfl
    · change (Stack.region s 296).Contains _ at ha
      simp only [Stack.region, Stack.returnAddressBytes, MemoryRegion.Contains, hSpNat,
        hAddr] at ha
      have hSize : (mode.frameSize v keccak fullState) + 304 ≤ (mode.entry v keccak fullState).minStackBytes := by
        rw [Mode.stackBudget mode v keccak fullState]
        omega
      omega
    · change (⟨(s.regValue .rdi).toNat, 201⟩ : MemoryRegion).Contains _ at ha
      simp only [MemoryRegion.Contains, hStateNat, hAddr] at ha
      omega
    · change (⟨(s.regValue .rsi).toNat, (v.digestBytes fullState)⟩ : MemoryRegion).Contains _ at ha
      rw [hRsi] at ha
      rcases hApart with hApart | hBelow
      · apply hApart _ ha
        simp only [Stack.region, Stack.returnAddressBytes, MemoryRegion.Contains, hAddr]
        constructor <;> omega
      · simp only [MemoryRegion.Contains, hAddr] at ha
        omega
  constructor
  · intro i
    rw [← hSaved.saved i]
    apply memLoad_congr
    intro j hj
    apply congrArg (fun x : Option UInt8 ↦ x.getD 0)
    change t.external[initial.regValue .rsp - BitVec.ofNat 64 (8 * mode.pushCount fullState) + BitVec.ofNat 64 (8 * i.val) +
        BitVec.ofNat 64 j]? = s.external[_]?
    simp only [Mode.savedBytes, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact hBytes (8 * i.val + j) (by have := i.isLt; omega)
  · rw [← hSaved.returnSlot]
    apply memLoad_congr
    intro j hj
    apply congrArg (fun x : Option UInt8 ↦ x.getD 0)
    have he : initial.regValue .rsp + BitVec.ofNat 64 j =
        initial.regValue .rsp - BitVec.ofNat 64 (8 * mode.pushCount fullState) + BitVec.ofNat 64 (8 * mode.pushCount fullState + j) := by
      rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]
    change t.external[initial.regValue .rsp + BitVec.ofNat 64 j]? = s.external[_]?
    rw [he]
    exact hBytes _ (by omega)

end Sha3.Proofs.Wrapper.Finish
