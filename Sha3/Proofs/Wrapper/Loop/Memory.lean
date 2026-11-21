import X86Proofs.Program.Compose
import Sha3.Proofs.Wrapper.Loop.Context
import Sha3.Proofs.Wrapper.Frame
import Sha3.Proofs.InputSlices
import Sha3.Proofs.PermutationCall

namespace Sha3.Proofs.Wrapper.Loop

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

variable {keccak fullState : Bool}

theorem stackBase_toNat {initial : RamState} {v : Variant} {kind : Kind}
    (hStack : Stack.Valid initial (kind.mode.entry v (keccak := keccak) (fullState := fullState)).minStackBytes) :
    (stackBase (keccak := keccak) (fullState := fullState) initial v kind).toNat =
      (initial.regValue .rsp).toNat - ((kind.mode.frameSize v (_keccak := keccak) (fullState := fullState)) + 336) := by
  change (initial.regValue .rsp - BitVec.ofNat 64 (kind.mode.frameSize v (_keccak := keccak) (fullState := fullState)) - 336).toNat = _
  rw [BitVec.sub_sub, show (336 : BitVec 64) = BitVec.ofNat 64 336 from rfl,
    ← BitVec.ofNat_add]
  exact stack_sub_toNat hStack.2.2.1 (by rw [(Mode.stackBudget _ _ keccak fullState)]; omega)

theorem statePointer_toNat {initial : RamState} {v : Variant} {kind : Kind}
    (hStack : Stack.Valid initial (kind.mode.entry v (keccak := keccak) (fullState := fullState)).minStackBytes) :
    (statePointer (keccak := keccak) (fullState := fullState) initial v kind.mode).toNat =
      (initial.regValue .rsp).toNat - (kind.mode.frameSize v (_keccak := keccak) (fullState := fullState)) + (kind.mode.stateOffset v (_keccak := keccak) (fullState := fullState)) := by
  rw [statePointer, frameAddress_toNat hStack (by rw [(Mode.stackBudget _ _ keccak fullState)]; omega)
    (by cases fullState <;> cases keccak <;> cases kind <;> cases v <;> decide)]
  rw [show (frameBase (keccak := keccak) (fullState := fullState) initial v kind.mode).toNat =
    (initial.regValue .rsp).toNat - (kind.mode.frameSize v (_keccak := keccak) (fullState := fullState)) from
      stack_sub_toNat hStack.2.2.1 (by rw [(Mode.stackBudget _ _ keccak fullState)]; omega)]

theorem writeRegions_bounds {initial : RamState} {v : Variant} {kind : Kind}
    (hStack : Stack.Valid initial (kind.mode.entry v (keccak := keccak) (fullState := fullState)).minStackBytes)
    {region : MemoryRegion} (hr : region ∈ writeRegions (keccak := keccak) (fullState := fullState) initial v kind) :
    (Stack.region initial (kind.mode.entry v (keccak := keccak) (fullState := fullState)).minStackBytes).start ≤ region.start ∧
      region.start + region.size ≤ (initial.regValue .rsp).toNat - 48 := by
  have hmin := hStack.2.2.1
  change (kind.mode.entry v (keccak := keccak) (fullState := fullState)).minStackBytes ≤ (initial.regValue .rsp).toNat at hmin
  rw [(Mode.stackBudget _ _ keccak fullState)] at hmin
  have hs := stackBase_toNat hStack
  have hp := statePointer_toNat hStack
  have hm : (kind.mode.stateOffset v (_keccak := keccak) (fullState := fullState)) + 249 ≤ (kind.mode.frameSize v (_keccak := keccak) (fullState := fullState)) := by
    cases fullState <;> cases keccak <;> cases kind <;> cases v <;> decide
  have hf : 48 ≤ (kind.mode.frameSize v (_keccak := keccak) (fullState := fullState)) := by cases fullState <;> cases keccak <;> cases kind <;> cases v <;> decide
  simp only [writeRegions, Vector.mem_mk, List.mem_toArray, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · simp only [Stack.region, (Mode.stackBudget _ _ keccak fullState), hs]
    constructor <;> omega
  · simp only [Stack.region, (Mode.stackBudget _ _ keccak fullState), hp]
    constructor <;> omega

theorem writeRegions_contains_stack {initial : RamState} {v : Variant} {kind : Kind}
    (hStack : Stack.Valid initial (kind.mode.entry v (keccak := keccak) (fullState := fullState)).minStackBytes)
    {region : MemoryRegion} (hr : region ∈ writeRegions (keccak := keccak) (fullState := fullState) initial v kind)
    {address : Nat} (ha : region.Contains address) :
    (Stack.region initial (kind.mode.entry v (keccak := keccak) (fullState := fullState)).minStackBytes).Contains address := by
  obtain ⟨hlo, hhi⟩ := writeRegions_bounds hStack hr
  have hmin := hStack.2.2.1
  change (kind.mode.entry v (keccak := keccak) (fullState := fullState)).minStackBytes ≤ (initial.regValue .rsp).toNat at hmin
  simp only [MemoryRegion.Contains] at ha ⊢
  refine ⟨Nat.le_trans hlo ha.1, ?_⟩
  simp only [Stack.region, Stack.returnAddressBytes]
  omega

theorem writeRegions_subset_outer {initial : RamState} {v : Variant} {kind : Kind}
    (hStack : Stack.Valid initial (kind.mode.entry v (keccak := keccak) (fullState := fullState)).minStackBytes) :
    ∀ region ∈ writeRegions (keccak := keccak) (fullState := fullState) initial v kind, ∀ address, region.Contains address →
      ∃ target ∈ Wrapper.writeRegions (keccak := keccak) (fullState := fullState) initial v kind.mode, target.Contains address := by
  intro region hr address ha
  exact ⟨_, stack_mem_writeRegions (keccak := keccak) (fullState := fullState) initial v kind.mode, writeRegions_contains_stack hStack hr ha⟩

theorem writeRegions_avoid [bindings : Bindings] {initial : RamState} {v : Variant}
    {kind : Kind} {inputs : Array Input} {split : Nat}
    (hCall : ValidInvocation (keccak := keccak) (fullState := fullState) bindings v kind.mode initial inputs split) :
    ∀ region ∈ writeRegions (keccak := keccak) (fullState := fullState) initial v kind,
      region.Avoids (fun address ↦ InProgram address ∨ InPageTables address) := by
  intro region hr address ha
  exact Wrapper.writeRegions_avoid hCall _ (stack_mem_writeRegions (keccak := keccak) (fullState := fullState) initial v kind.mode)
    address (writeRegions_contains_stack hCall.stackAvailable hr ha)

theorem clobbers_writesWithin {initial : RamState} {v : Variant} {kind : Kind}
    (hStack : Stack.Valid initial (kind.mode.entry v (keccak := keccak) (fullState := fullState)).minStackBytes) :
    WritesWithin (clobbers (keccak := keccak) (fullState := fullState) initial v kind) (writeRegions (keccak := keccak) (fullState := fullState) initial v kind) := by
  have hmin := hStack.2.2.1
  change (kind.mode.entry v (keccak := keccak) (fullState := fullState)).minStackBytes ≤ (initial.regValue .rsp).toNat at hmin
  rw [(Mode.stackBudget _ _ keccak fullState)] at hmin
  have hmax := (initial.regValue .rsp).isLt
  have hs := stackBase_toNat hStack
  have hp := statePointer_toNat hStack
  have hm : (kind.mode.stateOffset v (_keccak := keccak) (fullState := fullState)) + 201 ≤ (kind.mode.frameSize v (_keccak := keccak) (fullState := fullState)) := by
    cases fullState <;> cases keccak <;> cases kind <;> cases v <;> decide
  intro c hc address hcover
  simp only [clobbers, List.mem_append] at hc
  rcases hc with hc | hc
  case inr => exact (extraClobbers_no_memory c hc address hcover).elim
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcover.elim
  · obtain ⟨i, hi, rfl⟩ := hcover
    refine ⟨⟨(stackBase (keccak := keccak) (fullState := fullState) initial v kind).toNat, 336⟩,
      Vector.mem_iff_getElem.mpr ⟨0, by decide, rfl⟩, ?_⟩
    simp only [MemoryRegion.Contains, BitVec.toNat_add, BitVec.toNat_ofNat, hs]
    constructor <;> omega
  · obtain ⟨i, hi, rfl⟩ := hcover
    refine ⟨⟨(statePointer (keccak := keccak) (fullState := fullState) initial v kind.mode).toNat, 201⟩,
      Vector.mem_iff_getElem.mpr ⟨1, by decide, rfl⟩, ?_⟩
    simp only [MemoryRegion.Contains, BitVec.toNat_add, BitVec.toNat_ofNat, hp]
    constructor <;> omega

theorem clobbers_writesWithin_outer {initial : RamState} {v : Variant} {kind : Kind}
    (hStack : Stack.Valid initial (kind.mode.entry v (keccak := keccak) (fullState := fullState)).minStackBytes) :
    WritesWithin (clobbers (keccak := keccak) (fullState := fullState) initial v kind) (Wrapper.writeRegions (keccak := keccak) (fullState := fullState) initial v kind.mode) := by
  intro c hc address ha
  obtain ⟨region, hr, hm⟩ := clobbers_writesWithin hStack c hc address ha
  exact writeRegions_subset_outer hStack region hr address.toNat hm

theorem state_stack_apart (initial : RamState) (v : Variant) (kind : Kind) :
    RangeApart (statePointer (keccak := keccak) (fullState := fullState) initial v kind.mode) 201 (stackBase (keccak := keccak) (fullState := fullState) initial v kind) 344 := by
  have hp : statePointer (keccak := keccak) (fullState := fullState) initial v kind.mode =
      stackBase (keccak := keccak) (fullState := fullState) initial v kind + BitVec.ofNat 64 (336 + (kind.mode.stateOffset v (_keccak := keccak) (fullState := fullState))) := by
    simp only [stackBase, statePointer, BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, ← BitVec.add_assoc,
      BitVec.sub_add_cancel]
  rw [hp]
  have ha : 336 + (kind.mode.stateOffset v (_keccak := keccak) (fullState := fullState)) + 201 ≤ 2 ^ 64 := by cases fullState <;> cases keccak <;> cases kind <;> cases v <;> decide
  have hb : 344 ≤ 336 + (kind.mode.stateOffset v (_keccak := keccak) (fullState := fullState)) := by cases fullState <;> cases keccak <;> cases kind <;> cases v <;> decide
  simpa only [BitVec.add_zero] using
    RangeApart.offsets (stackBase (keccak := keccak) (fullState := fullState) initial v kind) (a := 336 + (kind.mode.stateOffset v (_keccak := keccak) (fullState := fullState)))
      (len := 201) (b := 0) (count := 344) ha (by decide) (.inr hb)

theorem update_stackBase {initial called : RamState} {v : Variant} {kind : Kind}
    (hsp : called.regValue .rsp = frameBase (keccak := keccak) (fullState := fullState) initial v kind.mode - 8) :
    Update.stackBase called = stackBase (keccak := keccak) (fullState := fullState) initial v kind := by
  simp only [Update.stackBase, hsp, stackBase, BitVec.sub_sub]
  rfl

theorem update_writeRegions_subset {initial called : RamState} {v : Variant} {kind : Kind}
    (hsp : called.regValue .rsp = frameBase (keccak := keccak) (fullState := fullState) initial v kind.mode - 8)
    (hp : called.regValue .rsi = statePointer (keccak := keccak) (fullState := fullState) initial v kind.mode) :
    ∀ region ∈ Update.writeRegions called, ∀ address, region.Contains address →
      ∃ target ∈ writeRegions (keccak := keccak) (fullState := fullState) initial v kind, target.Contains address := by
  intro region hr address ha
  simp only [Update.writeRegions, Vector.mem_mk, List.mem_toArray, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · refine ⟨⟨(stackBase (keccak := keccak) (fullState := fullState) initial v kind).toNat, 336⟩,
      Vector.mem_iff_getElem.mpr ⟨0, by decide, rfl⟩, ?_⟩
    simp only [update_stackBase hsp, Update.stackBytes, MemoryRegion.Contains] at ha ⊢
    constructor <;> omega
  · refine ⟨⟨(statePointer (keccak := keccak) (fullState := fullState) initial v kind.mode).toNat, 201⟩,
      Vector.mem_iff_getElem.mpr ⟨1, by decide, rfl⟩, ?_⟩
    simpa only [Update.stateRegion, hp] using ha

theorem update_stackValid {initial called : RamState} {v : Variant} {kind : Kind}
    (hStack : Stack.Valid initial (kind.mode.entry v (keccak := keccak) (fullState := fullState)).minStackBytes)
    (hsp : called.regValue .rsp = frameBase (keccak := keccak) (fullState := fullState) initial v kind.mode - 8)
    (hgrows : ∀ address : BitVec 64, (initial.external[address]?).isSome →
      (called.external[address]?).isSome) : Stack.Valid called Update.stackBytes := by
  apply stackValid_nested hStack (offset := (kind.mode.frameSize v (_keccak := keccak) (fullState := fullState)) + 8)
  · rw [(Mode.stackBudget _ _ keccak fullState)]
    exact Nat.add_le_add_left (by decide : 8 + Update.stackBytes ≤ 464) _
  · cases fullState <;> cases keccak <;> cases kind <;> cases v <;> decide
  · rw [hsp, frameBase, BitVec.sub_sub, BitVec.ofNat_add]
    rfl
  · exact hgrows

theorem savedFrame_of_memoryWriteFrame {initial s t : RamState} {mode : Mode}
    {savedFullState : Bool} {budget n : Nat} {regions : Vector MemoryRegion n}
    (h : SavedFrame initial s mode savedFullState)
    (hStack : Stack.Valid initial budget)
    (hframe : MemoryWriteFrame s t regions)
    (hFits : mode.savedBytes savedFullState ≤ budget)
    (hbounds : ∀ region ∈ regions, region.start + region.size ≤
      (initial.regValue .rsp).toNat - mode.savedBytes savedFullState) :
    SavedFrame initial t mode savedFullState := by
  have hmin := hStack.2.2.1
  change budget ≤ (initial.regValue .rsp).toNat at hmin
  have hmax := hStack.1
  simp only [Stack.region, Stack.returnAddressBytes, MemoryRegion.Bounded,
    userAddressLimit] at hmax
  have hcount : mode.pushCount savedFullState ≤ 6 := by
    cases mode <;> cases savedFullState <;> decide
  have hsize : mode.savedBytes savedFullState = 8 * mode.pushCount savedFullState := rfl
  constructor
  · intro i
    refine Eq.trans ?_ (h.saved i)
    apply memLoad_congr
    intro j hj
    apply congrArg (fun x : Option UInt8 ↦ x.getD 0)
    apply hframe
    intro region hr ha
    have hh := hbounds region hr
    have hi := i.isLt
    have hs : (initial.regValue .rsp - BitVec.ofNat 64 (mode.savedBytes savedFullState)).toNat =
        (initial.regValue .rsp).toNat - mode.savedBytes savedFullState :=
      stack_sub_toNat hStack.2.2.1 hFits
    simp only [MemoryRegion.Contains, BitVec.toNat_add, BitVec.toNat_ofNat, hs] at ha
    omega
  · refine Eq.trans ?_ h.returnSlot
    apply memLoad_congr
    intro j hj
    apply congrArg (fun x : Option UInt8 ↦ x.getD 0)
    apply hframe
    intro region hr ha
    have hh := hbounds region hr
    simp only [MemoryRegion.Contains, BitVec.toNat_add, BitVec.toNat_ofNat] at ha
    omega

theorem input_apart [bindings : Bindings] {initial : RamState} {v : Variant}
    {kind : Kind} {inputs : Array Input} {split : Nat}
    (hCall : ValidInvocation (keccak := keccak) (fullState := fullState) bindings v kind.mode initial inputs split) (i : Fin inputs.size) :
    ∀ region ∈ writeRegions (keccak := keccak) (fullState := fullState) initial v kind, inputs[i].region.Disjoint region := by
  intro region hr address ha hb
  have hread : inputs[i].region ∈ readRegions initial inputs := by
    simp only [readRegions, List.mem_cons, Array.mem_toList_iff]
    exact Or.inr (Or.inr (Array.mem_map.mpr ⟨inputs[i], Array.getElem_mem _, rfl⟩))
  exact ((hCall.sliceSeparation kind.mode_ne_digest).2 _ (stack_mem_writeRegions (keccak := keccak) (fullState := fullState) initial v kind.mode)).1 _ hread
    address ha (writeRegions_contains_stack hCall.stackAvailable hr hb)

theorem input_bytes [bindings : Bindings] {initial s : RamState} {v : Variant}
    {kind : Kind} {inputs : Array Input} {split : Nat}
    (hCall : ValidInvocation (keccak := keccak) (fullState := fullState) bindings v kind.mode initial inputs split)
    (hInv : Invariant (keccak := keccak) (fullState := fullState) initial v kind.mode s) (i : Fin inputs.size) :
    Bytes s.external inputs[i].address inputs[i].bytes.size
      (fun j ↦ (inputs[i].bytes.data[j]?).getD 0) := by
  have hb := input_hasBytes_of_memoryWriteFrame ((hCall.inputSlices kind.mode_ne_digest).inputsInMemory i)
    (hCall.sliceSeparation kind.mode_ne_digest) hInv.frame
  intro j hj
  have he := hb.2 ⟨j, hj⟩
  simpa only [Input.region, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    Array.getElem?_eq_getElem hj, Option.getD_some, ByteArray.getElem_eq_getElem_data] using he

theorem input_readable [bindings : Bindings] {initial s : RamState} {v : Variant}
    {kind : Kind} {inputs : Array Input} {split : Nat}
    (hCall : ValidInvocation (keccak := keccak) (fullState := fullState) bindings v kind.mode initial inputs split)
    (hInv : Invariant (keccak := keccak) (fullState := fullState) initial v kind.mode s) (i : Fin inputs.size) :
    MemReadable s inputs[i].address inputs[i].bytes.size := by
  apply (input_bytes hCall hInv i).readable
  have hb := ((hCall.inputSlices kind.mode_ne_digest).inputsInMemory i).2.2.2.1
  exact Nat.le_of_lt hb

theorem state_readable [Bindings] {initial s : RamState} {v : Variant} {kind : Kind}
    (hStack : Stack.Valid initial (kind.mode.entry v (keccak := keccak) (fullState := fullState)).minStackBytes)
    (hInv : Invariant (keccak := keccak) (fullState := fullState) initial v kind.mode s) :
    MemReadable s (statePointer (keccak := keccak) (fullState := fullState) initial v kind.mode) 201 :=
  hInv.frameReadable hStack (by cases fullState <;> cases keccak <;> cases kind <;> cases v <;> decide)

theorem update_writeRegions_bounds {initial called : RamState} {v : Variant} {mode : Mode}
    (hStack : Stack.Valid initial (mode.entry v keccak fullState).minStackBytes)
    (hsp : called.regValue .rsp = frameBase initial v mode keccak fullState - 8)
    (hptr : called.regValue .rsi = statePointer initial v mode keccak fullState)
    {region : MemoryRegion} (hr : region ∈ Update.writeRegions called) :
    (Stack.region initial (mode.entry v keccak fullState).minStackBytes).start ≤ region.start ∧
      region.start + region.size ≤ (initial.regValue .rsp).toNat - mode.savedBytes fullState := by
  have hmin := hStack.2.2.1
  change (mode.entry v keccak fullState).minStackBytes ≤ (initial.regValue .rsp).toNat at hmin
  rw [Mode.stackBudget mode v keccak fullState] at hmin
  have hbudget : mode.frameSize v keccak fullState ≤ (mode.entry v keccak fullState).minStackBytes := by
    rw [Mode.stackBudget mode v keccak fullState]; omega
  have hs : (Update.stackBase called).toNat =
      (initial.regValue .rsp).toNat - (mode.frameSize v keccak fullState + 336) := by
    simp only [Update.stackBase, hsp, frameBase, BitVec.sub_sub]
    rw [BitVec.add_assoc]
    change (initial.regValue .rsp - (BitVec.ofNat 64 (mode.frameSize v keccak fullState) + BitVec.ofNat 64 336)).toNat = _
    rw [← BitVec.ofNat_add]
    exact stack_sub_toNat hStack.2.2.1 (by rw [Mode.stackBudget mode v keccak fullState]; omega)
  have hp := frameAddress_toNat hStack hbudget
    (offset := mode.stateOffset v keccak fullState)
    (by cases keccak <;> cases mode <;> cases v <;> cases fullState <;> decide)
  have hb : (frameBase initial v mode keccak fullState).toNat =
      (initial.regValue .rsp).toNat - mode.frameSize v keccak fullState :=
    stack_sub_toNat hStack.2.2.1 hbudget
  have hm : mode.stateOffset v keccak fullState + 201 + mode.savedBytes fullState ≤ mode.frameSize v keccak fullState := by
    cases keccak <;> cases mode <;> cases v <;> cases fullState <;> decide
  have hf : mode.savedBytes fullState ≤ mode.frameSize v keccak fullState := by omega
  simp only [Update.writeRegions, Vector.mem_mk, List.mem_toArray, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · simp only [Update.stackBytes, hs, Stack.region, Mode.stackBudget mode v keccak fullState]
    constructor <;> omega
  · simp only [Update.stateRegion, hptr, statePointer, hp, hb, Stack.region,
      Mode.stackBudget mode v keccak fullState]
    constructor <;> omega

theorem update_writeRegions_subset_outer {initial called : RamState} {v : Variant} {mode : Mode}
    (hStack : Stack.Valid initial (mode.entry v keccak fullState).minStackBytes)
    (hsp : called.regValue .rsp = frameBase initial v mode keccak fullState - 8)
    (hptr : called.regValue .rsi = statePointer initial v mode keccak fullState) :
    ∀ region ∈ Update.writeRegions called, ∀ address, region.Contains address →
      ∃ target ∈ Wrapper.writeRegions initial v mode keccak fullState, target.Contains address := by
  intro region hr address ha
  refine ⟨_, stack_mem_writeRegions initial v mode keccak fullState, ?_⟩
  obtain ⟨hlo, hhi⟩ := update_writeRegions_bounds hStack hsp hptr hr
  have hmin := hStack.2.2.1
  change (mode.entry v keccak fullState).minStackBytes ≤ (initial.regValue .rsp).toNat at hmin
  simp only [MemoryRegion.Contains, Stack.region, Stack.returnAddressBytes] at ha hlo ⊢
  constructor <;> omega

theorem update_callContext [bindings : Bindings] {initial called : RamState}
    {v : Variant} {kind : Kind} {mode : Mode} {inputs : Array Input} {split : Nat}
    {state : Incremental.State} (input : Input)
    (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState)
    (hInv : Invariant initial v mode called keccak fullState)
    (hInput : ValidInput initial input.region input.bytes)
    (hRead : input.region ∈ invocationReadRegions initial inputs mode)
    (hRegs : UpdateEntryRegisters initial v kind input called keccak fullState mode)
    (hRip : called.RIP = v.updateAddress)
    (hState : Update.StateAt (statePointer initial v mode keccak fullState) state called)
    (hCursor : state.cursor < v.rate) (hTarget : InProgram (stackTop called)) :
    Update.CallContext v called input.bytes state := by
  have hStack := hCall.stackAvailable
  have hbytes : Bytes called.external input.address input.bytes.size
      (fun j ↦ (input.bytes.data[j]?).getD 0) := by
    have hh := hasBytes_of_memoryWriteFrame hInv.frame hInput.2.2
      (by have hh := hInput.2.1; change input.address.toNat + input.bytes.size < 2^32 at hh;
          change input.address.toNat + input.bytes.size ≤ 2^64; omega)
      (fun target ht ↦ (hCall.separation.2 target ht).1 _ hRead)
    intro j hj
    have he := hh.2 ⟨j, hj⟩
    simpa only [Input.region, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      Array.getElem?_eq_getElem hj, Option.getD_some, ByteArray.getElem_eq_getElem_data] using he
  refine ⟨hRip, hInv.ready, hInv.loaded, ?_, ?_, ?_, ?_, hRegs.length,
    (by rw [hRegs.cursor, hRegs.pointer]), hCursor, ?_, ?_, ?_, ?_, hTarget⟩
  · apply stackValid_nested hStack (offset := mode.frameSize v keccak fullState + 8)
    · rw [Mode.stackBudget mode v keccak fullState]
      exact Nat.add_le_add_left (by decide : 8 + Update.stackBytes ≤ 464) _
    · cases keccak <;> cases mode <;> cases v <;> cases fullState <;> decide
    · rw [hRegs.stack, frameBase, BitVec.sub_sub, BitVec.ofNat_add]; rfl
    · exact hInv.grows
  · rw [hRegs.pointer]
    exact hInv.frameReadable hStack (by cases keccak <;> cases mode <;> cases v <;> cases fullState <;> decide)
  · rw [hRegs.input]
    apply hbytes.readable
    have hh := hInput.2.1
    change input.address.toNat + input.bytes.size < 2^32 at hh
    omega
  · rw [hRegs.input]; exact hbytes
  · rw [hRegs.pointer]; exact hState
  · have he : statePointer initial v mode keccak fullState = Update.stackBase called +
        BitVec.ofNat 64 (336 + mode.stateOffset v keccak fullState) := by
      simp only [Update.stackBase, hRegs.stack, statePointer, BitVec.ofNat_add,
        BitVec.ofNat_eq_ofNat, ← BitVec.add_assoc, BitVec.sub_sub]
      rw [show (8#64 + 328#64) = 336#64 from rfl, BitVec.sub_add_cancel]
    rw [hRegs.pointer, he]
    simpa only [BitVec.add_zero] using
      RangeApart.offsets (Update.stackBase called) (a := 336 + mode.stateOffset v keccak fullState)
        (len := 201) (b := 0) (count := 336)
        (by cases keccak <;> cases mode <;> cases v <;> cases fullState <;> decide) (by decide) (.inr (by omega))
  · intro region hr address ha hh
    rw [hRegs.input] at ha
    obtain ⟨target, ht, hcontains⟩ :=
      update_writeRegions_subset_outer hStack hRegs.stack hRegs.pointer region hr address hh
    exact (hCall.separation.2 target ht).1 _ hRead address ha hcontains
  · intro region hr address ha
    obtain ⟨target, ht, hcontains⟩ :=
      update_writeRegions_subset_outer hStack hRegs.stack hRegs.pointer region hr address.toNat ha
    exact Wrapper.writeRegions_avoid hCall target ht address hcontains

theorem slot_avoids {initial : RamState} {v : Variant} {kind : Loop.Kind} {offset : Nat}
    (hslot : offset + 8 ≤ (kind.mode.stateOffset v (_keccak := keccak) (fullState := fullState))) :
    ∀ j, j < 8 → ∀ c ∈ Loop.clobbers (keccak := keccak) (fullState := fullState) initial v kind,
      ¬ c.Covers (frameBase (keccak := keccak) (fullState := fullState) initial v kind.mode + BitVec.ofNat 64 offset + BitVec.ofNat 64 j) := by
  have hsmall : offset < 297 := by
    have hmax : (kind.mode.stateOffset v (_keccak := keccak) (fullState := fullState)) ≤ 296 := by cases fullState <;> cases keccak <;> cases kind <;> cases v <;> decide
    omega
  intro j hj
  intro c hc hcover
  simp only [Loop.clobbers, List.mem_append] at hc
  rcases hc with hc | hc
  case inr => exact Loop.extraClobbers_no_memory c hc _ hcover
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcover.elim
  · obtain ⟨i, hi, he⟩ := hcover
    have apart := (by unfold OffsetsApart; decide +kernel : ∀ o : Fin 297,
      OffsetsApart (-(336 : BitVec 64)) 336 (BitVec.ofNat 64 o.val) 8) ⟨offset, hsmall⟩
    apply apart.ne (frameBase (keccak := keccak) (fullState := fullState) initial v kind.mode) hi hj (by decide)
    simpa only [Loop.stackBase, BitVec.sub_eq_add_neg] using he.symm
  · obtain ⟨i, hi, he⟩ := hcover
    have hmax : kind.mode.stateOffset v keccak fullState ≤ 296 := by
      cases fullState <;> cases keccak <;> cases kind <;> cases v <;> decide
    have apart := RangeApart.offsets (frameBase initial v kind.mode keccak fullState)
      (a := kind.mode.stateOffset v keccak fullState) (len := 201)
      (b := offset) (count := 8) (by omega) (by omega) (.inr hslot)
    exact apart i hi j hj he.symm

theorem preserves_slot {initial s t : RamState} {v : Variant} {kind : Loop.Kind} {offset : Nat}
    (ha : AgreesExcept (Loop.clobbers (keccak := keccak) (fullState := fullState) initial v kind) s t)
    (hslot : offset + 8 ≤ (kind.mode.stateOffset v (_keccak := keccak) (fullState := fullState))) :
    (Operand.mem (frameBase (keccak := keccak) (fullState := fullState) initial v kind.mode + BitVec.ofNat 64 offset) : Operand 64).read t =
      (Operand.mem (frameBase (keccak := keccak) (fullState := fullState) initial v kind.mode + BitVec.ofNat 64 offset) : Operand 64).read s := by
  apply memLoad_congr
  intro j hj
  simp only [memByte, PhysicalMemory.read, ha.byte (slot_avoids hslot j hj)]

end Sha3.Proofs.Wrapper.Loop
