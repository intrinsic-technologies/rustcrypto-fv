import Sha3.Proofs.Wrapper.Reset.Finalize.Memory
import Sha3.Proofs.Finalize

namespace Sha3.Proofs.Wrapper.Reset

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

structure FinalizeResetResult [Bindings] (initial : RamState) (v : Variant)
    (state : Incremental.State) (start final : RamState)
    (keccak : Bool := false) (fullState : Bool := false) (finalizeMode : Mode := .finalizeReset) : Prop where
  invariant : Invariant initial v finalizeMode final keccak fullState
  initialized : Initialized initial v finalizeMode final keccak fullState
  rip : final.RIP = comparePC v true keccak fullState finalizeMode
  saved : ∀ r ∈ (if fullState && (finalizeMode == .finalizeFixedReset || finalizeMode == .digestFinalizeReset)
      then [.rbx, .r12, .r14, .r15] else [.rbx, .rbp, .r12, .r13, .r14, .r15]),
    final.regValue r = start.regValue r
  index : (Operand.reg (indexReg true finalizeMode v fullState) : Operand 64).read final =
    (Operand.reg (indexReg true finalizeMode v fullState) : Operand 64).read start
  lowSlots : ∀ offset, offset + 8 ≤ 24 →
    (Operand.mem (frameBase initial v finalizeMode keccak fullState + BitVec.ofNat 64 offset) : Operand 64).read final =
      (Operand.mem (frameBase initial v finalizeMode keccak fullState + BitVec.ofNat 64 offset) : Operand 64).read start
  output : ∀ i : Fin (v.digestBytes fullState),
    final.external[initial.regValue .rcx + BitVec.ofNat 64 i.val]? =
      some (Finalize.digest v state keccak fullState)[i]
  outputSlot : (Operand.mem (outputSlot initial v finalizeMode keccak fullState) : Operand 64).read final =
    (Operand.mem (outputSlot initial v finalizeMode keccak fullState) : Operand 64).read start
  memory : MemoryWriteFrame start final (finalizeWriteRegions initial v keccak fullState finalizeMode)

theorem finalize_called_steps [bindings : Bindings] (hstride : UnitStringStride bindings)
    (v : Variant) {keccak fullState : Bool} {finalizeMode : Mode}
    {initial called : RamState} {inputs : Array Input} {split : Nat} {state : Incremental.State}
    (hInitial : ReadyToStep initial)
    (hCall : ValidInvocation bindings v finalizeMode initial inputs split keccak fullState)
    (entry : FinalizeResetEntry initial v state called keccak fullState finalizeMode)
    (hCursor : state.cursor < v.rate) :
    ∃ fuel t, Advances (returnBoundary initial) fuel called t ∧
      Invariant initial v finalizeMode t keccak fullState ∧
      Initialized initial v finalizeMode t keccak fullState ∧
      Finalize.CallResult v true state called t keccak fullState := by
  have hBoundary := (validInvocation_returnBoundary_bounds hInitial hCall).2
  have hfinal : ∃ fuel t, Advances (returnBoundary initial) fuel called t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧
      Finalize.CallResult v true state called t keccak fullState := by
    cases fullState with
    | false =>
      obtain ⟨t, ht, hr, hc, res⟩ := Finalize.call_advance (keccak := keccak) hstride v true state
        (returnBoundary initial) hBoundary called entry.invariant.ready
        entry.invariant.code (entry.pre hCall hCursor)
      exact ⟨_, t, ht, hr, hc, res⟩
    | true =>
      obtain ⟨rfl, rfl⟩ := hCall.fullState_valid rfl
      have hinside : called.regValue .rsp - (32 : BitVec 64) ≠
          (returnBoundary initial).rsp := by
        rw [entry.stack, frameBase, BitVec.sub_sub, BitVec.sub_sub]
        apply Finish.stackSub_ne_returnBoundary
        cases finalizeMode <;> decide +kernel
      obtain ⟨t, ht, hr, hc, res⟩ := Finalize.full_call_advance hstride true state
        (returnBoundary initial) hBoundary called entry.invariant.ready entry.invariant.code
        (entry.pre hCall hCursor) hinside
      exact ⟨_, t, ht, hr, hc, res⟩
  obtain ⟨fuel, t, hfinish, hready, _, result⟩ := hfinal
  have hMemory := finalizeMemory_before entry hCall result.memory
  have hcover := finalizeWriteRegions_subset initial v keccak fullState finalizeMode entry.modeValid
  have it := entry.invariant.of_callResult hCall hready hMemory
    (fun region hr address ha ↦ ⟨region, hcover region hr, ha⟩) result.grows result.rest
  have st := Finish.finalizeMemory_saved
    (offset := finalizeMode.stateOffset v keccak fullState) hCall.stackAvailable
    (by cases keccak <;> cases fullState <;> cases finalizeMode <;> cases v <;> decide)
    entry.stack entry.pointer entry.output (finalizeOutput_saved hCall entry.modeValid)
    result.memory entry.saved
  have htstack : stackPtr t = frameBase initial v finalizeMode keccak fullState := by
    change t.regValue .rsp = _
    rw [result.stack, entry.stack, BitVec.sub_add_cancel]
  refine ⟨fuel, t, hfinish, it, ⟨htstack, st, ?_⟩, result⟩
  simpa only [entry.pointer, Bytes] using result.zero rfl

theorem finalize_steps [bindings : Bindings] (hstride : UnitStringStride bindings)
    (v : Variant) {keccak fullState : Bool} {finalizeMode : Mode}
    {initial s : RamState} {inputs : Array Input} {split : Nat} {state : Incremental.State}
    (hInitial : ReadyToStep initial)
    (hCall : ValidInvocation bindings v finalizeMode initial inputs split keccak fullState)
    (inv : Invariant initial v finalizeMode s keccak fullState)
    (saved : SavedFrame initial s finalizeMode fullState)
    (hp : s.RIP = preparePC v true keccak fullState finalizeMode)
    (hs : stackPtr s = frameBase initial v finalizeMode keccak fullState)
    (ho : (beforeOutputOperand initial v finalizeMode keccak fullState).read s = initial.regValue .rcx)
    (hstate : Update.StateAt (statePointer initial v finalizeMode keccak fullState) state s)
    (hCursor : state.cursor < v.rate)
    (hMode : finalizeMode.hasBeforeOutput = true := by decide) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧
      FinalizeResetResult initial v state s t keccak fullState finalizeMode := by
  obtain ⟨prepFuel, called, hrun, entry, hslot, hlow, ha⟩ :=
    enter_finalize v hCall inv saved hp hs ho hstate hstride hMode
  obtain ⟨callFuel, t, hfinish, it, initialized, result⟩ :=
    finalize_called_steps hstride v hInitial hCall entry hCursor
  have keeps : ∀ r ∈ (if fullState && (finalizeMode == .finalizeFixedReset || finalizeMode == .digestFinalizeReset)
      then [.rbx, .r12, .r14, .r15] else [.rbx, .rbp, .r12, .r13, .r14, .r15]),
      t.regValue r = s.regValue r := by
    intro r hr
    have hsaved : r ∈ ([.rbx, .rbp, .r12, .r13, .r14, .r15] : List Syntax.Reg) := by
      split at hr
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> simp
      · exact hr
    refine (result.saved r hsaved).trans ?_
    cases finalizeMode <;> cases fullState
    all_goals first
      | change r ∈ ([.rbx, .r12, .r14, .r15] : List Syntax.Reg) at hr
      | change r ∈ ([.rbx, .rbp, .r12, .r13, .r14, .r15] : List Syntax.Reg) at hr
    all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    all_goals first
      | (rcases hr with rfl | rfl | rfl | rfl | rfl | rfl)
      | (rcases hr with rfl | rfl | rfl | rfl)
    all_goals first
      | apply ha.read (n := 64) (r := 3)
      | apply ha.read (n := 64) (r := 5)
      | apply ha.read (n := 64) (r := 12)
      | apply ha.read (n := 64) (r := 13)
      | apply ha.read (n := 64) (r := 14)
      | apply ha.read (n := 64) (r := 15)
    all_goals simp [finalizePrepareChanges, prepareChanges, Output.Zero.fullChanges,
      Output.Zero.fullPrepareChanges, Output.Zero.prepareChanges, Memset.clobbers]
  have low : ∀ offset, offset + 8 ≤ 24 →
      (Operand.mem (frameBase initial v finalizeMode keccak fullState + BitVec.ofNat 64 offset) : Operand 64).read t =
        (Operand.mem (frameBase initial v finalizeMode keccak fullState + BitVec.ofNat 64 offset) : Operand 64).read s := by
    intro offset hb
    refine (finalizeMemory_afterSlot entry hCall result.memory offset ?_ ?_).trans (hlow offset hb)
    · have hmin : 24 ≤ finalizeMode.stateOffset v keccak fullState := by
        cases finalizeMode <;> cases v <;> cases keccak <;> cases fullState <;>
          first | (solve | cases hMode) | decide +kernel
      omega
    · intro hm
      have ht : 24 ≤ Output.tempOffset v fullState := by cases fullState <;> cases v <;> decide +kernel
      omega
  have slot : (Operand.mem (outputSlot initial v finalizeMode keccak fullState) : Operand 64).read t =
      (Operand.mem (outputSlot initial v finalizeMode keccak fullState) : Operand 64).read s :=
    (finalizeMemory_afterSlot entry hCall result.memory
      (finalizeMode.outputSlotOffset v keccak fullState)
      (by cases finalizeMode <;> cases v <;> cases keccak <;> cases fullState <;>
        first | (solve | cases hMode) | decide +kernel)
      (by intro hc; rcases hc with rfl | rfl <;> cases v <;> cases keccak <;> cases fullState <;> decide +kernel)).trans hslot
  have memory : MemoryWriteFrame s t (finalizeWriteRegions initial v keccak fullState finalizeMode) :=
    memoryWriteFrame_trans (enter_finalize_memory hCall.stackAvailable ha)
      (finalizeMemory_before entry hCall result.memory)
  have index : (Operand.reg (indexReg true finalizeMode v fullState) : Operand 64).read t =
      (Operand.reg (indexReg true finalizeMode v fullState) : Operand 64).read s := by
    have h3 := keeps .rbx (by split <;> simp)
    have h13 : ¬(fullState = true ∧ (finalizeMode = .finalizeFixedReset ∨ finalizeMode = .digestFinalizeReset)) →
        t.regValue .r13 = s.regValue .r13 := by
      intro hn
      exact keeps .r13 (by cases finalizeMode <;> cases fullState <;> simp_all)
    cases finalizeMode <;> cases v <;> cases fullState <;>
      first | (solve | cases hMode) | exact h3 | exact h13 (by simp)
  by_cases hm : finalizeMode = .finalizeFixedReset ∨ finalizeMode = .digestFinalizeReset
  · cases fullState with
    | false =>
      have ob : t.regValue .rbp = initial.regValue .rcx := by
        refine (keeps .rbp (by simp)).trans ?_
        rcases hm with rfl | rfl <;> exact ho
      obtain ⟨u, hu, iu, su, pu, spu, bytes, frame, agu, savedu⟩ :=
        Output.inline_wrapper_steps v finalizeMode hm hCall it
          (by rcases hm with rfl | rfl <;> exact result.rip.trans entry.target)
          ob initialized.stack initialized.saved
          (beforeOutput_valid hCall hMode) (beforeOutput_mem initial v keccak false finalizeMode hMode)
          (beforeOutput_stack hCall hMode)
      have reads (offset : Nat) (hb : offset + 8 ≤ 24) :
          (Operand.mem (frameBase initial v finalizeMode keccak false + BitVec.ofNat 64 offset) : Operand 64).read u =
            (Operand.mem (frameBase initial v finalizeMode keccak false + BitVec.ofNat 64 offset) : Operand 64).read t := by
        apply memLoad_congr
        intro j hj
        simp only [memByte, PhysicalMemory.read, BitVec.add_assoc, ← BitVec.ofNat_add]
        rw [frame (offset+j) (by
          rcases hm with rfl | rfl <;> cases v <;> cases keccak <;>
            simp only [Mode.frameSize, Bool.false_eq_true, ↓reduceIte] <;> omega) (Or.inl (by omega))]
      have memoryu : MemoryWriteFrame t u (finalizeWriteRegions initial v keccak false finalizeMode) := by
        apply agu.memoryWriteFrame
        exact Output.inline_writes hm hCall.stackAvailable (beforeOutput_valid hCall hMode).2.1
          (Vector.mem_iff_getElem.mpr ⟨1, by decide, rfl⟩)
          (by
            have h : outputRegion (finalizeMode.entry v keccak false) initial ∈
                finalizeWriteRegions initial v keccak false finalizeMode :=
              Vector.mem_iff_getElem.mpr ⟨0, by decide, rfl⟩
            simpa only [beforeOutput_region] using h)
      refine ⟨_, u, (hrun.trans hfinish).trans hu,
        ⟨iu, ⟨spu, su, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, memoryWriteFrame_trans memory memoryu⟩⟩
      · intro i hi
        have he := frame (finalizeMode.stateOffset v keccak false+i) (by
          rcases hm with rfl | rfl <;> cases v <;> cases keccak <;>
            simp only [Mode.frameSize, Mode.stateOffset, Bool.false_eq_true, ↓reduceIte] <;> omega)
          (Or.inr (by
            rcases hm with rfl | rfl <;> cases v <;> cases keccak <;>
              simp only [Mode.stateOffset, Variant.digestBytes, Bool.false_eq_true, ↓reduceIte] <;> omega))
        have he' : u.external[statePointer initial v finalizeMode keccak false + BitVec.ofNat 64 i]? =
            t.external[statePointer initial v finalizeMode keccak false + BitVec.ofNat 64 i]? := by
          simpa only [statePointer, BitVec.ofNat_add, ← BitVec.add_assoc] using he
        exact he'.trans (initialized.zero i hi)
      · exact pu.trans (by rcases hm with rfl | rfl <;> cases v <;> cases keccak <;> decide +kernel)
      · intro r hr
        exact (savedu r (by simpa using hr)).trans (keeps r hr)
      · refine Eq.trans ?_ index
        have h3 := savedu .rbx (by simp)
        have h13 := savedu .r13 (by simp)
        rcases hm with rfl | rfl <;> cases v <;> first | exact h3 | exact h13
      · intro offset hb
        exact (reads offset hb).trans (low offset hb)
      · intro i
        have he := bytes i.val i.isLt
        have he' := result.output i
        rcases hm with rfl | rfl <;>
          exact he.trans (by simpa only [entry.output, finalizeOutputPointer] using he')
      · refine (reads (finalizeMode.outputSlotOffset v keccak false) ?_).trans slot
        rcases hm with rfl | rfl <;> cases v <;> cases keccak <;> decide +kernel
    | true =>
      obtain ⟨rfl, rfl⟩ := hCall.fullState_valid rfl
      have temp : t.regValue .r13 = Output.tempPointer initial .sha256 finalizeMode true true :=
        (result.saved .r13 (by simp)).trans (entry.temp rfl hm)
      have ob : (Operand.mem (frameBase initial .sha256 finalizeMode true true + 16) : Operand 64).read t =
          initial.regValue .rcx := by
        refine (low 16 (by decide)).trans ?_
        rcases hm with rfl | rfl <;> exact ho
      obtain ⟨u, hu, iu, pu, spu, bytes, frame, agu⟩ := Output.full_copy_steps hstride
        finalizeMode hm hCall it
        (by rcases hm with rfl | rfl <;> exact result.rip.trans entry.target)
        initialized.stack temp ob
        (beforeOutput_valid hCall hMode) (beforeOutput_mem initial .sha256 true true finalizeMode hMode)
        (beforeOutput_stack hCall hMode)
      have reads (offset : Nat) (hb : offset + 8 ≤ 240) :
          (Operand.mem (frameBase initial .sha256 finalizeMode true true + BitVec.ofNat 64 offset) : Operand 64).read u =
            (Operand.mem (frameBase initial .sha256 finalizeMode true true + BitVec.ofNat 64 offset) : Operand 64).read t := by
        apply memLoad_congr
        intro j hj
        simp only [memByte, PhysicalMemory.read, BitVec.add_assoc, ← BitVec.ofNat_add]
        rw [frame (offset+j) (by omega) (Or.inl (by omega))]
      have su : SavedFrame initial u finalizeMode true := by
        apply Output.saved_of_frame_bytes (v := .sha256) (keccak := true) hm initialized.saved
        intro offset hlo hhi
        have hsize : finalizeMode.frameSize .sha256 true true = 696 := by
          rcases hm with rfl | rfl <;> rfl
        rw [hsize] at hlo hhi
        exact frame offset hhi (Or.inr (by omega))
      have savedu : ∀ r ∈ ([.rbx, .r12, .r14, .r15] : List Syntax.Reg),
          u.regValue r = t.regValue r := by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        all_goals first
          | apply agu.read (n := 64) (r := 3)
          | apply agu.read (n := 64) (r := 12)
          | apply agu.read (n := 64) (r := 14)
          | apply agu.read (n := 64) (r := 15)
        all_goals simp [Output.fullFirstCopyChanges, Output.fullSecondCopyChanges,
          Output.fullCopyChanges, Memcpy.clobbers]
      have memoryu : MemoryWriteFrame t u (finalizeWriteRegions initial .sha256 true true finalizeMode) := by
        apply agu.memoryWriteFrame
        exact Output.full_copy_writes hm hCall.stackAvailable (beforeOutput_valid hCall hMode).2.1
          (Vector.mem_iff_getElem.mpr ⟨1, by decide, rfl⟩)
          (by
            have h : outputRegion (finalizeMode.entry .sha256 true true) initial ∈
                finalizeWriteRegions initial .sha256 true true finalizeMode :=
              Vector.mem_iff_getElem.mpr ⟨0, by decide, rfl⟩
            simpa only [beforeOutput_region, Variant.digestBytes, ↓reduceIte] using h)
      refine ⟨_, u, (hrun.trans hfinish).trans hu,
        ⟨iu, ⟨spu, su, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, memoryWriteFrame_trans memory memoryu⟩⟩
      · intro i hi
        have he := frame (32+i) (by omega) (Or.inl (by omega))
        have he' : u.external[statePointer initial .sha256 finalizeMode true true + BitVec.ofNat 64 i]? =
            t.external[statePointer initial .sha256 finalizeMode true true + BitVec.ofNat 64 i]? := by
          rcases hm with rfl | rfl <;>
            simpa only [statePointer, Mode.stateOffset, ↓reduceIte, BitVec.ofNat_add,
              BitVec.ofNat_eq_ofNat, ← BitVec.add_assoc] using he
        exact he'.trans (initialized.zero i hi)
      · rcases hm with rfl | rfl <;> exact pu
      · intro r hr
        have hr' : r ∈ ([.rbx, .r12, .r14, .r15] : List Syntax.Reg) := by
          rcases hm with rfl | rfl <;> simpa using hr
        exact (savedu r hr').trans (keeps r hr)
      · refine Eq.trans ?_ index
        rcases hm with rfl | rfl <;> exact savedu .rbx (by simp)
      · intro offset hb
        exact (reads offset (by omega)).trans (low offset hb)
      · intro i
        have he := bytes i.val (by have := i.isLt; exact this)
        have he' := result.output i
        rcases hm with rfl | rfl <;>
          exact he.trans (by simpa only [entry.output, finalizeOutputPointer] using he')
      · refine (reads (finalizeMode.outputSlotOffset .sha256 true true) ?_).trans slot
        rcases hm with rfl | rfl <;> decide +kernel
  · have hd : finalizeMode = .finalizeReset ∨ finalizeMode = .digestFinalizeIntoReset := by
      cases finalizeMode <;> simp_all [Mode.hasBeforeOutput]
    refine ⟨_, t, hrun.trans hfinish, ⟨it, initialized, ?_, keeps, index, low, ?_, slot, memory⟩⟩
    · exact (result.rip.trans entry.target).trans (by rcases hd with rfl | rfl <;> cases v <;> cases keccak <;> cases fullState <;> decide +kernel)
    · intro i
      have h := result.output i
      rcases hd with rfl | rfl <;> simpa only [entry.output, finalizeOutputPointer] using h

end Sha3.Proofs.Wrapper.Reset
