import Sha3.Proofs.Finalize.Frame
import Sha3.Proofs.Finalize.Output
import Sha3.Proofs.Finalize.Epilogue
import Sha3.Proofs.Finalize.Reset

namespace Sha3.Proofs.Finalize

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

def finishSteps (v : Variant) (reset : Bool) : Nat :=
  Output.steps v + if reset then 52 else 4

theorem directionFlagUnset_of_fixedPart {s t : RamState}
    (h : scalarFrame t = scalarFrame s) (hs : DirectionFlagUnset s) : DirectionFlagUnset t :=
  ⟨(congrArg ScalarFrame.direction h).trans hs.df⟩

theorem BodyFrame.output_pre {boundary : ReturnBoundary} {v : Variant}
    {keccak fullState reset : Bool} {state : Incremental.State} {initial s : RamState}
    {p : BitVec 64}
    (hp : CallPre boundary v reset state initial keccak fullState)
    (h : BodyFrame v initial s fullState) (hip : s.RIP = p) :
    Output.OutputPre p (initial.regValue .rdi) (initial.regValue .rsi)
      (v.digestBytes fullState) (.reg 14) Extracted.programImage s := by
  refine ⟨hip, h.stateSaved, h.output, ?_, ?_, ?_, ?_, ?_⟩
  · intro offset n hn
    exact h.toSavedFrame.readable (readable_slice hp.stateRead offset n (by omega))
  · intro offset n hn
    exact h.toSavedFrame.readable (readable_slice hp.outputRead offset n hn)
  · exact fun i hi ht ↦ hp.outputAvoid i hi (.inr ht)
  · intro i hi x hx he
    exact hp.outputAvoid i hi (.inl (he ▸ ⟨x.2, hx⟩))
  · exact fun i hi j hj ↦ hp.outputState i hi j (by omega)

theorem Permuted.output_pre {boundary : ReturnBoundary} {v : Variant} {keccak : Bool} {reset : Bool}
    {state : Incremental.State} {initial s : RamState}
    (hp : CallPre (keccak := keccak) boundary v reset state initial) (h : Permuted (keccak := keccak) v reset state initial s) :
    Output.Pre v (outputAddress (keccak := keccak) v reset) (initial.regValue .rdi) (initial.regValue .rsi)
      (Incremental.finalize Keccak.keccakLanes v.rate state (Variant.suffix keccak)) Extracted.programImage s := by
  exact ⟨h.toBodyFrame.output_pre hp h.rip, h.lanes⟩

theorem output_writesWithin {boundary : ReturnBoundary} {v : Variant} {fullState : Bool} {keccak : Bool} {reset : Bool}
    {state : Incremental.State} {initial : RamState}
    (hp : CallPre (fullState := fullState) (keccak := keccak) boundary v reset state initial) :
    WritesWithin (Output.outputChanges (initial.regValue .rsi) (v.digestBytes (fullState := fullState)))
      (writeRegions (fullState := fullState) v initial) := by
  intro c hc x hcover
  simp only [Output.outputChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · exact hcover.elim
  · exact hcover.elim
  · exact hcover.elim
  · obtain ⟨i, hi, rfl⟩ := hcover
    exact ⟨⟨(initial.regValue .rsi).toNat, (v.digestBytes (fullState := fullState))⟩, by simp [writeRegions],
      region_contains_byte hp.outputRead.low hi⟩
  · exact hcover.elim

theorem output_slot {boundary : ReturnBoundary} {v : Variant} {fullState : Bool} {keccak : Bool} {reset : Bool}
    {state : Incremental.State} {initial s t : RamState}
    (hp : CallPre (fullState := fullState) (keccak := keccak) boundary v reset state initial)
    (ha : AgreesExcept (Output.outputChanges (initial.regValue .rsi) (v.digestBytes (fullState := fullState))) s t)
    {k : Nat} (hk : k ≤ 16) :
    (Operand.mem (initial.regValue .rsp - BitVec.ofNat 64 k) : Operand 64).read t =
      (Operand.mem (initial.regValue .rsp - BitVec.ofNat 64 k) : Operand 64).read s := by
  rw [frame_offset initial (by omega : k ≤ 296)]
  exact Output.outputChanges_stackLoad ha hp.outputStack (296 - k) 64 (by omega)

theorem BodyFrame.after_output {boundary : ReturnBoundary} {v : Variant} {fullState : Bool} {keccak : Bool} {reset : Bool}
    {state : Incremental.State} {initial s t : RamState}
    (hp : CallPre (fullState := fullState) (keccak := keccak) boundary v reset state initial) (h : BodyFrame (fullState := fullState) v initial s)
    (ha : AgreesExcept (Output.outputChanges (initial.regValue .rsi) (v.digestBytes (fullState := fullState))) s t) :
    BodyFrame (fullState := fullState) v initial t := by
  have hsaved : CalleeSavedRegistersUnchanged s t :=
    calleeSavedRegistersUnchanged_of_agreesExcept ha (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp (config := { decide := true }) [Output.outputChanges])
  refine {
    saved := ?_
    rbx := (output_slot hp ha (k := 16) (by decide)).trans h.rbx
    r14 := (output_slot hp ha (k := 8) (by decide)).trans h.r14
    returnSlot := ?_
    memory := memoryWriteFrame_trans h.memory (ha.memoryWriteFrame (output_writesWithin hp))
    grows := fun a hx ↦ ha.grow a (h.grows a hx)
    rest := (ha.scalarFrame_eq (by rfl)).trans h.rest
    stack := (Output.outputChanges_stack ha).trans h.stack
    stateSaved := (hsaved .rbx (by simp)).trans h.stateSaved
    output := (hsaved .r14 (by simp)).trans h.output }
  · intro r hr
    have hr' : r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl <;> simp
    exact (hsaved r hr').trans (h.saved r hr)
  · have hz := output_slot hp ha (k := 0) (by decide)
    simp only [BitVec.sub_zero] at hz
    exact hz.trans h.returnSlot

theorem BodyFrame.epilogue_pre [Bindings] {boundary : ReturnBoundary} {v : Variant} {keccak : Bool}
    {state : Incremental.State} {initial s : RamState}
    (hp : CallPre (keccak := keccak) boundary v false state initial) (h : BodyFrame v initial s)
    (hc : CodeIn Extracted.programImage s) (hip : s.RIP = epilogueAddress (keccak := keccak) v false) :
    FinalizeEpiloguePre (epilogueAddress (keccak := keccak) v false) (stackTop initial)
      (initial.regValue .rsp + 8) s := by
  refine ⟨hip, ?_, ?_, ?_, ?_⟩
  · rw [show stackPtr s = initial.regValue .rsp - 24 from h.stack]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  · intro i
    have he : initial.regValue .rsp + 8 - 24 =
        frameBase initial + BitVec.ofNat 64 280 := by
      simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rfl
    rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact h.toSavedFrame.readable (readable_slice hp.frameRead (280 + 8 * i.val) 8
      (by have := i.isLt; omega))
  · simpa only [BitVec.add_sub_cancel] using h.returnSlot
  · obtain ⟨byte, hbyte⟩ := hp.target
    exact (hc (stackTop initial, byte) hbyte).1

theorem epilogue_result {v : Variant} {keccak : Bool}
    {state : Incremental.State} {initial s t : RamState}
    (h : BodyFrame v initial s)
    (hd : ∀ i : Fin (v.digestBytes),
      s.external[initial.regValue .rsi + BitVec.ofNat 64 i.val]? = some (digest v state (keccak := keccak))[i])
    (he : FinalizeEpilogueResult (stackTop initial) (initial.regValue .rsp + 8) s t) :
    CallResult (keccak := keccak) v false state initial t := by
  have hbx : t.regValue .rbx = initial.regValue .rbx := by
    have hp : initial.regValue .rsp + 8 - 24 = initial.regValue .rsp - 16 := by
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rfl
    exact (hp ▸ he.rbx).trans h.rbx
  have h14 : t.regValue .r14 = initial.regValue .r14 := by
    have hp : initial.regValue .rsp + 8 - 16 = initial.regValue .rsp - 8 := by
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rfl
    exact (hp ▸ he.r14).trans h.r14
  refine {
    rip := he.rip
    stack := he.stack
    saved := ?_
    memory := ?_
    grows := ?_
    rest := (he.agrees.scalarFrame_eq (by rfl)).trans h.rest
    output := ?_
    zero := fun hf ↦ Bool.noConfusion hf }
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hbx
    · exact (he.agrees.read (n := 64) (r := 5) (by simp [epilogueChanges])).trans
        (h.saved .rbp (by simp))
    · exact (he.agrees.read (n := 64) (r := 12) (by simp [epilogueChanges])).trans
        (h.saved .r12 (by simp))
    · exact (he.agrees.read (n := 64) (r := 13) (by simp [epilogueChanges])).trans
        (h.saved .r13 (by simp))
    · exact h14
    · exact (he.agrees.read (n := 64) (r := 15) (by simp [epilogueChanges])).trans
        (h.saved .r15 (by simp))
  · intro a ha
    rw [he.memory]
    exact h.memory a ha
  · intro a ha
    rw [he.memory]
    exact h.grows a ha
  · intro i
    rw [he.memory]
    exact hd i

theorem BodyFrame.reset_pre {boundary : ReturnBoundary} {v : Variant} {fullState : Bool} {keccak : Bool}
    {state : Incremental.State} {initial s : RamState}
    (hp : CallPre (fullState := fullState) (keccak := keccak) boundary v true state initial) (h : BodyFrame (fullState := fullState) v initial s)
    (hip : s.RIP = epilogueAddress (fullState := fullState) (keccak := keccak) v true) :
    Reset.Pre (fullState := fullState) (keccak := keccak) boundary v (initial.regValue .rdi) (initial.regValue .rsp) (stackTop initial) s := by
  refine {
    rip := hip
    pointer := h.stateSaved
    stack := h.stack
    readable := ?_
    aligned := hp.aligned
    direction := directionFlagUnset_of_fixedPart h.rest hp.direction
    destination := h.toSavedFrame.readable hp.stateRead
    tables := ?_
    program := ?_
    returnRead := ?_
    returnSlot := h.returnSlot
    targetInProgram := hp.target
    disjoint := ?_
    inside := hp.resetBoundary rfl }
  · intro i
    rw [show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
      frame_offset initial (by decide : 16 ≤ 296), BitVec.add_assoc, ← BitVec.ofNat_add]
    exact h.toSavedFrame.readable (readable_slice hp.frameRead (280 + 8 * i.val) 8
      (by have := i.isLt; omega))
  · intro address hin ht
    obtain ⟨i, hi, he⟩ := region_contains_offset hin
    subst address
    exact hp.stateAvoid i hi (.inr ht)
  · intro address hin ht
    obtain ⟨i, hi, he⟩ := region_contains_offset hin
    subst address
    exact hp.stateAvoid i hi (.inl ht)
  · have hread := h.toSavedFrame.readable (readable_slice hp.frameRead 296 8 (by decide))
    simpa only [frameBase, BitVec.ofNat_eq_ofNat, BitVec.sub_add_cancel] using hread
  · intro i hi j hj he
    apply hp.stateStack i hi (296 + j) (by omega)
    have hbase : initial.regValue .rsp = frameBase initial + BitVec.ofNat 64 296 :=
      (BitVec.sub_add_cancel _ _).symm
    rw [hbase] at he
    simpa only [BitVec.add_assoc, ← BitVec.ofNat_add] using he

theorem reset_result [Bindings] {boundary : ReturnBoundary} {v : Variant} {fullState : Bool} {keccak : Bool}
    {state : Incremental.State} {initial s t : RamState}
    (hp : CallPre (fullState := fullState) (keccak := keccak) boundary v true state initial) (h : BodyFrame (fullState := fullState) v initial s)
    (hd : ∀ i : Fin (v.digestBytes (fullState := fullState)),
      s.external[initial.regValue .rsi + BitVec.ofNat 64 i.val]? = some (digest v state (fullState := fullState) (keccak := keccak))[i])
    (he : Reset.Done (initial.regValue .rdi) (initial.regValue .rsp) (stackTop initial) s t) :
    CallResult (fullState := fullState) (keccak := keccak) v true state initial t := by
  refine {
    rip := he.rip
    stack := he.stack
    saved := ?_
    memory := memoryWriteFrame_trans h.memory (he.agrees.memoryWriteFrame ?_)
    grows := fun a hx ↦ he.agrees.grow a (h.grows a hx)
    rest := (he.agrees.scalarFrame_eq (by rfl)).trans h.rest
    output := ?_
    zero := fun _ ↦ he.zero }
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact he.rbx.trans h.rbx
    · exact (he.read 5 (by simp)).trans (h.saved .rbp (by simp))
    · exact (he.read 12 (by simp)).trans (h.saved .r12 (by simp))
    · exact (he.read 13 (by simp)).trans (h.saved .r13 (by simp))
    · exact he.r14.trans h.r14
    · exact (he.read 15 (by simp)).trans (h.saved .r15 (by simp))
  · apply Reset.changes_writesWithin
    intro i hi
    exact ⟨⟨(initial.regValue .rdi).toNat, 201⟩, by simp [writeRegions],
      region_contains_byte hp.stateRead.low hi⟩
  · intro i
    rw [← hd i]
    apply he.agrees.byte
    intro c hc hcover
    simp only [Reset.changes, List.mem_append] at hc
    rcases hc with hc | hc
    · simp only [Reset.scalarChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hcover
    · simp only [Memset.clobbers, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        try exact hcover
      obtain ⟨j, hj, haddr⟩ := hcover
      exact hp.outputState i.val i.isLt j hj haddr

theorem finish_advance [bindings : Bindings] (hstride : UnitStringStride bindings)
    {boundary : ReturnBoundary} {v : Variant} {keccak : Bool} {reset : Bool}
    {state : Incremental.State} {initial : RamState}
    (hp : CallPre (keccak := keccak) boundary v reset state initial) (hb : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (finishSteps v reset) (Permuted (keccak := keccak) v reset state initial)
      Extracted.programImage (fun _ t ↦ CallResult (keccak := keccak) v reset state initial t) := by
  intro s hs hcode h
  obtain ⟨copied, hcopy, hready, hcopiedcode, ho⟩ := Output.copy (keccak := keccak) v reset
    (initial.regValue .rdi) (initial.regValue .rsi)
    (Incremental.finalize Keccak.keccakLanes v.rate state (Variant.suffix keccak)) boundary hb s hs hcode
    (h.output_pre hp)
  have hf := h.toBodyFrame.after_output hp ho.agrees
  have hout : ∀ i : Fin (v.digestBytes),
      copied.external[initial.regValue .rsi + BitVec.ofNat 64 i.val]? =
        some (digest v state (keccak := keccak))[i] := ho.output
  cases reset with
  | false =>
    obtain ⟨t, htail, htr, htc, he⟩ := finalizeEpilogue_advance boundary
      (epilogueAddress (keccak := keccak) v false) (stackTop initial) (initial.regValue .rsp + 8)
      (finalizeEpilogue_image (keccak := keccak) v) (by
        intro p hpc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hpc
        rcases hpc with rfl | rfl | rfl | rfl
        · exact fun he ↦ hb (he ▸ finalizeEpilogue_inProgram (keccak := keccak) v ⟨4, by decide⟩)
        · exact fun he ↦ hb (he ▸ finalizeEpilogue_inProgram (keccak := keccak) v ⟨5, by decide⟩)
        · exact fun he ↦ hb (he ▸ finalizeEpilogue_inProgram (keccak := keccak) v ⟨7, by decide⟩)
        · exact fun he ↦ hb (he ▸ hp.target)) copied hready hcopiedcode
      (hf.epilogue_pre hp hcopiedcode ho.rip)
    exact ⟨t, hcopy.trans htail, htr, htc, epilogue_result hf hout he⟩
  | true =>
    obtain ⟨t, htail, he⟩ := Reset.tail_steps (keccak := keccak) hstride boundary hb v
      (initial.regValue .rdi) (initial.regValue .rsp) (stackTop initial) copied
      hready hcopiedcode (hf.reset_pre hp ho.rip)
    exact ⟨t, hcopy.trans htail, he.ready, he.code, reset_result hp hf hout he⟩

end Sha3.Proofs.Finalize
