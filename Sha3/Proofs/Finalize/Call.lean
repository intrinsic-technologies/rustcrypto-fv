import Sha3.Proofs.Finalize.Frame
import Sha3.Proofs.Permutation.Execution
import Sha3.Proofs.PermutationCall
import Sha3.Proofs.Calls

namespace Sha3.Proofs.Finalize

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

def callDisplacement (v : Variant) (reset : Bool) (keccak : Bool := false) (fullState : Bool := false) : BitVec 32 :=
  (Permutation.entryAddress .finalize - outputAddress (keccak := keccak) (fullState := fullState) v reset).setWidth 32

theorem call_target (v : Variant) (reset : Bool)
    (keccak : Bool := false) (fullState : Bool := false)
    (valid : fullState = true → v = .sha256 ∧ keccak = true := by simp_all) :
    branchTarget (callAddress (keccak := keccak) (fullState := fullState) v reset) 5 ((callDisplacement (keccak := keccak) (fullState := fullState) v reset).signExtend 64) =
      Permutation.entryAddress .finalize := by
  cases v <;> cases reset <;> cases keccak <;> cases fullState <;>
      simp_all <;> decide +kernel

theorem call_code (v : Variant) (reset : Bool)
    (keccak : Bool := false) (fullState : Bool := false)
    (valid : fullState = true → v = .sha256 ∧ keccak = true := by simp_all) :
    ∀ x ∈ codeRange (callAddress (keccak := keccak) (fullState := fullState) v reset) (encodeCallRel32 (callDisplacement (keccak := keccak) (fullState := fullState) v reset)),
      x ∈ Extracted.programImage := by
  have h : ∀ i : Fin (encodeCallRel32 (callDisplacement (keccak := keccak) (fullState := fullState) v reset)).length,
      Extracted.programSections.fetchByte (callAddress (keccak := keccak) (fullState := fullState) v reset + BitVec.ofNat 64 i.val) =
        some (encodeCallRel32 (callDisplacement (keccak := keccak) (fullState := fullState) v reset))[i.val] := by
    cases v <;> cases reset <;> cases keccak <;> cases fullState <;>
      simp_all <;> decide +kernel
  intro x hx
  obtain ⟨i, rfl⟩ := (mem_codeRange_iff _ _ _).mp hx
  exact imageSections_mem_toCodeMap_of_fetchByte (h i)

theorem output_inProgram (v : Variant) (reset : Bool)
    (keccak : Bool := false) (fullState : Bool := false)
    (valid : fullState = true → v = .sha256 ∧ keccak = true := by simp_all) :
    InProgram (outputAddress (keccak := keccak) (fullState := fullState) v reset) := by
  apply Exists.intro (if fullState then 0xba else 0x48)
  apply imageSections_mem_toCodeMap_of_fetchByte
  cases v <;> cases reset <;> cases keccak <;> cases fullState <;>
      simp_all <;> decide +kernel

theorem pushAddr_padded {v : Variant} {keccak : Bool} {fullState : Bool} {reset : Bool} {state : Incremental.State}
    {initial s : RamState} (h : Padded (keccak := keccak) (fullState := fullState) v reset state initial s) :
    pushAddr s = initial.regValue .rsp - 32 := by
  change s.regValue .rsp - 8 = _
  rw [h.stack, BitVec.sub_sub]
  rfl

theorem call_push_read {boundary : ReturnBoundary} {v : Variant} {keccak : Bool} {fullState : Bool} {reset : Bool}
    {state : Incremental.State} {initial s : RamState}
    (hp : CallPre (keccak := keccak) (fullState := fullState) boundary v reset state initial) (h : Padded (keccak := keccak) (fullState := fullState) v reset state initial s) :
    MemReadable s (pushAddr s) 8 := by
  rw [pushAddr_padded h]
  have he : initial.regValue .rsp - 32 = frameBase initial + BitVec.ofNat 64 264 := by
    simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  rw [he]
  exact h.toSavedFrame.readable (readable_slice hp.frameRead 264 8 (by decide))

theorem call_push_page {boundary : ReturnBoundary} {v : Variant} {keccak : Bool} {fullState : Bool} {reset : Bool}
    {state : Incremental.State} {initial s : RamState}
    (hp : CallPre (keccak := keccak) (fullState := fullState) boundary v reset state initial) (h : Padded (keccak := keccak) (fullState := fullState) v reset state initial s) :
    (pushAddr s).toNat % 4096 + 8 ≤ 4096 := by
  rw [pushAddr_padded h]
  rw [show (32 : BitVec 64) = BitVec.ofNat 64 32 from rfl,
    stack_sub_toNat hp.stack.2.2.1 (by decide : 32 ≤ frameBytes)]
  have ha : (initial.regValue .rsp).toNat % 16 = 8 := hp.stack.2.2.2
  have hb : 296 ≤ (initial.regValue .rsp).toNat := hp.stack.2.2.1
  omega

theorem call_step [Bindings] {boundary : ReturnBoundary} {v : Variant} {keccak : Bool} {fullState : Bool} {reset : Bool}
    {state : Incremental.State} {initial s : RamState}
    (hp : CallPre (keccak := keccak) (fullState := fullState) boundary v reset state initial) (hb : ¬ InProgram boundary.rip)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (h : Padded (keccak := keccak) (fullState := fullState) v reset state initial s) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      (callEffect (fun _ ↦ Permutation.entryAddress .finalize)
        (outputAddress (keccak := keccak) (fullState := fullState) v reset) s).Holds s t := by
  let pre := Padded (keccak := keccak) (fullState := fullState) v reset state initial
  have hw : ∀ s, pre s → ∀ i < 8, ∃ region ∈ #v[Stack.region initial frameBytes],
      region.Contains (pushAddr s + BitVec.ofNat 64 i).toNat := by
    intro s hs i hi
    refine ⟨Stack.region initial frameBytes, by simp, ?_⟩
    rw [pushAddr_padded hs]
    exact stack_sub_contains (offset := 32) hp.stack (by decide) (by omega)
  have ha : ∀ s, pre s → ∀ region ∈ #v[Stack.region initial frameBytes],
      region.Avoids InPageTables := by
    intro s hs region hregion
    have he : region = Stack.region initial frameBytes := by simpa using hregion
    subst region
    exact fun a hin ht ↦ hp.stackAvoid a hin (.inr ht)
  have hs := call_rel32_effect_step_of_readable
    (fun _ ↦ #v[Stack.region initial frameBytes]) hw ha (callDisplacement (keccak := keccak) (fullState := fullState) v reset)
    (fun s hs ↦ ⟨hs.rip, call_push_read hp hs⟩)
    (fun s hs ↦ call_push_page hp hs)
    (by rw [call_target (keccak := keccak) (fullState := fullState) (valid := hp.valid)]; decide +kernel)
  obtain ⟨t, ht, hr', he⟩ := hs.advances hr (hc.mono (call_code (keccak := keccak) (fullState := fullState) v reset (valid := hp.valid))) h (by
    change branchTarget (callAddress (keccak := keccak) (fullState := fullState) v reset) 5 _ ≠ boundary.rip
    rw [call_target (keccak := keccak) (fullState := fullState) (valid := hp.valid)]
    exact fun he ↦ hb (he ▸ ⟨0x55,
      imageSections_mem_toCodeMap_of_fetchByte (by decide +kernel)⟩))
  have hv : (callEffect (fun _ ↦ branchTarget (callAddress (keccak := keccak) (fullState := fullState) v reset) 5
      ((callDisplacement (keccak := keccak) (fullState := fullState) v reset).signExtend 64)) (callAddress (keccak := keccak) (fullState := fullState) v reset + 5) s).Avoids
      Extracted.programImage := by
    intro x hx c hmem hcover
    simp only [callEffect, pushEffect_components, List.mem_cons,
      List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact hcover
    · obtain ⟨i, hi, heq⟩ := hcover
      obtain ⟨region, hreg, hin⟩ := hw s h i hi
      have he : region = Stack.region initial frameBytes := by simpa using hreg
      subst region
      exact hp.stackAvoid x.1 (heq ▸ hin) (.inl ⟨x.2, hx⟩)
    · exact hcover
  refine ⟨t, ht, hr', he.codeIn hv hc, ?_⟩
  simpa only [call_target (keccak := keccak) (fullState := fullState) (valid := hp.valid), outputAddress] using he

theorem called_agrees {v : Variant} {keccak : Bool} {fullState : Bool} {reset : Bool} {state : Incremental.State}
    {initial s t : RamState} (h : Padded (keccak := keccak) (fullState := fullState) v reset state initial s)
    (he : (callEffect (fun _ ↦ Permutation.entryAddress .finalize)
      (outputAddress (keccak := keccak) (fullState := fullState) v reset) s).Holds s t) :
    AgreesExcept [.reg 4, .mem (initial.regValue .rsp - 32) 8, .rip] s t := by
  simpa only [callEffect, pushEffect_components, pushAddr_padded h] using he.agrees

theorem called_stack {v : Variant} {keccak : Bool} {fullState : Bool} {reset : Bool} {state : Incremental.State}
    {initial s t : RamState} (h : Padded (keccak := keccak) (fullState := fullState) v reset state initial s)
    (he : (callEffect (fun _ ↦ Permutation.entryAddress .finalize)
      (outputAddress (keccak := keccak) (fullState := fullState) v reset) s).Holds s t) :
    t.regValue .rsp = initial.regValue .rsp - 32 :=
  he.writes.1.trans (pushAddr_padded h)

theorem called_pointer {v : Variant} {keccak : Bool} {fullState : Bool} {reset : Bool} {state : Incremental.State}
    {initial s t : RamState} (h : Padded (keccak := keccak) (fullState := fullState) v reset state initial s)
    (he : (callEffect (fun _ ↦ Permutation.entryAddress .finalize)
      (outputAddress (keccak := keccak) (fullState := fullState) v reset) s).Holds s t) :
    t.regValue .rdi = initial.regValue .rdi :=
  ((called_agrees h he).read (n := 64) (r := 7) (by simp)).trans h.pointer

theorem called_frameBase {v : Variant} {keccak : Bool} {fullState : Bool} {reset : Bool} {state : Incremental.State}
    {initial s t : RamState} (h : Padded (keccak := keccak) (fullState := fullState) v reset state initial s)
    (he : (callEffect (fun _ ↦ Permutation.entryAddress .finalize)
      (outputAddress (keccak := keccak) (fullState := fullState) v reset) s).Holds s t) :
    Permutation.frameBase t = frameBase initial := by
  rw [Permutation.frameBase, called_stack h he, BitVec.sub_sub]
  rfl

theorem called_pre {boundary : ReturnBoundary} {v : Variant} {keccak : Bool} {fullState : Bool} {reset : Bool}
    {state : Incremental.State} {initial s t : RamState}
    (hp : CallPre (keccak := keccak) (fullState := fullState) boundary v reset state initial) (h : Padded (keccak := keccak) (fullState := fullState) v reset state initial s)
    (he : (callEffect (fun _ ↦ Permutation.entryAddress .finalize)
      (outputAddress (keccak := keccak) (fullState := fullState) v reset) s).Holds s t) : Permutation.CallPre .finalize t := by
  have ha := called_agrees h he
  have hs := called_stack h he
  have hd := called_pointer h he
  have hg (a : BitVec 64) (hx : (initial.external[a]?).isSome) :
      (t.external[a]?).isSome := ha.grow a (h.grows a hx)
  refine ⟨he.rip, stackValid_nested hp.stack (by decide : 32 + 264 ≤ frameBytes)
    (by decide) hs hg, ?_, ?_, ?_, ?_, ?_⟩
  · intro a hin
    exact hp.stackAvoid a (stackRegion_nested hp.stack.2.2.1
      (by decide : 32 + 264 ≤ frameBytes) hs hin)
  · rw [hd]
    exact readable_of_grows hg (by
      simpa only [BitVec.add_zero] using readable_slice hp.stateRead 0 200 (by decide))
  · rw [hd, called_frameBase h he]
    intro i hi j hj
    exact hp.stateStack i (by omega) j (by omega)
  · rw [hd]
    exact fun i hi ↦ hp.stateAvoid i (by omega)
  · have htop : stackTop t = outputAddress (keccak := keccak) (fullState := fullState) v reset := by
      change (Operand.mem (t.regValue .rsp) : Operand 64).read t = _
      rw [hs, ← pushAddr_padded h]
      exact he.writes.2
    rw [htop]
    exact output_inProgram (keccak := keccak) (fullState := fullState) v reset (valid := hp.valid)

theorem called_read {v : Variant} {keccak : Bool} {fullState : Bool} {reset : Bool} {state : Incremental.State}
    {initial s t : RamState} (h : Padded (keccak := keccak) (fullState := fullState) v reset state initial s)
    (he : (callEffect (fun _ ↦ Permutation.entryAddress .finalize)
      (outputAddress (keccak := keccak) (fullState := fullState) v reset) s).Holds s t) {a : BitVec 64} {n : Nat}
    (hap : RangeApart (initial.regValue .rsp - 32) 8 a (n / 8)) :
    (Operand.mem a : Operand n).read t = (Operand.mem a : Operand n).read s := by
  apply read_of_agrees (called_agrees h he)
  intro i hi c hc hcover
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact hcover
  · obtain ⟨j, hj, heq⟩ := hcover
    exact hap j hj i hi heq.symm
  · exact hcover

theorem called_lanes {boundary : ReturnBoundary} {v : Variant} {keccak : Bool} {fullState : Bool} {reset : Bool}
    {state : Incremental.State} {initial s t : RamState}
    (hp : CallPre (keccak := keccak) (fullState := fullState) boundary v reset state initial) (h : Padded (keccak := keccak) (fullState := fullState) v reset state initial s)
    (he : (callEffect (fun _ ↦ Permutation.entryAddress .finalize)
      (outputAddress (keccak := keccak) (fullState := fullState) v reset) s).Holds s t) :
    Permutation.memoryLanes (initial.regValue .rdi) t =
      Permutation.memoryLanes (initial.regValue .rdi) s := by
  funext lane
  apply called_read h he
  intro i hi j hj heq
  apply hp.stateStack (8 * lane.val + j) (by have := lane.isLt; omega)
    (264 + i) (by omega)
  have hslot : initial.regValue .rsp - 32 = frameBase initial + BitVec.ofNat 64 264 := by
    simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  rw [hslot] at heq
  simpa only [BitVec.add_assoc, ← BitVec.ofNat_add] using heq.symm


theorem called_slot {v : Variant} {keccak : Bool} {fullState : Bool} {reset : Bool} {state : Incremental.State}
    {initial s t : RamState} (h : Padded (keccak := keccak) (fullState := fullState) v reset state initial s)
    (he : (callEffect (fun _ ↦ Permutation.entryAddress .finalize)
      (outputAddress (keccak := keccak) (fullState := fullState) v reset) s).Holds s t) {k : Nat} (hk : k ≤ 16) :
    (Operand.mem (initial.regValue .rsp - BitVec.ofNat 64 k) : Operand 64).read t =
      (Operand.mem (initial.regValue .rsp - BitVec.ofNat 64 k) : Operand 64).read s := by
  apply called_read h he
  rw [frame_offset initial (by omega : k ≤ 296)]
  change RangeApart (initial.regValue .rsp - BitVec.ofNat 64 32) 8 _ 8
  rw [frame_offset initial (by decide : 32 ≤ 296)]
  exact RangeApart.offsets (frameBase initial) (a := 264) (len := 8)
    (b := 296 - k) (count := 8) (by decide) (by omega) (.inl (by omega))

theorem called_memory {boundary : ReturnBoundary} {v : Variant} {keccak : Bool} {fullState : Bool} {reset : Bool}
    {state : Incremental.State} {initial s t : RamState}
    (hp : CallPre (keccak := keccak) (fullState := fullState) boundary v reset state initial) (h : Padded (keccak := keccak) (fullState := fullState) v reset state initial s)
    (he : (callEffect (fun _ ↦ Permutation.entryAddress .finalize)
      (outputAddress (keccak := keccak) (fullState := fullState) v reset) s).Holds s t) :
    MemoryWriteFrame s t (writeRegions (fullState := fullState) v initial) := by
  apply (called_agrees h he).memoryWriteFrame
  intro c hc address hcover
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact hcover.elim
  · obtain ⟨i, hi, rfl⟩ := hcover
    refine ⟨Stack.region initial frameBytes, by simp [writeRegions], ?_⟩
    exact stack_sub_contains (offset := 32) hp.stack (by decide) (by omega)
  · exact hcover.elim

theorem permutation_slot {boundary : ReturnBoundary} {v : Variant} {keccak : Bool} {fullState : Bool} {reset : Bool}
    {state : Incremental.State} {initial s called t : RamState}
    (hp : CallPre (keccak := keccak) (fullState := fullState) boundary v reset state initial) (h : Padded (keccak := keccak) (fullState := fullState) v reset state initial s)
    (he : (callEffect (fun _ ↦ Permutation.entryAddress .finalize)
      (outputAddress (keccak := keccak) (fullState := fullState) v reset) s).Holds s called) {a : Keccak.Lanes}
    (hr : Permutation.CallResult called t a) {k : Nat} (hk : k ≤ 16) :
    (Operand.mem (initial.regValue .rsp - BitVec.ofNat 64 k) : Operand 64).read t =
      (Operand.mem (initial.regValue .rsp - BitVec.ofNat 64 k) : Operand 64).read called := by
  apply memLoad_congr
  intro j hj
  apply congrArg (fun x : Option UInt8 ↦ x.getD 0)
  apply hr.memory
  intro region hregion hin
  have hregions : region = ⟨(frameBase initial).toNat, 264⟩ ∨
      region = ⟨(initial.regValue .rdi).toNat, 200⟩ := by
    simpa only [Permutation.writeRegions, called_frameBase h he, called_pointer h he,
      Permutation.frameBytes, Vector.mem_mk, List.mem_toArray, List.mem_cons,
      List.not_mem_nil, or_false] using hregion
  rcases hregions with rfl | rfl
  · obtain ⟨i, hi, heq⟩ := region_contains_offset hin
    apply RangeApart.offsets (frameBase initial) (a := 0) (len := 264)
      (b := 296 - k) (count := 8) (by decide) (by omega) (.inl (by omega))
      i hi j hj
    rw [frame_offset initial (by omega : k ≤ 296)] at heq
    simpa only [BitVec.add_zero] using heq.symm
  · obtain ⟨i, hi, heq⟩ := region_contains_offset hin
    apply hp.stateStack i (by omega) (296 - k + j) (by omega)
    rw [frame_offset initial (by omega : k ≤ 296)] at heq
    simpa only [BitVec.add_assoc, ← BitVec.ofNat_add] using heq.symm

theorem permutation_memory {boundary : ReturnBoundary} {v : Variant} {keccak : Bool} {fullState : Bool} {reset : Bool}
    {state : Incremental.State} {initial s called t : RamState}
    (hp : CallPre (keccak := keccak) (fullState := fullState) boundary v reset state initial) (h : Padded (keccak := keccak) (fullState := fullState) v reset state initial s)
    (he : (callEffect (fun _ ↦ Permutation.entryAddress .finalize)
      (outputAddress (keccak := keccak) (fullState := fullState) v reset) s).Holds s called) {a : Keccak.Lanes}
    (hr : Permutation.CallResult called t a) :
    MemoryWriteFrame called t (writeRegions (fullState := fullState) v initial) := by
  apply memoryWriteFrame_mono hr.memory
  intro region hregion address hin
  have hregions : region = ⟨(frameBase initial).toNat, 264⟩ ∨
      region = ⟨(initial.regValue .rdi).toNat, 200⟩ := by
    simpa only [Permutation.writeRegions, called_frameBase h he, called_pointer h he,
      Permutation.frameBytes, Vector.mem_mk, List.mem_toArray, List.mem_cons,
      List.not_mem_nil, or_false] using hregion
  rcases hregions with rfl | rfl
  · refine ⟨Stack.region initial frameBytes, by simp [writeRegions], ?_⟩
    rw [hp.frameRegion]
    obtain ⟨hl, hh⟩ := hin
    exact ⟨hl, by dsimp only at hh ⊢; omega⟩
  · refine ⟨⟨(initial.regValue .rdi).toNat, 201⟩, by simp [writeRegions], ?_⟩
    obtain ⟨hl, hh⟩ := hin
    exact ⟨hl, by dsimp only at hh ⊢; omega⟩


theorem permutation_advance [Bindings] {boundary : ReturnBoundary} {v : Variant} {keccak : Bool} {fullState : Bool}
    {reset : Bool} {state : Incremental.State} {initial : RamState}
    (hp : CallPre (keccak := keccak) (fullState := fullState) boundary v reset state initial) (hb : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary 6340 (Padded (keccak := keccak) (fullState := fullState) v reset state initial) Extracted.programImage
      (fun _ t ↦ Permuted (keccak := keccak) (fullState := fullState) v reset state initial t) := by
  intro s hs hcode h
  obtain ⟨called, hcall, hready, hcalledcode, he⟩ := call_step hp hb hs hcode h
  obtain ⟨t, hrun, ht, hct, hr⟩ := Permutation.call_advance .finalize boundary hb called
    hready hcalledcode (called_pre hp h he)
  have ha := called_agrees h he
  have hsavedcall : CalleeSavedRegistersUnchanged s called := by
    apply calleeSavedRegistersUnchanged_of_agreesExcept ha
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := { decide := true })
  have htop : stackTop called = outputAddress (keccak := keccak) (fullState := fullState) v reset := by
    change (Operand.mem (called.regValue .rsp) : Operand 64).read called = _
    rw [called_stack h he, ← pushAddr_padded h]
    exact he.writes.2
  refine ⟨t, hcall.trans hrun, ht, hct, {
    saved := ?_
    rbx := (permutation_slot hp h he hr (k := 16) (by decide)).trans
      ((called_slot h he (k := 16) (by decide)).trans h.rbx)
    r14 := (permutation_slot hp h he hr (k := 8) (by decide)).trans
      ((called_slot h he (k := 8) (by decide)).trans h.r14)
    returnSlot := ?_
    memory := memoryWriteFrame_trans h.memory
      (memoryWriteFrame_trans (called_memory hp h he) (permutation_memory hp h he hr))
    grows := fun a hx ↦ hr.grows a (ha.grow a (h.grows a hx))
    rest := hr.rest.trans ((ha.scalarFrame_eq (by rfl)).trans h.rest)
    stack := ?_
    stateSaved := (hr.saved .rbx (by simp)).trans
      ((hsavedcall .rbx (by simp)).trans h.stateSaved)
    output := (hr.saved .r14 (by simp)).trans
      ((hsavedcall .r14 (by simp)).trans h.output)
    rip := hr.rip.trans htop
    lanes := ?_ }⟩
  · intro r hreg
    have hmem : r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hreg ⊢
      rcases hreg with rfl | rfl | rfl | rfl <;> simp
    exact (hr.saved r hmem).trans ((hsavedcall r hmem).trans (h.saved r hreg))
  · have hslot := (permutation_slot hp h he hr (k := 0) (by decide)).trans
      (called_slot h he (k := 0) (by decide))
    simp only [BitVec.sub_zero] at hslot
    exact hslot.trans h.returnSlot
  · rw [hr.stack, called_stack h he]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  · rw [← called_pointer h he, hr.lanes, called_pointer h he, called_lanes hp h he, h.lanes]
    rfl


end Sha3.Proofs.Finalize
