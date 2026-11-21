import Sha3.Proofs.Finalize.Prologue
import Sha3.Proofs.Finalize.Frame
import Sha3.Proofs.Finalize.Padding

namespace Sha3.Proofs.Finalize

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

theorem Prologue.PushProgress.savedFrame {boundary : ReturnBoundary} {v : Variant} {keccak : Bool} {fullState : Bool}
    {reset : Bool} {state : Incremental.State} {initial s : RamState}
    (hp : CallPre (keccak := keccak) (fullState := fullState) boundary v reset state initial) (hs : PushProgress (keccak := keccak) (fullState := fullState) v reset initial 3 s) :
    SavedFrame (fullState := fullState) v initial s := by
  refine ⟨?_, hs.saved ⟨1, by decide⟩ (by decide),
    hs.saved ⟨0, by decide⟩ (by decide), hs.returnSlot, ?_, hs.grow, hs.rest⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hs.registers 5 (by decide)
    · exact hs.registers 12 (by decide)
    · exact hs.registers 13 (by decide)
    · exact hs.registers 15 (by decide)
  · apply memoryWriteFrame_mono hs.memory
    intro region hregion address hin
    have he : region = ⟨(frameBase initial).toNat, frameBytes⟩ := by simpa using hregion
    subst region
    refine ⟨Stack.region initial frameBytes, by simp [writeRegions], ?_⟩
    exact (EntryStackPre.mk hp.rip hp.stack hp.stackAvoid).frame_subset hin

theorem Prologue.PushProgress.state_byte {boundary : ReturnBoundary} {v : Variant} {keccak : Bool} {fullState : Bool}
    {reset : Bool} {state : Incremental.State} {initial s : RamState} {k : Nat}
    (hp : CallPre (keccak := keccak) (fullState := fullState) boundary v reset state initial) (hs : PushProgress (keccak := keccak) (fullState := fullState) v reset initial k s)
    {i : Nat} (hi : i < 201) :
    s.external[initial.regValue .rdi + BitVec.ofNat 64 i]? =
      initial.external[initial.regValue .rdi + BitVec.ofNat 64 i]? := by
  apply hs.memory
  intro region hregion hin
  have he : region = ⟨(frameBase initial).toNat, frameBytes⟩ := by simpa using hregion
  subst region
  obtain ⟨j, hj, heq⟩ := region_contains_offset hin
  exact hp.stateStack i hi j (by change j < 296 at hj; omega) heq

def preparationClobbers (ptr : BitVec 64) : List Component :=
  .reg 3 :: Padding.clobbers ptr

theorem preparation_stack_read {boundary : ReturnBoundary} {v : Variant} {keccak : Bool} {fullState : Bool} {reset : Bool}
    {state : Incremental.State} {initial s t : RamState}
    (hp : CallPre (keccak := keccak) (fullState := fullState) boundary v reset state initial)
    (ha : AgreesExcept (preparationClobbers (initial.regValue .rdi)) s t)
    {offset : Nat} (hspan : offset + 8 ≤ 304) :
    (Operand.mem (frameBase initial + BitVec.ofNat 64 offset) : Operand 64).read t =
      (Operand.mem (frameBase initial + BitVec.ofNat 64 offset) : Operand 64).read s := by
  apply read_of_agrees ha
  intro i hi c hc hcover
  simp only [preparationClobbers, Padding.clobbers, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcover.elim
  obtain ⟨j, hj, he⟩ := hcover
  rw [BitVec.add_assoc, ← BitVec.ofNat_add] at he
  exact hp.stateStack j hj (offset + i) (by omega) he.symm

theorem SavedFrame.of_preparation {boundary : ReturnBoundary} {v : Variant} {keccak : Bool} {fullState : Bool} {reset : Bool}
    {state : Incremental.State} {initial s t : RamState}
    (hp : CallPre (keccak := keccak) (fullState := fullState) boundary v reset state initial) (hs : SavedFrame (fullState := fullState) v initial s)
    (ha : AgreesExcept (preparationClobbers (initial.regValue .rdi)) s t) :
    SavedFrame (fullState := fullState) v initial t := by
  refine ⟨?_, ?_, ?_, ?_, ?_, fun a h ↦ ha.grow a (hs.grows a h),
    (ha.scalarFrame_eq (by rfl)).trans hs.rest⟩
  · intro r hr
    apply Eq.trans ?_ (hs.saved r hr)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ha.read (n := 64) (r := 5) (by
        simp (config := { decide := true }) [preparationClobbers, Padding.clobbers])
    · exact ha.read (n := 64) (r := 12) (by
        simp (config := { decide := true }) [preparationClobbers, Padding.clobbers])
    · exact ha.read (n := 64) (r := 13) (by
        simp (config := { decide := true }) [preparationClobbers, Padding.clobbers])
    · exact ha.read (n := 64) (r := 15) (by
        simp (config := { decide := true }) [preparationClobbers, Padding.clobbers])
  · have he : initial.regValue .rsp - 16 = frameBase initial + BitVec.ofNat 64 280 := by
      simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rfl
    rw [he, preparation_stack_read hp ha (by decide), ← he]
    exact hs.rbx
  · have he : initial.regValue .rsp - 8 = frameBase initial + BitVec.ofNat 64 288 := by
      simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rfl
    rw [he, preparation_stack_read hp ha (by decide), ← he]
    exact hs.r14
  · have he : initial.regValue .rsp = frameBase initial + BitVec.ofNat 64 296 := by
      simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]
      simp
    rw [he, preparation_stack_read hp ha (by decide), ← he]
    exact hs.returnSlot
  · apply memoryWriteFrame_trans hs.memory
    apply ha.memoryWriteFrame
    intro c hc address hcover
    simp only [preparationClobbers, Padding.clobbers, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcover.elim
    obtain ⟨i, hi, rfl⟩ := hcover
    exact ⟨⟨(initial.regValue .rdi).toNat, 201⟩, by simp [writeRegions],
      region_contains_byte hp.stateRead.low hi⟩

theorem save_state_code (v : Variant) (reset : Bool)
    (keccak : Bool := false) (fullState : Bool := false)
    (valid : fullState = true → v = .sha256 ∧ keccak = true := by simp_all) :
    ∀ x ∈ codeRange (entryAddress (keccak := keccak) (fullState := fullState) v reset + 4) [0x48, 0x89, 0xfb],
      x ∈ Extracted.programImage := by
  have h : ∀ i : Fin 3,
      Extracted.programSections.fetchByte (entryAddress (keccak := keccak) (fullState := fullState) v reset + 4 + BitVec.ofNat 64 i.val) =
        some ([0x48, 0x89, 0xfb] : List UInt8)[i.val] := by
    cases v <;> cases reset <;> cases keccak <;> cases fullState <;>
      simp_all <;> decide +kernel
  intro x hx
  obtain ⟨i, rfl⟩ := (mem_codeRange_iff _ _ _).mp hx
  exact imageSections_mem_toCodeMap_of_fetchByte (h i)

theorem padding_start_inProgram (v : Variant) (reset : Bool)
    (keccak : Bool := false) (fullState : Bool := false)
    (valid : fullState = true → v = .sha256 ∧ keccak = true := by simp_all) :
    InProgram (entryAddress (keccak := keccak) (fullState := fullState) v reset + 7) := by
  apply Exists.intro 0x0f
  apply imageSections_mem_toCodeMap_of_fetchByte
  cases v <;> cases reset <;> cases keccak <;> cases fullState <;>
      simp_all <;> decide +kernel

theorem prepare_advance (v : Variant) (reset : Bool) (state : Incremental.State)
    [Bindings] (boundary : ReturnBoundary) (hboundary : ¬ InProgram boundary.rip) (keccak : Bool := false) (fullState : Bool := false) :
    AdvanceTriple boundary 12 (CallPre (keccak := keccak) (fullState := fullState) boundary v reset state) Extracted.programImage
      (Padded (keccak := keccak) (fullState := fullState) v reset state) := by
  intro initial hready hcode hp
  obtain ⟨s₁, hrun₁, hr₁, hc₁, hs₁⟩ :=
    Prologue.pushes_advance_program (keccak := keccak) (fullState := fullState) v reset boundary hboundary initial hready hcode
      ⟨hp.rip, hp.stack, hp.stackAvoid⟩
  obtain ⟨s₂, hrun₂, hr₂, he₂⟩ :=
    (mov_r64_r64_effect_step (entryAddress (keccak := keccak) (fullState := fullState) v reset + 4) 0x48 0xfb
      (by unfold RexWPrefix; decide) (by decide)).advances hr₁
      (hc₁.mono (save_state_code (keccak := keccak) (fullState := fullState) v reset (valid := hp.valid))) hs₁.rip (by
        change entryAddress (keccak := keccak) (fullState := fullState) v reset + 4 + 3 ≠ boundary.rip
        rw [BitVec.add_assoc]
        exact fun he ↦ hboundary (he ▸ padding_start_inProgram (keccak := keccak) (fullState := fullState) v reset (valid := hp.valid)))
  have ha₂ : AgreesExcept [.reg 3, .rip] s₁ s₂ := he₂.agrees
  have hm₂ : s₂.external = s₁.external :=
    ha₂.external (by simp [Component.Covers])
  have hc₂ : CodeIn Extracted.programImage s₂ := hc₁.of_external_eq hm₂
  have hstack₂ : (Operand.reg 4 : Operand 64).read s₂ = initial.regValue .rsp - 24 :=
    (ha₂.read (r := 4) (by decide)).trans hs₁.stack
  have hptr₂ : (Operand.reg 7 : Operand 64).read s₂ = initial.regValue .rdi :=
    (ha₂.read (r := 7) (by decide)).trans (hs₁.registers 7 (by decide))
  have hout₂ : (Operand.reg 6 : Operand 64).read s₂ = initial.regValue .rsi :=
    (ha₂.read (r := 6) (by decide)).trans (hs₁.registers 6 (by decide))
  have hsaved₂ : (Operand.reg 3 : Operand 64).read s₂ = initial.regValue .rdi :=
    he₂.writes.trans (hs₁.registers 7 (by decide))
  have hcontext : Padding.Context boundary (initial.regValue .rsp - 24)
      (initial.regValue .rdi) s₂ :=
    ⟨hr₂, fun a b h ↦ (hc₂ (a, b) h).2, hstack₂, hptr₂,
      readable_of_grows (fun a h ↦ ha₂.grow a (hs₁.grow a h)) hp.stateRead,
      hp.stateAvoid, hp.boundary⟩
  have hmeta : (Operand.mem (initial.regValue .rdi + 200) : Operand 8).read s₂ =
      BitVec.ofNat 8 state.cursor := by
    apply Eq.trans ?_ hp.metadata
    apply memLoad_congr
    intro i hi
    have hi0 : i = 0 := by omega
    subst i
    change (s₂.external[initial.regValue .rdi + 200 + BitVec.ofNat 64 0]?).getD 0 = _
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    rw [hm₂, hs₁.state_byte hp (by decide : 200 < 201)]
    rfl
  have hbytes : Bytes s₂.external (initial.regValue .rdi) 200
      (fun i ↦ memByte initial.external (initial.regValue .rdi + BitVec.ofNat 64 i)) := by
    intro i hi
    rw [hm₂, hs₁.state_byte hp (by omega)]
    exact Bytes.of_isSome hp.stateRead.mem i (by omega)
  have hip₂ : s₂.RIP = entryAddress (keccak := keccak) (fullState := fullState) v reset + (7 : BitVec 64) := by
    simpa only [movR64R64Effect, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.ofNat_eq_ofNat] using he₂.rip
  let cursor : Fin 200 := ⟨state.cursor, Nat.lt_of_lt_of_le hp.cursor v.rate_le⟩
  obtain ⟨s₃, hrun₃, hc₃, hip₃, ha₃, hout₃, hb₃⟩ :=
    Padding.steps (keccak := keccak) (fullState := fullState) (v := v) (reset := reset) hcontext cursor hmeta hip₂ hbytes hp.valid
  have ha : AgreesExcept (preparationClobbers (initial.regValue .rdi)) s₁ s₃ :=
    (ha₂.trans ha₃).mono (by
      simp (config := { decide := true }) [preparationClobbers, Padding.clobbers])
  have hf : SavedFrame (fullState := fullState) v initial s₃ := (hs₁.savedFrame hp).of_preparation hp ha
  refine ⟨s₃, (hrun₁.trans hrun₂).trans hrun₃, hc₃.ready,
    CodeIn.of_loaded hc₃.loaded (SectionsLow.codeLow programSections_low), ?_⟩
  refine ⟨⟨hf, hc₃.stack, ?_, hout₃.trans hout₂⟩, hip₃, hc₃.state, ?_⟩
  · exact (ha₃.read (r := 3) (by
      simp (config := { decide := true }) [Padding.clobbers])).trans hsaved₂
  · have hlanes := Padding.padded_memoryLanes_eq state.cursor v.rate v.rate_pos hb₃
    rw [hp.lanes] at hlanes
    exact hlanes

end Sha3.Proofs.Finalize
