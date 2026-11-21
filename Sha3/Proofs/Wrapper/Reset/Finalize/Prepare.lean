import Sha3.Proofs.Wrapper.Reset.Call
import Sha3.Proofs.Wrapper.Reset.Finalize.Output.Zero
import Sha3.Proofs.Wrapper.Finish.FinalizeCall
import Sha3.Proofs.Update.Frame

namespace Sha3.Proofs.Wrapper.Reset

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

def restorePC (v : Variant) (keccak : Bool := false)
    (fullState : Bool := false) (finalizeMode : Mode := .finalizeReset) : BitVec 64 :=
  (finalizeMode.entry v keccak fullState).entryAddress +
    (match finalizeMode with
    | .finalizeFixedReset | .digestFinalizeReset =>
      if fullState || v == .sha384 || v == .sha512 then 0x9f else 0x94
    | _ => 0x94)

def beforeOutputOperand (initial : RamState) (v : Variant) (finalizeMode : Mode)
    (keccak : Bool := false) (fullState : Bool := false) : Operand 64 :=
  match finalizeMode with
  | .finalizeFixedReset | .digestFinalizeReset =>
    if fullState then .mem (frameBase initial v finalizeMode keccak fullState + 16)
    else .reg 5
  | _ => .reg 5

def beforeOutputSource (initial : RamState) (v : Variant) (finalizeMode : Mode)
    (keccak : Bool := false) (fullState : Bool := false) : Operand 64 :=
  .mem (frameBase initial v finalizeMode keccak fullState +
    match finalizeMode with
    | .finalizeFixedReset | .digestFinalizeReset => if fullState then 16 else 8
    | _ => 8)

def restoreChanges : List Component := [.reg 5, .reg 15, .rip]

def restoreBytes (v : Variant) (fullState : Bool := false)
    (finalizeMode : Mode := .finalizeReset) : List UInt8 :=
  match finalizeMode with
  | .finalizeFixedReset | .digestFinalizeReset =>
    if fullState then [0x4c, 0x8b, 0x7c, 0x24, 0x08]
    else if v = .sha384 ∨ v = .sha512 then
      [0x4c, 0x8b, 0x3c, 0x24, 0x48, 0x8b, 0x6c, 0x24, 0x08]
    else [0x48, 0x8b, 0x6c, 0x24, 0x08]
  | _ => [0x48, 0x8b, 0x6c, 0x24, 0x08]

theorem restore_image (v : Variant) (keccak : Bool := false)
    (fullState : Bool := false) (finalizeMode : Mode := .finalizeReset)
    (hMode : finalizeMode.hasBeforeOutput = true := by decide) :
    ImageAt (restorePC v keccak fullState finalizeMode) (restoreBytes v fullState finalizeMode) := by
  cases finalizeMode <;> cases fullState <;> cases keccak <;> cases v <;>
    first | contradiction | (unfold ImageAt; decide +kernel)

def finalizeOutputPointer (initial : RamState) (v : Variant) (finalizeMode : Mode)
    (keccak : Bool := false) (fullState : Bool := false) : BitVec 64 :=
  match finalizeMode with
  | .finalizeFixedReset | .digestFinalizeReset =>
    Output.tempPointer initial v finalizeMode keccak fullState
  | _ => initial.regValue .rcx

def finalizePC (v : Variant) (keccak : Bool := false)
    (fullState : Bool := false) (finalizeMode : Mode := .finalizeReset) : BitVec 64 :=
  match finalizeMode with
  | .finalizeFixedReset | .digestFinalizeReset => Output.callPC v finalizeMode keccak fullState
  | _ => (finalizeMode.entry v keccak fullState).entryAddress + 0xa1

def finalizeDisp (v : Variant) (keccak : Bool := false)
    (fullState : Bool := false) (finalizeMode : Mode := .finalizeReset) : BitVec 32 :=
  (Finalize.entryAddress v true keccak fullState - (finalizePC v keccak fullState finalizeMode + 5)).setWidth 32

theorem finalize_target (v : Variant) (keccak : Bool := false)
    (fullState : Bool := false) (finalizeMode : Mode := .finalizeReset) :
    branchTarget (finalizePC v keccak fullState finalizeMode) 5 ((finalizeDisp v keccak fullState finalizeMode).signExtend 64) =
      Finalize.entryAddress v true keccak fullState := by cases finalizeMode <;> cases fullState <;> cases keccak <;> cases v <;>
      first | contradiction | decide +kernel

theorem finalize_code (v : Variant) (keccak : Bool := false)
    (fullState : Bool := false) (finalizeMode : Mode := .finalizeReset)
    (hMode : finalizeMode.hasBeforeOutput = true)
    (hf : fullState = true → v = .sha256 ∧ keccak = true) :
    ∀ x ∈ codeRange (finalizePC v keccak fullState finalizeMode) (encodeCallRel32 (finalizeDisp v keccak fullState finalizeMode)),
      x ∈ Extracted.programImage := by
  have h : ∀ i : Fin (encodeCallRel32 (finalizeDisp v keccak fullState finalizeMode)).length,
      Extracted.programSections.fetchByte (finalizePC v keccak fullState finalizeMode + BitVec.ofNat 64 i.val) =
        some (encodeCallRel32 (finalizeDisp v keccak fullState finalizeMode))[i.val] := by
    cases finalizeMode <;> cases fullState <;> cases keccak <;> cases v <;>
      first | contradiction | (solve | have := hf rfl; simp_all) | decide +kernel
  intro x hx
  obtain ⟨i, rfl⟩ := (mem_codeRange_iff _ _ _).mp hx
  exact imageSections_mem_toCodeMap_of_fetchByte (h i)

theorem compare_inProgram (v : Variant) (keccak : Bool := false)
    (fullState : Bool := false) : InProgram (comparePC v true keccak fullState) := by
  refine ⟨0x4d, imageSections_mem_toCodeMap_of_fetchByte ?_⟩
  cases fullState <;> cases keccak <;> cases v <;> decide +kernel

theorem restore_load [bindings : Bindings] {v : Variant} {keccak fullState : Bool}
    {m : Mode} {initial s : RamState} {inputs : Array Input} {split : Nat}
    (hCall : ValidInvocation bindings v m initial inputs split keccak fullState)
    (inv : Invariant initial v m s keccak fullState)
    (p : BitVec 64) (upper zero : Bool)
    (hp : s.RIP = p) (hs : stackPtr s = frameBase initial v m keccak fullState)
    (image : ImageAt p ((if upper then 0x4c else 0x48) :: 0x8b ::
      (AddrMode.sib 4 none 0 (if zero then .none else .d8 8)).modrm
        (if upper then 7 else 5) ::
      (AddrMode.sib 4 none 0 (if zero then .none else .d8 8)).tail)) :
    ∃ t, Advances (returnBoundary initial) 1 s t ∧
      Invariant initial v m t keccak fullState ∧
      t.RIP = p + (if zero then (4 : BitVec 64) else 5) ∧
      (Operand.reg (if upper then 15 else 5) : Operand 64).read t =
        (Operand.mem (frameBase initial v m keccak fullState + (if zero then 0 else 8)) : Operand 64).read s ∧
      AgreesExcept [.reg (if upper then 15 else 5), .rip] s t := by
  have hsp : s.GPR[4] ≠ (returnBoundary initial).rsp := by
    change stackPtr s ≠ _
    rw [hs, frameBase]
    apply Finish.stackSub_ne_returnBoundary
    cases m <;> cases v <;> cases keccak <;> cases fullState <;> decide +kernel
  have hread : MemReadable s (stackPtr s + (if zero then 0 else 8)) 8 := by
    rw [hs]
    cases zero <;> apply inv.frameReadable hCall.stackAvailable
    all_goals cases m <;> cases v <;> cases keccak <;> cases fullState <;> decide +kernel
  obtain ⟨t, ht, it, _, et, ag⟩ := advanceNoMemory (noDf := by simp) hCall
    (mov_r64_m64_effect_step p (if upper then 0x4c else 0x48)
      (by cases upper <;> unfold RexWPrefix <;> decide +kernel) (if upper then 7 else 5)
      (.sib 4 none 0 (if zero then .none else .d8 8))
      (by cases zero <;> decide +kernel)
      (by cases upper <;> cases zero <;> decide +kernel)
      (by cases upper <;> cases zero <;> decide +kernel))
    image (changes := [.reg (if upper then 15 else 5), .rip])
    (by cases upper <;> simp only [movR64M64Effect_components] <;> decide +kernel)
    (by simp [Component.Covers]) (by cases upper <;> decide +kernel)
    inv hsp ⟨hp, by cases zero <;> exact hread⟩
  refine ⟨t, ht, it, ?_, ?_, ag⟩
  · cases zero <;> exact et.rip
  · have hw : (Operand.reg (if upper then 15 else 5) : Operand 64).read t =
        (Operand.mem (stackPtr s + (if zero then 0 else 8)) : Operand 64).read s := by
      cases upper <;> cases zero <;> exact et.writes
    simpa only [hs] using hw

theorem restore_before_output [bindings : Bindings] (v : Variant) {keccak fullState : Bool}
    {finalizeMode : Mode} {initial s : RamState} {inputs : Array Input} {split : Nat}
    (hCall : ValidInvocation bindings v finalizeMode initial inputs split keccak fullState)
    (inv : Invariant initial v finalizeMode s keccak fullState)
    (hp : s.RIP = restorePC v keccak fullState finalizeMode)
    (hs : stackPtr s = frameBase initial v finalizeMode keccak fullState)
    (hMode : finalizeMode.hasBeforeOutput = true := by decide) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧
      Invariant initial v finalizeMode t keccak fullState ∧
      t.RIP = preparePC v true keccak fullState finalizeMode ∧
      (beforeOutputOperand initial v finalizeMode keccak fullState).read t =
        (beforeOutputSource initial v finalizeMode keccak fullState).read s ∧
      t.regValue .r15 =
        (if (finalizeMode = .finalizeFixedReset ∨ finalizeMode = .digestFinalizeReset) ∧
            (fullState = true ∨ v = .sha384 ∨ v = .sha512)
        then (Operand.mem (frameBase initial v finalizeMode keccak fullState +
          (if fullState then 8 else 0)) : Operand 64).read s else s.regValue .r15) ∧
      t.external = s.external ∧ AgreesExcept restoreChanges s t := by
  have noMem : ∀ c ∈ restoreChanges, ∀ address, ¬ c.Covers address := by
    simp [restoreChanges, Component.Covers]
  by_cases large : (finalizeMode = .finalizeFixedReset ∨ finalizeMode = .digestFinalizeReset) ∧
      (fullState = true ∨ v = .sha384 ∨ v = .sha512)
  · obtain ⟨u, hu, iu, pu, wu, au⟩ := restore_load hCall inv
      (restorePC v keccak fullState finalizeMode) true (!fullState) hp hs (by
        cases finalizeMode <;> cases v <;> cases fullState <;> cases keccak <;>
          first
          | (solve | exfalso; simp only [Mode.hasBeforeOutput, Bool.false_eq_true] at hMode)
          | (solve | exfalso; simp at large)
          | (unfold ImageAt; decide +kernel))
    have eu : u.external = s.external := au.external (by simp [Component.Covers])
    cases fullState
    · have hsu : stackPtr u = frameBase initial v finalizeMode keccak false :=
        (au.read (r := 4) (n := 64) (by simp)).trans hs
      obtain ⟨t, ht, it, pt, wt, agt⟩ := restore_load hCall iu
        (restorePC v keccak false finalizeMode + 4) false false
        (by exact pu) hsu (by
          cases finalizeMode <;> cases v <;> cases keccak <;>
            first
            | (solve | exfalso; simp only [Mode.hasBeforeOutput, Bool.false_eq_true] at hMode)
            | (solve | exfalso; simp at large)
            | (unfold ImageAt; decide +kernel))
      have ag : AgreesExcept restoreChanges s t :=
        (au.trans agt).mono (by simp [restoreChanges])
      refine ⟨2, t, hu.trans ht, it, ?_, ?_, ?_, ag.external noMem, ag⟩
      · apply pt.trans
        cases finalizeMode <;> cases v <;> cases keccak <;>
          first
          | (solve | exfalso; simp only [Mode.hasBeforeOutput, Bool.false_eq_true] at hMode)
          | (solve | exfalso; simp at large)
          | rfl
      · have wt' := wt
        simp only [Operand.read, eu] at wt'
        cases finalizeMode <;> simp_all [beforeOutputOperand, beforeOutputSource, Operand.read]
      · rw [ite_eq_left large]
        exact (agt.read (r := 15) (n := 64) (by simp)).trans (by exact wu)
    · have ag : AgreesExcept restoreChanges s u := au.mono (by simp [restoreChanges])
      refine ⟨1, u, hu, iu, ?_, ?_, ?_, eu, ag⟩
      · apply pu.trans
        cases finalizeMode <;> cases v <;> cases keccak <;>
          first
          | (solve | exfalso; simp only [Mode.hasBeforeOutput, Bool.false_eq_true] at hMode)
          | (solve | exfalso; simp at large)
          | rfl
      · cases finalizeMode <;> simp_all [beforeOutputOperand, beforeOutputSource, Operand.read]
      · rw [ite_eq_left large]
        exact wu
  · obtain ⟨t, ht, it, pt, wt, agt⟩ := restore_load hCall inv
      (restorePC v keccak fullState finalizeMode) false false hp hs (by
        cases finalizeMode <;> cases v <;> cases fullState <;> cases keccak <;>
          first
          | (solve | exfalso; simp only [Mode.hasBeforeOutput, Bool.false_eq_true] at hMode)
          | (solve | exfalso; simp at large)
          | (unfold ImageAt; decide +kernel))
    have ag : AgreesExcept restoreChanges s t := agt.mono (by simp [restoreChanges])
    refine ⟨1, t, ht, it, ?_, ?_, ?_, ag.external noMem, ag⟩
    · apply pt.trans
      cases finalizeMode <;> cases v <;> cases fullState <;> cases keccak <;>
        first
        | (solve | exfalso; simp only [Mode.hasBeforeOutput, Bool.false_eq_true] at hMode)
        | (solve | exfalso; simp at large)
        | rfl
    · cases finalizeMode <;> cases fullState <;>
        simp_all [beforeOutputOperand, beforeOutputSource]
    · rw [ite_eq_right large]
      exact agt.read (r := 15) (n := 64) (by simp)


theorem prepare_finalize_direct [bindings : Bindings] (v : Variant) {keccak fullState : Bool} {finalizeMode : Mode}
    {initial s : RamState} {inputs : Array Input} {split : Nat} {out : BitVec 64}
    (hCall : ValidInvocation bindings v finalizeMode initial inputs split keccak fullState)
    (inv : Invariant initial v finalizeMode s keccak fullState) (hp : s.RIP = preparePC v true keccak fullState finalizeMode)
    (hs : stackPtr s = frameBase initial v finalizeMode keccak fullState) (ho : s.regValue .rbp = out)
    (hDirect : finalizeMode = .finalizeReset ∨ finalizeMode = .digestFinalizeIntoReset) :
    ∃ t, Advances (returnBoundary initial) 2 s t ∧ Invariant initial v finalizeMode t keccak fullState ∧
      t.RIP = finalizePC v keccak fullState finalizeMode ∧ stackPtr t = frameBase initial v finalizeMode keccak fullState ∧
      t.regValue .rdi = statePointer initial v finalizeMode keccak fullState ∧ t.regValue .rsi = out ∧
      t.external = s.external ∧ AgreesExcept prepareChanges s t := by
  obtain ⟨u, hu, iu, ipu, ptru, au⟩ := prepare_state (keccak := keccak) (fullState := fullState) v true (finalizeMode := finalizeMode) hCall inv hp hs (hDirect := hDirect)
  have hspu : stackPtr u = frameBase initial v finalizeMode keccak fullState :=
    (au.read (r := 4) (n := 64) (by simp [prepareChanges])).trans hs
  have hne : u.GPR[4] ≠ (returnBoundary initial).rsp := by
    change stackPtr u ≠ _
    rw [hspu, frameBase]
    exact Finish.stackSub_ne_returnBoundary initial _ (by rcases hDirect with rfl | rfl <;> cases keccak <;> cases fullState <;> cases v <;> decide +kernel)
  obtain ⟨t, ht, it, _, et, agt⟩ := advanceNoMemory hCall
    (mov_r64_r64_effect_step (preparePC v true keccak fullState finalizeMode + 5) 0x48 0xee
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel))
    (by unfold ImageAt; rcases hDirect with rfl | rfl <;> cases keccak <;> cases fullState <;> cases v <;> decide +kernel)
    (changes := prepareChanges) (by simp only [movR64R64Effect_components]; decide +kernel)
    prepareChanges_noMem (by simp [prepareChanges]) iu hne ipu
  have ag : AgreesExcept prepareChanges s t :=
    (au.trans agt).mono (by intro c hc; exact (List.mem_append.mp hc).elim id id)
  refine ⟨t, hu.trans ht, it, et.rip.trans (by rcases hDirect with rfl | rfl <;> cases keccak <;> cases fullState <;> cases v <;> rfl),
    (ag.read (r := 4) (n := 64) (by simp [prepareChanges])).trans hs,
    ?_, ?_, ag.external prepareChanges_noMem, ag⟩
  · exact (et.agrees.read (r := 7) (n := 64)
      (by simp only [movR64R64Effect_components]; decide +kernel)).trans ptru
  · exact et.writes.trans ((au.read (r := 5) (n := 64) (by simp [prepareChanges])).trans ho)

def finalizePrepareChanges (initial : RamState) (v : Variant) (m : Mode)
    (keccak fullState : Bool) : List Component :=
  if m = .finalizeFixedReset ∨ m = .digestFinalizeReset then
    (if fullState then Output.Zero.fullChanges initial m
     else Output.Zero.prepareChanges initial v m keccak) ++ [.reg 7, .reg 6, .rip]
  else prepareChanges

theorem finalizePrepareChanges_read {initial s t : RamState} {v : Variant} {m : Mode}
    {keccak fullState : Bool} {offset width : Nat}
    (valid : fullState = true → v = .sha256 ∧ keccak = true)
    (ag : AgreesExcept (finalizePrepareChanges initial v m keccak fullState) s t)
    (hb : offset + width / 8 ≤ (if fullState then 32 else 24) ∨
      (m.stateOffset v keccak fullState ≤ offset ∧
        offset + width / 8 ≤ m.stateOffset v keccak fullState + 201)) :
    (Operand.mem (frameBase initial v m keccak fullState + BitVec.ofNat 64 offset) : Operand width).read t =
      (Operand.mem (frameBase initial v m keccak fullState + BitVec.ofNat 64 offset) : Operand width).read s := by
  by_cases hm : m = .finalizeFixedReset ∨ m = .digestFinalizeReset
  · cases fullState
    · apply memLoad_congr
      intro j hj
      simp only [memByte, PhysicalMemory.read]
      rw [ag.byte (by
        intro c hc ha
        simp only [finalizePrepareChanges, ite_eq_left hm, Bool.false_eq_true, ite_false,
          List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with hc | rfl | rfl | rfl
        · obtain ⟨i, hi, he⟩ := Output.Zero.prepareChanges_cover_temp hc ha
          have bound : offset + width / 8 ≤ 1024 := by
            rcases hm with rfl | rfl <;> cases v <;> simp only [Mode.stateOffset, Bool.false_eq_true, ↓reduceIte] at hb <;> omega
          have hd : Output.tempOffset v + v.digestBytes ≤ 2^64 := by cases v <;> decide +kernel
          have sep : Output.tempOffset v + v.digestBytes ≤ offset ∨
              offset + width / 8 ≤ Output.tempOffset v := by
            rcases hm with rfl | rfl <;> cases v <;>
              simp only [Mode.stateOffset, Bool.false_eq_true, ↓reduceIte] at hb <;>
              simp only [Output.tempOffset, Variant.digestBytes, Bool.false_eq_true, ↓reduceIte] <;> omega
          have apart := RangeApart.offsets (frameBase initial v m keccak)
            (a := Output.tempOffset v) (b := offset) (len := v.digestBytes) (count := width / 8)
            hd (by omega) sep
          exact apart i hi j hj he.symm
        all_goals exact ha.elim)]
    · obtain ⟨rfl, rfl⟩ := valid rfl
      apply Output.Zero.fullChanges_read
        (ag.mono (by
          simp only [finalizePrepareChanges, ite_eq_left hm, ite_true, List.mem_append,
            List.mem_cons, List.not_mem_nil, or_false]
          intro c hc
          rcases hc with hc | rfl | rfl | rfl
          · exact hc
          all_goals simp [Output.Zero.fullChanges, Output.Zero.fullPrepareChanges]))
      rcases hm with rfl | rfl <;> simp only [Mode.stateOffset, ↓reduceIte] at hb <;> omega
  · have ext := ag.external (by
      simp only [finalizePrepareChanges, ite_eq_right hm]
      exact prepareChanges_noMem)
    simp only [Operand.read, ext]

theorem prepare_finalize [bindings : Bindings] (v : Variant) {keccak fullState : Bool}
    {finalizeMode : Mode} {initial s : RamState} {inputs : Array Input} {split : Nat}
    (hCall : ValidInvocation bindings v finalizeMode initial inputs split keccak fullState)
    (inv : Invariant initial v finalizeMode s keccak fullState)
    (saved : SavedFrame initial s finalizeMode fullState)
    (hp : s.RIP = preparePC v true keccak fullState finalizeMode)
    (hs : stackPtr s = frameBase initial v finalizeMode keccak fullState)
    (ho : (beforeOutputOperand initial v finalizeMode keccak fullState).read s = initial.regValue .rcx)
    (hstride : UnitStringStride bindings)
    (hMode : finalizeMode.hasBeforeOutput = true := by decide) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧
      Invariant initial v finalizeMode t keccak fullState ∧
      SavedFrame initial t finalizeMode fullState ∧
      t.RIP = finalizePC v keccak fullState finalizeMode ∧
      stackPtr t = frameBase initial v finalizeMode keccak fullState ∧
      t.regValue .rdi = statePointer initial v finalizeMode keccak fullState ∧
      t.regValue .rsi = finalizeOutputPointer initial v finalizeMode keccak fullState ∧
      (fullState = true →
        (finalizeMode = .finalizeFixedReset ∨ finalizeMode = .digestFinalizeReset) →
        t.regValue .r13 = Output.tempPointer initial v finalizeMode keccak fullState) ∧
      AgreesExcept (finalizePrepareChanges initial v finalizeMode keccak fullState) s t := by
  by_cases hm : finalizeMode = .finalizeFixedReset ∨ finalizeMode = .digestFinalizeReset
  · cases fullState
    · obtain ⟨a, ha, ia, savedA, sa, pa, aa⟩ := Output.Zero.zero_steps hm hCall inv saved hs hp
      obtain ⟨b, hb, ib, pb, db, ab⟩ := Output.prepare_state v finalizeMode hm hCall ia pa sa
      have sb : stackPtr b = frameBase initial v finalizeMode keccak false :=
        (ab.read (r := 4) (n := 64) (by simp)).trans sa
      obtain ⟨t, ht, it, pt, ot, at'⟩ := Output.prepare_output v finalizeMode hm hCall ib pb sb
      have abt : AgreesExcept [.reg 7, .reg 6, .rip] a t :=
        (ab.trans at').mono (by simp)
      have et : t.external = a.external := abt.external (by simp [Component.Covers])
      refine ⟨_, t, ha.trans (hb.trans ht), it, savedA.of_external_eq et, ?_,
        (at'.read (r := 4) (n := 64) (by simp)).trans sb,
        (at'.read (r := 7) (n := 64) (by simp)).trans db, ?_, ?_, ?_⟩
      · rcases hm with rfl | rfl <;> exact pt
      · rcases hm with rfl | rfl <;> exact ot
      · intro hf; contradiction
      · simpa only [finalizePrepareChanges, ite_eq_left hm, Bool.false_eq_true, ite_false] using aa.trans abt
    · obtain ⟨rfl, rfl⟩ := hCall.fullState_valid rfl
      obtain ⟨a, ha, ia, savedA, pa, sa, ra, aa⟩ :=
        Output.Zero.full_zero_steps finalizeMode hm hCall hstride inv saved hp hs
      obtain ⟨b, hb, ib, pb, db, ab⟩ := Output.prepare_state .sha256 finalizeMode hm hCall ia pa sa
      have sb : stackPtr b = frameBase initial .sha256 finalizeMode true true :=
        (ab.read (r := 4) (n := 64) (by simp)).trans sa
      have rb : b.regValue .r13 = Output.tempPointer initial .sha256 finalizeMode true true :=
        (ab.read (r := 13) (n := 64) (by simp)).trans ra
      obtain ⟨t, ht, it, pt, ot, at'⟩ :=
        Output.prepare_full_output finalizeMode hm hCall ib pb sb rb
      have abt : AgreesExcept [.reg 7, .reg 6, .rip] a t :=
        (ab.trans at').mono (by simp)
      have et : t.external = a.external := abt.external (by simp [Component.Covers])
      refine ⟨_, t, ha.trans (hb.trans ht), it, savedA.of_external_eq et, ?_,
        (at'.read (r := 4) (n := 64) (by simp)).trans sb,
        (at'.read (r := 7) (n := 64) (by simp)).trans db, ?_, ?_, ?_⟩
      · rcases hm with rfl | rfl <;> exact pt
      · rcases hm with rfl | rfl <;> exact ot
      · intro _ _
        exact (at'.read (r := 13) (n := 64) (by simp)).trans rb
      · simpa only [finalizePrepareChanges, ite_eq_left hm, ite_true] using aa.trans abt
  · have hd : finalizeMode = .finalizeReset ∨ finalizeMode = .digestFinalizeIntoReset := by
      cases finalizeMode <;> simp_all [Mode.hasBeforeOutput]
    have ho' : s.regValue .rbp = initial.regValue .rcx := by
      rcases hd with rfl | rfl <;> exact ho
    obtain ⟨t, ht, it, pt, st, dt, ot, et, at'⟩ :=
      prepare_finalize_direct v hCall inv hp hs ho' hd
    refine ⟨2, t, ht, it, saved.of_external_eq et, pt, st, dt, ?_, ?_, ?_⟩
    · rcases hd with rfl | rfl <;> exact ot
    · intro _ h; exact (hm h).elim
    · simpa only [finalizePrepareChanges, ite_eq_right hm] using at'

theorem finalize_return_inProgram (v : Variant) (keccak : Bool := false)
    (fullState : Bool := false) (finalizeMode : Mode := .finalizeReset)
    (hMode : finalizeMode.hasBeforeOutput = true := by decide) :
    InProgram (finalizePC v keccak fullState finalizeMode + 5) := by
  refine ⟨(match finalizeMode with
    | .finalizeFixedReset | .digestFinalizeReset =>
      if fullState || v != .sha224 then 0x48 else 0x8b
    | _ => 0x4d), imageSections_mem_toCodeMap_of_fetchByte ?_⟩
  cases finalizeMode <;> cases keccak <;> cases fullState <;> cases v <;>
    first | contradiction | (dsimp only; decide +kernel)

structure FinalizeResetEntry [Bindings] (initial : RamState) (v : Variant)
    (state : Incremental.State) (s : RamState)
    (keccak : Bool := false) (fullState : Bool := false)
    (finalizeMode : Mode := .finalizeReset) : Prop where
  invariant : Invariant initial v finalizeMode s keccak fullState
  saved : SavedFrame initial s finalizeMode fullState
  rip : s.RIP = Finalize.entryAddress v true keccak fullState
  stack : s.regValue .rsp = frameBase initial v finalizeMode keccak fullState - 8
  pointer : s.regValue .rdi = statePointer initial v finalizeMode keccak fullState
  output : s.regValue .rsi = finalizeOutputPointer initial v finalizeMode keccak fullState
  state : Update.StateAt (statePointer initial v finalizeMode keccak fullState) state s
  target : stackTop s = finalizePC v keccak fullState finalizeMode + 5
  modeValid : finalizeMode.hasBeforeOutput = true
  temp : fullState = true →
    (finalizeMode = .finalizeFixedReset ∨ finalizeMode = .digestFinalizeReset) →
    s.regValue .r13 = Output.tempPointer initial v finalizeMode keccak fullState

theorem enter_finalize [bindings : Bindings] (v : Variant) {keccak fullState : Bool}
    {finalizeMode : Mode} {initial s : RamState} {inputs : Array Input} {split : Nat}
    {state : Incremental.State}
    (hCall : ValidInvocation bindings v finalizeMode initial inputs split keccak fullState)
    (inv : Invariant initial v finalizeMode s keccak fullState)
    (saved : SavedFrame initial s finalizeMode fullState)
    (hp : s.RIP = preparePC v true keccak fullState finalizeMode)
    (hs : stackPtr s = frameBase initial v finalizeMode keccak fullState)
    (ho : (beforeOutputOperand initial v finalizeMode keccak fullState).read s = initial.regValue .rcx)
    (hstate : Update.StateAt (statePointer initial v finalizeMode keccak fullState) state s)
    (hstride : UnitStringStride bindings)
    (hMode : finalizeMode.hasBeforeOutput = true := by decide) :
    ∃ fuel called, Advances (returnBoundary initial) fuel s called ∧
      FinalizeResetEntry initial v state called keccak fullState finalizeMode ∧
      (Operand.mem (outputSlot initial v finalizeMode keccak fullState) : Operand 64).read called =
        (Operand.mem (outputSlot initial v finalizeMode keccak fullState) : Operand 64).read s ∧
      (∀ offset : Nat, offset + 8 ≤ 24 →
        (Operand.mem (frameBase initial v finalizeMode keccak fullState + BitVec.ofNat 64 offset) : Operand 64).read called =
          (Operand.mem (frameBase initial v finalizeMode keccak fullState + BitVec.ofNat 64 offset) : Operand 64).read s) ∧
      AgreesExcept (finalizePrepareChanges initial v finalizeMode keccak fullState ++
        [.reg 4, .mem (frameBase initial v finalizeMode keccak fullState - 8) 8, .rip]) s called := by
  obtain ⟨fuel, u, hu, iu, su, ipu, spu, pu, ou, tempU, au⟩ :=
    prepare_finalize v hCall inv saved hp hs ho hstride hMode
  obtain ⟨called, hc, ic, ipc, spc, topc, ac, ec⟩ :=
    Finish.directCallAt (finalizeMode.frameSize v keccak fullState)
      (finalizePC v keccak fullState finalizeMode) (finalizeDisp v keccak fullState finalizeMode)
      hCall
      (by cases finalizeMode <;> cases keccak <;> cases fullState <;> cases v <;> decide +kernel)
      (by cases finalizeMode <;> cases keccak <;> cases fullState <;> cases v <;> decide +kernel)
      iu ipu spu (finalize_code v keccak fullState finalizeMode hMode hCall.fullState_valid)
      (by rw [finalize_target v keccak fullState finalizeMode]; cases keccak <;> cases fullState <;> cases v <;> decide +kernel)
  have ac' : AgreesExcept [.reg 4,
      .mem (frameBase initial v finalizeMode keccak fullState - 8) 8, .rip] u called := by
    simpa only [frameBase_sub_eight] using ac
  have savedC := su.of_localFrame (v := v) (mode := finalizeMode) ac' (by
    intro c hc address hcover
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact hcover.elim
    · obtain ⟨i, hi, rfl⟩ := hcover
      refine ⟨i, ?_, rfl⟩
      cases finalizeMode <;> cases keccak <;> cases fullState <;> cases v <;>
        simp only [Mode.frameSize, Mode.pushCount, Bool.false_eq_true, ↓reduceIte] <;> omega
    · exact hcover.elim)
  have readU {offset width : Nat}
      (hb : offset + width / 8 ≤ (if fullState then 32 else 24) ∨
        (finalizeMode.stateOffset v keccak fullState ≤ offset ∧
          offset + width / 8 ≤ finalizeMode.stateOffset v keccak fullState + 201)) :
      (Operand.mem (frameBase initial v finalizeMode keccak fullState + BitVec.ofNat 64 offset) : Operand width).read u =
        (Operand.mem (frameBase initial v finalizeMode keccak fullState + BitVec.ofNat 64 offset) : Operand width).read s :=
    finalizePrepareChanges_read hCall.fullState_valid au hb
  have stateU : Update.StateAt (statePointer initial v finalizeMode keccak fullState) state u := by
    constructor
    · refine Eq.trans ?_ hstate.lanes
      funext i
      have he := readU (offset := finalizeMode.stateOffset v keccak fullState + 8 * i.val)
        (width := 64) (Or.inr (by have := i.isLt; constructor <;> omega))
      simpa only [Permutation.memoryLanes, statePointer, BitVec.ofNat_add, BitVec.add_assoc] using he
    · refine Eq.trans ?_ hstate.cursor
      unfold Update.cursor
      congr 1
      have he := readU (offset := finalizeMode.stateOffset v keccak fullState + 200)
        (width := 8) (Or.inr (by constructor <;> omega))
      simpa only [statePointer, BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using he
  have stateC : Update.StateAt (statePointer initial v finalizeMode keccak fullState) state called := by
    apply stateU.of_bytes_eq
    intro i hi
    have he := Finish.callMemory_above ec
      (offset := finalizeMode.stateOffset v keccak fullState) (count := 201)
      (by cases finalizeMode <;> cases keccak <;> cases fullState <;> cases v <;> decide +kernel) i hi
    simpa only [spu, statePointer] using he
  refine ⟨_, called, hu.trans hc,
    ⟨ic, savedC, ipc.trans (finalize_target v keccak fullState finalizeMode),
      by
        change stackPtr called = _
        simpa only [frameBase_sub_eight] using spc,
      (ac'.read (r := 7) (n := 64) (by simp)).trans pu,
      (ac'.read (r := 6) (n := 64) (by simp)).trans ou, stateC, topc, hMode, fun hf hm ↦
        (ac'.read (r := 13) (n := 64) (by simp)).trans (tempU hf hm)⟩,
    ?_, ?_, au.trans ac'⟩
  · have he := Finish.callRead_above ec
      (offset := finalizeMode.outputSlotOffset v keccak fullState) (width := 64)
      (by cases finalizeMode <;> cases keccak <;> cases fullState <;> cases v <;> decide +kernel)
    have he' := readU (offset := finalizeMode.outputSlotOffset v keccak fullState)
      (width := 64) (Or.inl (by
        cases finalizeMode <;> cases keccak <;> cases fullState <;> cases v <;>
          first | contradiction | decide +kernel))
    refine Eq.trans ?_ he'
    simpa only [spu, outputSlot] using he
  · intro offset hb
    have he := Finish.callRead_above ec (offset := offset) (width := 64) (by omega)
    have he' := readU (offset := offset) (width := 64)
      (Or.inl (by cases fullState <;> simp_all only [Bool.false_eq_true, ↓reduceIte] <;> omega))
    refine Eq.trans ?_ he'
    simpa only [spu] using he

end Sha3.Proofs.Wrapper.Reset
