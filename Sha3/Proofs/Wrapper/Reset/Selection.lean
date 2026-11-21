import Sha3.Proofs.Wrapper.Loop.Layout
import X86Proofs.Instructions.NopMem.Triple
import Sha3.Proofs.Wrapper.Frame
import Sha3.Proofs.Wrapper.Setup.Basic
import Sha3.Proofs.X86.Instructions.Cmp.Triple
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Lea.Triple

namespace Sha3.Proofs.Wrapper.Reset

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

def mode (finalize : Bool) (finalizeMode : Mode := .finalizeReset) : Mode :=
  if finalize then finalizeMode else .reset

def selectionKind (finalize : Bool) (finalizeMode : Mode := .finalizeReset) : Loop.Kind :=
  if finalize then match finalizeMode with
    | .finalizeFixedReset => .secondFinalizeFixedReset
    | .digestFinalizeIntoReset => .secondDigestFinalizeIntoReset
    | .digestFinalizeReset => .secondDigestFinalizeReset
    | _ => .secondFinalizeReset
  else .secondReset

def comparePC (v : Variant) (finalize : Bool)
    (keccak : Bool := false) (fullState : Bool := false)
    (finalizeMode : Mode := .finalizeReset) : BitVec 64 :=
  ((mode finalize finalizeMode).entry v keccak fullState).entryAddress +
    (if !finalize then 0x96 else match finalizeMode with
    | .finalizeFixedReset | .digestFinalizeReset =>
      if fullState then 0xf6 else match v with
      | .sha224 => 0x103 | .sha256 => 0x107 | .sha384 => 0x144 | .sha512 => 0x184
    | _ => 0xa6)

def loopPC (v : Variant) (finalize : Bool)
    (keccak : Bool := false) (fullState : Bool := false)
    (finalizeMode : Mode := .finalizeReset) : BitVec 64 :=
  (selectionKind finalize finalizeMode).start v keccak fullState

def finishPC (v : Variant) (finalize : Bool)
    (keccak : Bool := false) (fullState : Bool := false)
    (finalizeMode : Mode := .finalizeReset) : BitVec 64 :=
  (selectionKind finalize finalizeMode).exit v keccak fullState

def stateMode (finalize : Bool) (finalizeMode : Mode := .finalizeReset)
    (v : Variant := .sha256) (fullState : Bool := false) : AddrMode :=
  .sib 4 none 0 (if finalize && (finalizeMode == .finalizeFixedReset ||
    finalizeMode == .digestFinalizeReset) && !fullState then
      .d32 (BitVec.ofNat 32 ((mode finalize finalizeMode).stateOffset v false fullState))
    else .d8 (BitVec.ofNat 8 ((mode finalize finalizeMode).stateOffset v false fullState)))

def indexReg (finalize : Bool) (finalizeMode : Mode := .finalizeReset)
    (v : Variant := .sha256) (fullState : Bool := false) : BitVec 5 :=
  (selectionKind finalize finalizeMode).indexReg v fullState

def stateReg (finalize : Bool) (finalizeMode : Mode := .finalizeReset)
    (v : Variant := .sha256) (fullState : Bool := false) : BitVec 5 :=
  (selectionKind finalize finalizeMode).stateReg v fullState

def selectionChanges (finalize : Bool) (finalizeMode : Mode := .finalizeReset)
    (v : Variant := .sha256) (fullState : Bool := false) : List Component :=
  [.reg (stateReg finalize finalizeMode v fullState), .flags, .rip] ++
    if (selectionKind finalize finalizeMode).largeFollower v fullState then [.reg 5] else []

theorem selectionChanges_noMem (finalize : Bool) (finalizeMode : Mode := .finalizeReset)
    (v : Variant := .sha256) (fullState : Bool := false) :
    ∀ c ∈ selectionChanges finalize finalizeMode v fullState, ∀ address, ¬ c.Covers address := by
  cases fullState <;> cases finalize <;> cases finalizeMode <;> cases v <;>
    simp [selectionChanges, selectionKind, Loop.Kind.largeFollower, Component.Covers]

theorem advanceNoMemory [bindings : Bindings] {initial s : RamState} {v : Variant}
    {wrapperMode : Mode} {keccak fullState : Bool} {inputs : Array Input} {split : Nat} {boundary : ReturnBoundary}
    {p : BitVec 64} {bytes : List UInt8} {pre : RamState → Prop}
    {effect : RamState → Effect} {changes : List Component}
    (hCall : ValidInvocation bindings v wrapperMode initial inputs split keccak fullState)
    (step : StepEffect pre (codeRange p bytes) effect) (image : ImageAt p bytes)
    (frame : ∀ c ∈ (effect s).components, c ∈ changes)
    (noMem : ∀ c ∈ changes, ∀ address, ¬ c.Covers address)
    (noRsp : Component.reg 4 ∉ changes)
    (inv : Invariant initial v wrapperMode s keccak fullState)
    (sp : s.GPR[4] ≠ boundary.rsp) (hp : pre s)
    (noDf : .df ∉ changes := by decide) :
    ∃ t, Advances boundary 1 s t ∧ Invariant initial v wrapperMode t keccak fullState ∧
      t.GPR[4] ≠ boundary.rsp ∧ (effect s).Holds s t ∧
      AgreesExcept changes s t := by
  obtain ⟨t, ht, hr, he⟩ := step s inv.ready (image.code inv.loaded) hp
  have ha := he.agrees.mono frame
  have hsp : t.GPR[4] = s.GPR[4] :=
    ha.agree (.reg 4) noRsp rfl
  refine ⟨t, Advances.of_step ht (.inr (hsp ▸ sp)),
    inv.of_agreesExcept hCall hr ha ?_ noDf, hsp ▸ sp, he, ha⟩
  intro c hc address hcover
  exact (noMem c hc address hcover).elim

def compareRex (finalize : Bool) (finalizeMode : Mode) (v : Variant)
    (fullState : Bool) : UInt8 :=
  if indexReg finalize finalizeMode v fullState = 13 then 0x4d else 0x4c

def compareModrm (finalize : Bool) (finalizeMode : Mode) (v : Variant)
    (fullState : Bool) : UInt8 :=
  if indexReg finalize finalizeMode v fullState = 13 then 0xfd else 0xfb

def selectionBranch (finalize : Bool) (finalizeMode : Mode) (v : Variant)
    (fullState : Bool) : BitVec 8 :=
  if !finalize then 0x29 else match finalizeMode with
  | .finalizeFixedReset | .digestFinalizeReset =>
    if fullState then 0x36 else match v with
    | .sha224 => 0x2c | .sha256 => 0x38 | .sha384 | .sha512 => 0x37
  | _ => 0x29

def stateRex (finalize : Bool) (finalizeMode : Mode) (v : Variant)
    (fullState : Bool) : UInt8 :=
  if stateReg finalize finalizeMode v fullState = 13 then 0x4c else 0x48

def cursorMode (v : Variant) (finalizeMode : Mode) (fullState : Bool) : AddrMode :=
  .sib 4 none 0 (.d32 (BitVec.ofNat 32 (finalizeMode.stateOffset v false fullState + 200)))

def selectionStatePC (v : Variant) (finalize : Bool) (keccak fullState : Bool)
    (finalizeMode : Mode) : BitVec 64 :=
  comparePC v finalize keccak fullState finalizeMode +
    if (selectionKind finalize finalizeMode).largeFollower v fullState then 13 else 5

theorem compare_image (v : Variant) (finalize : Bool)
    (keccak : Bool := false) (fullState : Bool := false)
    (finalizeMode : Mode := .finalizeReset)
    (hMode : finalizeMode.hasBeforeOutput = true := by decide) :
    ImageAt (comparePC v finalize keccak fullState finalizeMode)
      [compareRex finalize finalizeMode v fullState, 0x39,
        compareModrm finalize finalizeMode v fullState] := by
  cases fullState <;> cases keccak <;> cases finalize <;> cases finalizeMode <;>
    cases v <;> first | contradiction | (unfold ImageAt; decide +kernel)

theorem branch_image (v : Variant) (finalize : Bool)
    (keccak : Bool := false) (fullState : Bool := false)
    (finalizeMode : Mode := .finalizeReset)
    (hMode : finalizeMode.hasBeforeOutput = true := by decide) :
    ImageAt (comparePC v finalize keccak fullState finalizeMode + (3 : BitVec 64))
      [0x73, UInt8.ofNat (selectionBranch finalize finalizeMode v fullState).toNat] := by
  cases fullState <;> cases keccak <;> cases finalize <;> cases finalizeMode <;>
    cases v <;> first | contradiction | (unfold ImageAt; decide +kernel)

theorem lea_image (v : Variant) (finalize : Bool)
    (keccak : Bool := false) (fullState : Bool := false)
    (finalizeMode : Mode := .finalizeReset)
    (hMode : finalizeMode.hasBeforeOutput = true := by decide) :
    ImageAt (selectionStatePC v finalize keccak fullState finalizeMode)
      (stateRex finalize finalizeMode v fullState :: 0x8d ::
        (stateMode finalize finalizeMode v fullState).modrm 5 ::
        (stateMode finalize finalizeMode v fullState).tail) := by
  cases fullState <;> cases keccak <;> cases finalize <;> cases finalizeMode <;>
    cases v <;> first | contradiction | (unfold ImageAt; decide +kernel)

theorem compare_cf (finalize : Bool) {s t : RamState} {p : BitVec 64} {i count : Nat}
    {finalizeMode : Mode} {v : Variant}
    {fullState : Bool}
    (hi : i < 2^64) (hn : count < 2^64)
    (hindex : (Operand.reg (indexReg finalize finalizeMode v fullState) : Operand 64).read s = BitVec.ofNat 64 i)
    (hcount : (Operand.reg 15 : Operand 64).read s = BitVec.ofNat 64 count)
    (he : (cmpR64R64Effect p (indexReg finalize finalizeMode v fullState) 15 s).Holds s t) :
    (StatusFlags.ofRFLAGS t.RFLAGS).CF = decide (i < count) := by
  have hflags := he.flags
  change StatusFlagsOutcome.Allows (.ofStatusFlags (cmpSpec
    ((Operand.reg (indexReg finalize finalizeMode v fullState) : Operand 64).read s) ((Operand.reg 15 : Operand 64).read s)))
    (StatusFlags.ofRFLAGS t.RFLAGS) at hflags
  have hcf := hflags.1
  simpa only [StatusFlagsOutcome.ofStatusFlags, FlagAllows, cmpSpec, subSpec, hindex, hcount,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hn] using hcf

theorem selection_branch_target (v : Variant) (finalize keccak fullState : Bool)
    (finalizeMode : Mode) (hMode : finalizeMode.hasBeforeOutput = true) :
    (comparePC v finalize keccak fullState finalizeMode + (3 : BitVec 64)) + (2 : BitVec 64) +
      (selectionBranch finalize finalizeMode v fullState).signExtend 64 =
      finishPC v finalize keccak fullState finalizeMode := by
  cases fullState <;> cases keccak <;> cases finalize <;> cases finalizeMode <;> cases v <;>
    first | contradiction | decide +kernel

theorem compare_step [Bindings] (v : Variant) (finalize keccak fullState : Bool)
    (finalizeMode : Mode) :
    StepEffect (fun s ↦ s.RIP = comparePC v finalize keccak fullState finalizeMode)
      (codeRange (comparePC v finalize keccak fullState finalizeMode)
        [compareRex finalize finalizeMode v fullState, 0x39,
          compareModrm finalize finalizeMode v fullState])
      (cmpR64R64Effect (comparePC v finalize keccak fullState finalizeMode)
        (indexReg finalize finalizeMode v fullState) 15) := by
  cases fullState <;> cases finalize <;> cases finalizeMode <;> cases v <;>
    exact cmp_r64_r64_effect_step _ _ _ (by unfold RexWPrefix; decide) (by decide)

theorem selectionChanges_noRsp (v : Variant) (finalize fullState : Bool)
    (finalizeMode : Mode) : Component.reg 4 ∉ selectionChanges finalize finalizeMode v fullState := by
  cases fullState <;> cases finalize <;> cases finalizeMode <;> cases v <;> decide +kernel

theorem state_step [Bindings] (v : Variant) (finalize keccak fullState : Bool)
    (finalizeMode : Mode) :
    StepEffect (fun s ↦ s.RIP = selectionStatePC v finalize keccak fullState finalizeMode)
      (codeRange (selectionStatePC v finalize keccak fullState finalizeMode)
        (stateRex finalize finalizeMode v fullState :: 0x8d ::
          (stateMode finalize finalizeMode v fullState).modrm 5 ::
          (stateMode finalize finalizeMode v fullState).tail))
      (leaR64Effect (selectionStatePC v finalize keccak fullState finalizeMode)
        (stateReg finalize finalizeMode v fullState) (stateMode finalize finalizeMode v fullState)) := by
  cases fullState <;> cases finalize <;> cases finalizeMode <;> cases v <;>
    exact lea_r64_effect_step _ _ (by unfold RexWPrefix; decide) 5 _ (by decide) (by decide) (by decide)

theorem stateMode_addr (v : Variant) (finalize keccak fullState : Bool)
    (finalizeMode : Mode) (hMode : finalizeMode.hasBeforeOutput = true)
    (s : RamState) (p : BitVec 64) :
    (stateMode finalize finalizeMode v fullState).addr s p =
      (Operand.reg 4 : Operand 64).read s +
        BitVec.ofNat 64 ((mode finalize finalizeMode).stateOffset v keccak fullState) := by
  cases fullState <;> cases keccak <;> cases finalize <;> cases finalizeMode <;> cases v <;>
    first | contradiction | rfl

theorem selection_cursorReg (v : Variant) (finalize fullState : Bool) (finalizeMode : Mode) :
    (selectionKind finalize finalizeMode).cursorReg v fullState =
      if (selectionKind finalize finalizeMode).largeFollower v fullState then some 5 else none := by
  cases fullState <;> cases finalize <;> cases finalizeMode <;> cases v <;> rfl

theorem cursor_image (v : Variant) (finalize keccak fullState : Bool) (finalizeMode : Mode)
    (hMode : finalizeMode.hasBeforeOutput = true)
    (large : (selectionKind finalize finalizeMode).largeFollower v fullState = true) :
    ImageAt (comparePC v finalize keccak fullState finalizeMode + (5 : BitVec 64))
      (0x48 :: 0x8d :: (cursorMode v finalizeMode fullState).modrm 5 ::
        (cursorMode v finalizeMode fullState).tail) := by
  cases fullState <;> cases keccak <;> cases finalize <;> cases finalizeMode <;> cases v <;>
    first | contradiction | (unfold ImageAt; decide +kernel)

theorem cursorMode_addr (v : Variant) (finalize keccak fullState : Bool) (finalizeMode : Mode)
    (large : (selectionKind finalize finalizeMode).largeFollower v fullState = true)
    (s : RamState) (p : BitVec 64) :
    (cursorMode v finalizeMode fullState).addr s p = (Operand.reg 4 : Operand 64).read s +
      BitVec.ofNat 64 ((mode finalize finalizeMode).stateOffset v keccak fullState + 200) := by
  cases fullState <;> cases keccak <;> cases finalize <;> cases finalizeMode <;> cases v <;>
    first | contradiction | rfl

theorem cursor_ne_state (v : Variant) (finalize fullState : Bool) (finalizeMode : Mode)
    (r : BitVec 5) (hr : (selectionKind finalize finalizeMode).cursorReg v fullState = some r) :
    r ≠ stateReg finalize finalizeMode v fullState := by
  cases fullState <;> cases finalize <;> cases finalizeMode <;> cases v <;>
    simp_all [selectionKind, Loop.Kind.cursorReg, Loop.Kind.largeFollower,
      stateReg, Loop.Kind.stateReg] <;> subst r <;> decide +kernel

def selectionNopPC (v : Variant) (finalize keccak fullState : Bool) (finalizeMode : Mode) : BitVec 64 :=
  selectionStatePC v finalize keccak fullState finalizeMode +
    BitVec.ofNat 64 (leaLen (stateMode finalize finalizeMode v fullState))

def selectionNopPre (v : Variant) (finalize fullState : Bool) (finalizeMode : Mode) : List UInt8 :=
  if (selectionKind finalize finalizeMode).largeFollower v fullState then [] else [0x66, 0x66, 0x66, 0x2e]

def selectionNopMode (v : Variant) (finalize fullState : Bool) (finalizeMode : Mode) : AddrMode :=
  if !fullState && (selectionKind finalize finalizeMode).largeFollower v fullState then
    .base 0 (.d32 0) else .sib 0 (some 0) 0 (.d32 0)

theorem selection_nop_step [Bindings] (v : Variant) (finalize keccak fullState : Bool)
    (finalizeMode : Mode) :
    StepEffect (fun s ↦ s.RIP = selectionNopPC v finalize keccak fullState finalizeMode)
      (codeRange (selectionNopPC v finalize keccak fullState finalizeMode)
        (encodeNopM (selectionNopPre v finalize fullState finalizeMode)
          (selectionNopMode v finalize fullState finalizeMode)))
      (fun _ ↦ nopEffect (selectionNopPC v finalize keccak fullState finalizeMode)
        (nopMemLen (selectionNopPre v finalize fullState finalizeMode)
          (selectionNopMode v finalize fullState finalizeMode))) := by
  cases fullState <;> cases finalize <;> cases finalizeMode <;> cases v <;>
    exact nop_m_effect_step _ _ (by decide) (by decide) _ (by decide) rfl rfl

theorem selection_nop_image (v : Variant) (finalize keccak fullState : Bool)
    (finalizeMode : Mode) (hMode : finalizeMode.hasBeforeOutput = true)
    (hn : selectionNopPC v finalize keccak fullState finalizeMode ≠
      loopPC v finalize keccak fullState finalizeMode) :
    ImageAt (selectionNopPC v finalize keccak fullState finalizeMode)
      (encodeNopM (selectionNopPre v finalize fullState finalizeMode)
        (selectionNopMode v finalize fullState finalizeMode)) := by
  cases fullState <;> cases keccak <;> cases finalize <;> cases finalizeMode <;> cases v <;>
    first | contradiction | (exfalso; apply hn; decide +kernel) | (unfold ImageAt; decide +kernel)

theorem selection_nop_target (v : Variant) (finalize keccak fullState : Bool)
    (finalizeMode : Mode) (hMode : finalizeMode.hasBeforeOutput = true)
    (hn : selectionNopPC v finalize keccak fullState finalizeMode ≠
      loopPC v finalize keccak fullState finalizeMode) :
    selectionNopPC v finalize keccak fullState finalizeMode +
      BitVec.ofNat 64 (nopMemLen (selectionNopPre v finalize fullState finalizeMode)
        (selectionNopMode v finalize fullState finalizeMode)) =
      loopPC v finalize keccak fullState finalizeMode := by
  cases fullState <;> cases keccak <;> cases finalize <;> cases finalizeMode <;> cases v <;>
    first | contradiction | (exfalso; apply hn; decide +kernel) | decide +kernel

set_option maxHeartbeats 1600000 in
theorem selection [bindings : Bindings] (v : Variant) (finalize : Bool)
    {keccak fullState : Bool} {finalizeMode : Mode}
    {initial s : RamState} {inputs : Array Input} {split i count : Nat}
    (hCall : ValidInvocation bindings v (mode finalize finalizeMode) initial inputs split keccak fullState)
    (inv : Invariant initial v (mode finalize finalizeMode) s keccak fullState)
    (hp : s.RIP = comparePC v finalize keccak fullState finalizeMode)
    (sp : s.GPR[4] ≠ (returnBoundary initial).rsp)
    (hi : i < 2^64) (hn : count < 2^64)
    (hindex : (Operand.reg (indexReg finalize finalizeMode v fullState) : Operand 64).read s = BitVec.ofNat 64 i)
    (hcount : (Operand.reg 15 : Operand 64).read s = BitVec.ofNat 64 count)
    (hMode : finalizeMode.hasBeforeOutput = true := by decide) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧
      Invariant initial v (mode finalize finalizeMode) t keccak fullState ∧
      t.RIP = (if i < count then loopPC v finalize keccak fullState finalizeMode else finishPC v finalize keccak fullState finalizeMode) ∧
      (i < count → (Operand.reg (stateReg finalize finalizeMode v fullState) : Operand 64).read t =
        (Operand.reg 4 : Operand 64).read s +
          BitVec.ofNat 64 ((mode finalize finalizeMode).stateOffset v keccak fullState)) ∧
      (i < count → ∀ r, (selectionKind finalize finalizeMode).cursorReg v fullState = some r →
        (Operand.reg r : Operand 64).read t = (Operand.reg 4 : Operand 64).read s +
          BitVec.ofNat 64 ((mode finalize finalizeMode).stateOffset v keccak fullState + 200)) ∧
      AgreesExcept (selectionChanges finalize finalizeMode v fullState) s t := by
  let changes := selectionChanges finalize finalizeMode v fullState
  have noDf : .df ∉ changes := by
    unfold changes selectionChanges
    split <;> simp
  have noMem := selectionChanges_noMem finalize finalizeMode v fullState
  have noRsp : Component.reg 4 ∉ changes := selectionChanges_noRsp v finalize fullState finalizeMode
  obtain ⟨s1, h1, inv1, sp1, e1, a1⟩ := advanceNoMemory (changes := changes) (noDf := noDf) hCall
    (compare_step v finalize keccak fullState finalizeMode)
    (compare_image v finalize keccak fullState finalizeMode hMode)
    (by change ∀ c ∈ [.flags, .rip], c ∈ changes; simp [changes, selectionChanges])
    noMem noRsp inv sp hp
  have hcf := compare_cf finalize hi hn hindex hcount e1
  obtain ⟨s2, h2, inv2, sp2, e2, a2⟩ := advanceNoMemory (changes := changes) (noDf := noDf) hCall
    (jcc_rel8_effect_step (comparePC v finalize keccak fullState finalizeMode + (3 : BitVec 64))
      3 (selectionBranch finalize finalizeMode v fullState))
    (branch_image v finalize keccak fullState finalizeMode hMode)
    (by simp [jccEffect, branchEffect_components, changes, selectionChanges]) noMem noRsp inv1 sp1
    ⟨e1.rip, fun _ ↦ by
      clear hCall inv hp sp hi hn hindex hcount
      cases fullState <;> cases keccak <;> cases finalize <;> cases finalizeMode <;> cases v <;>
        first | contradiction | decide +kernel⟩
  have hip2 : s2.RIP = if i < count then comparePC v finalize keccak fullState finalizeMode + (5 : BitVec 64)
      else finishPC v finalize keccak fullState finalizeMode := by
    have he := e2.rip
    simp only [jccEffect, branchEffect, condHolds, BitVec.reduceToNat, hcf] at he
    by_cases hh : i < count
    · simpa [hh, BitVec.add_assoc] using he
    · simp only [hh, ite_false]
      calc
        s2.RIP = (comparePC v finalize keccak fullState finalizeMode + (3 : BitVec 64)) +
            (2 : BitVec 64) + (selectionBranch finalize finalizeMode v fullState).signExtend 64 := by
          simpa [hh, branchTarget] using he
        _ = _ := selection_branch_target v finalize keccak fullState finalizeMode hMode
  have h12 : AgreesExcept changes s s2 :=
    (a1.trans a2).mono (by intro c hc; exact (List.mem_append.mp hc).elim id id)
  by_cases hlt : ¬ i < count
  · exact ⟨2, s2, h1.trans h2, inv2, by simpa only [show ¬ i < count from hlt, ite_false] using hip2,
      fun hh ↦ (hlt hh).elim, fun hh ↦ (hlt hh).elim, h12⟩
  have hlt : i < count := by omega
  have hip2' : s2.RIP = comparePC v finalize keccak fullState finalizeMode + (5 : BitVec 64) := by
    simpa only [hlt, ite_true] using hip2
  have cursorStep : ∃ n u, Advances (returnBoundary initial) n s2 u ∧
      Invariant initial v (mode finalize finalizeMode) u keccak fullState ∧
      u.GPR[4] ≠ (returnBoundary initial).rsp ∧
      u.RIP = selectionStatePC v finalize keccak fullState finalizeMode ∧
      AgreesExcept changes s2 u ∧
      (∀ r, (selectionKind finalize finalizeMode).cursorReg v fullState = some r →
        (Operand.reg r : Operand 64).read u = (Operand.reg 4 : Operand 64).read s +
          BitVec.ofNat 64 ((mode finalize finalizeMode).stateOffset v keccak fullState + 200)) := by
    by_cases large : (selectionKind finalize finalizeMode).largeFollower v fullState = true
    · obtain ⟨u, hu, iu, su, eu, au⟩ := advanceNoMemory (changes := changes) (noDf := noDf)
        (effect := leaR64Effect (comparePC v finalize keccak fullState finalizeMode + (5 : BitVec 64)) 5
          (cursorMode v finalizeMode fullState)) hCall
        (lea_r64_effect_step _ 0x48 (by unfold RexWPrefix; decide) 5 (cursorMode v finalizeMode fullState)
          (by clear hCall inv hp sp hi hn hindex hcount; cases fullState <;> cases finalizeMode <;> cases v <;> decide +kernel) rfl rfl)
        (cursor_image v finalize keccak fullState finalizeMode hMode large)
        (by simp [changes, selectionChanges, large, leaR64Effect_components]) noMem noRsp inv2 sp2 hip2'
      refine ⟨1, u, hu, iu, su, ?_, au, ?_⟩
      · simpa [selectionStatePC, large, leaR64Effect, leaLen, cursorMode, AddrMode.tail,
          Disp.bytes, immBytes, BitVec.add_assoc] using eu.rip
      · intro r hr
        have stack := h12.read (n := 64) (r := 4) noRsp
        have hr' : r = 5 := by simpa only [selection_cursorReg, large, ite_true, Option.some.injEq] using hr.symm
        subst r
        exact eu.writes.trans ((cursorMode_addr v finalize keccak fullState finalizeMode large s2 0).trans
          (congrArg (fun x : BitVec 64 ↦ x + _) stack))
    · refine ⟨0, s2, (advances_zero _ _ _).mpr rfl, inv2, sp2, ?_, AgreesExcept.refl _ _, ?_⟩
      · simpa [selectionStatePC, large] using hip2'
      · intro r hr
        have large' : (selectionKind finalize finalizeMode).largeFollower v fullState = false := Bool.eq_false_iff.mpr large
        simp [selection_cursorReg, large'] at hr
  obtain ⟨nc, u, hc, ic, sc, pc, ac, cursor⟩ := cursorStep
  obtain ⟨w, hw, iw, sw, ew, aw⟩ := advanceNoMemory (changes := changes) (noDf := noDf)
    (effect := leaR64Effect (selectionStatePC v finalize keccak fullState finalizeMode)
      (stateReg finalize finalizeMode v fullState) (stateMode finalize finalizeMode v fullState)) hCall
    (state_step v finalize keccak fullState finalizeMode)
    (lea_image v finalize keccak fullState finalizeMode hMode)
    (by simp [changes, selectionChanges, leaR64Effect_components]) noMem noRsp ic sc pc
  have allAgrees : AgreesExcept changes s w :=
    ((h12.trans ac).trans aw).mono (by
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact (List.mem_append.mp hc).elim id id
      · exact hc)
  have state : (Operand.reg (stateReg finalize finalizeMode v fullState) : Operand 64).read w =
      (Operand.reg 4 : Operand 64).read s +
        BitVec.ofNat 64 ((mode finalize finalizeMode).stateOffset v keccak fullState) := by
    have stack := (h12.trans ac).read (n := 64) (r := 4) (by simpa using noRsp)
    exact ew.writes.trans ((stateMode_addr v finalize keccak fullState finalizeMode hMode u 0).trans
      (congrArg (fun x : BitVec 64 ↦ x + _) stack))
  have cursor' : ∀ r, (selectionKind finalize finalizeMode).cursorReg v fullState = some r →
      (Operand.reg r : Operand 64).read w = (Operand.reg 4 : Operand 64).read s +
        BitVec.ofNat 64 ((mode finalize finalizeMode).stateOffset v keccak fullState + 200) := by
    intro r hr
    rw [ew.agrees.read (n := 64) (r := r) (by
      simp [leaR64Effect_components, cursor_ne_state v finalize fullState finalizeMode r hr])]
    exact cursor r hr
  have pw := ew.rip
  by_cases done : selectionStatePC v finalize keccak fullState finalizeMode +
      BitVec.ofNat 64 (leaLen (stateMode finalize finalizeMode v fullState)) =
      loopPC v finalize keccak fullState finalizeMode
  · refine ⟨2 + nc + 1, w, (h1.trans h2).trans (hc.trans hw), iw, ?_,
      fun _ ↦ state, fun _ ↦ cursor', allAgrees⟩
    simpa only [hlt, ite_true] using pw.trans done
  · obtain ⟨t, ht, it, _, et, aTail⟩ := advanceNoMemory (changes := changes) (noDf := noDf) hCall
      (selection_nop_step v finalize keccak fullState finalizeMode)
      (selection_nop_image v finalize keccak fullState finalizeMode hMode done)
      (by simp [nopEffect_components, changes, selectionChanges]) noMem noRsp iw sw pw
    refine ⟨2 + nc + 2, t, (h1.trans h2).trans (hc.trans (hw.trans ht)), it, ?_, ?_, ?_,
      (allAgrees.trans aTail).mono (by intro c hc; exact (List.mem_append.mp hc).elim id id)⟩
    · simp only [hlt, ite_true]
      exact et.rip.trans (selection_nop_target v finalize keccak fullState finalizeMode hMode done)
    · intro _
      exact (et.agrees.read (by simp [nopEffect_components])).trans state
    · intro _ r hr
      exact (et.agrees.read (by simp [nopEffect_components])).trans (cursor' r hr)

end Sha3.Proofs.Wrapper.Reset
