import Sha3.Proofs.Wrapper.Loop.Layout
import Sha3.Proofs.Scalar.Condition.Sete
import Sha3.Proofs.Scalar.Condition.Or
import Sha3.Proofs.Scalar.Condition.Cmov
import Sha3.Proofs.Scalar.Condition.Dec
import Sha3.Proofs.X86.Instructions.Inc.Triple
import Sha3.Proofs.X86.Instructions.Cmp.Triple
import Sha3.Proofs.Wrapper.Setup.Initialize
import Sha3.Proofs.X86.Instructions.Test.Triple
import X86Proofs.Instructions.Branch.Triple
import Sha3.Proofs.X86.Instructions.Xor.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.NopMem.Triple

namespace Sha3.Proofs.Wrapper

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

namespace Setup

def firstKind : Mode → Loop.Kind
  | .plain | .digest => .plain
  | .reset => .firstReset
  | .finalizeReset => .firstFinalizeReset
  | .finalizeFixedReset => .firstFinalizeFixedReset
  | .digestFinalizeIntoReset => .firstDigestFinalizeIntoReset
  | .digestFinalizeReset => .firstDigestFinalizeReset

end Setup

namespace Selection

def plainChanges : List Component := [.reg 0, .reg 5, .reg 13, .flags, .rip]

def plainTestOffset (v : Variant) (fullState : Bool := false) : BitVec 64 := if v = .sha512 ∧ fullState = false then 0x34 else if fullState then 0x30 else 0x31

def plainStateAddr (v : Variant) (fullState : Bool := false) : AddrMode :=
  if v = .sha512 ∧ fullState = false then .sib 4 none 0 (.d32 136)
  else .sib 4 none 0 (.d8 (BitVec.ofNat 8 (Mode.plain.stateOffset v false fullState)))

def plainStateOffset (v : Variant) (fullState : Bool := false) : BitVec 64 := if v = .sha512 ∧ fullState = false then 0x43 else if fullState then 0x3f else 0x40

def plainNopOffset (v : Variant) (fullState : Bool := false) : BitVec 64 := if v = .sha512 ∧ fullState = false then 0x4b else if fullState then 0x44 else 0x45

private theorem advance [bindings : Bindings] {initial s : RamState}
    {v : Variant} {keccak fullState : Bool} {mode : Mode} {inputs : Array Input} {split : Nat}
    {boundary : ReturnBoundary} {p : BitVec 64} {bytes : List UInt8}
    {pre : RamState → Prop} {effect : RamState → Effect} {cs : List Component}
    (hCall : ValidInvocation (keccak := keccak) (fullState := fullState) bindings v mode initial inputs split)
    (step : StepEffect pre (codeRange p bytes) effect) (image : ImageAt p bytes)
    (frame : ∀ c ∈ (effect s).components, c ∈ cs)
    (writes : WritesWithin cs (writeRegions (keccak := keccak) (fullState := fullState) initial v mode))
    (nosp : Component.reg 4 ∉ cs)
    (inv : Invariant (keccak := keccak) (fullState := fullState) initial v mode s) (sp : s.GPR[4] ≠ boundary.rsp) (hp : pre s)
    (hd : Component.df ∉ cs := by exact of_decide_eq_true rfl) :
    ∃ t, Advances boundary 1 s t ∧ Invariant (keccak := keccak) (fullState := fullState) initial v mode t ∧
      t.GPR[4] ≠ boundary.rsp ∧ (effect s).Holds s t ∧ AgreesExcept cs s t := by
  obtain ⟨t, ht, hr, he⟩ := step s inv.ready (image.code inv.loaded) hp
  have ha := he.agrees.mono frame
  have hsp : t.GPR[4] = s.GPR[4] := ha.agree (.reg 4) nosp rfl
  exact ⟨t, Advances.of_step ht (.inr (hsp ▸ sp)),
    inv.of_agreesExcept hCall hr ha writes hd, hsp ▸ sp, he, ha⟩

private theorem nomem_writes {cs : List Component}
    {regions : Vector MemoryRegion n}
    (hn : ∀ c ∈ cs, ∀ a, ¬ c.Covers a) : WritesWithin cs regions := by
  intro c hc a ha
  exact (hn c hc a ha).elim

private theorem plain_nomem : ∀ c ∈ plainChanges, ∀ a, ¬ c.Covers a := by
  simp [plainChanges, Component.Covers]

private theorem same_trans {cs : List Component} {s t u : RamState}
    (ha : AgreesExcept cs s t) (hb : AgreesExcept cs t u) : AgreesExcept cs s u :=
  (ha.trans hb).mono (by intro c hc; simpa only [List.mem_append, or_self] using hc)

private theorem plainTest [bindings : Bindings] {initial s : RamState}
    {v : Variant} {keccak fullState : Bool} {inputs : Array Input} {split : Nat} (boundary : ReturnBoundary)
    (hCall : ValidInvocation (keccak := keccak) (fullState := fullState) bindings v .plain initial inputs split)
    (inv : Invariant (keccak := keccak) (fullState := fullState) initial v .plain s) (sp : s.GPR[4] ≠ boundary.rsp)
    (ip : s.RIP = (v.entry keccak fullState).entryAddress + plainTestOffset v fullState)
    (count : (Operand.reg 15 : Operand 64).read s = initial.regValue .rsi) :
    ∃ t, Advances boundary 2 s t ∧ Invariant (keccak := keccak) (fullState := fullState) initial v .plain t ∧
      t.GPR[4] ≠ boundary.rsp ∧
      t.RIP = (if initial.regValue .rsi = (0 : BitVec 64) then (v.entry keccak fullState).entryAddress + (0x6f : BitVec 64)
        else (v.entry keccak fullState).entryAddress + (plainTestOffset v fullState + (5 : BitVec 64))) ∧ AgreesExcept plainChanges s t := by
  obtain ⟨s1, a1, i1, b1, e1, f1⟩ := advance (effect := testR64R64Effect ((v.entry keccak fullState).entryAddress + plainTestOffset v fullState) 15 15) hCall
    (test_r64_r64_effect_step ((v.entry keccak fullState).entryAddress + plainTestOffset v fullState) 0x4d 0xff
      (by unfold RexWPrefix; decide) (by decide))
    (by cases fullState <;> cases keccak <;> cases v <;> unfold ImageAt <;> decide +kernel)
    (by simp [plainChanges, testR64R64Effect_components])
    (nomem_writes plain_nomem) (by decide) inv sp ip
  have hz : (StatusFlags.ofRFLAGS s1.RFLAGS).ZF = (initial.regValue .rsi == 0) := by
    have h := e1.flag .ZF
    change (StatusFlags.ofRFLAGS s1.RFLAGS).ZF =
      (((Operand.reg 15 : Operand 64).read s &&&
        (Operand.reg 15 : Operand 64).read s) == 0) at h
    simpa only [count, BitVec.and_self] using h
  obtain ⟨s2, a2, i2, b2, e2, f2⟩ := advance hCall
    (jcc_rel8_effect_step ((v.entry keccak fullState).entryAddress + (plainTestOffset v fullState + 3)) 4 (if v = .sha512 ∧ fullState = false then 0x36 else if fullState then 0x3a else 0x39))
    (by cases fullState <;> cases keccak <;> cases v <;> unfold ImageAt <;> decide +kernel)
    (by simp [plainChanges, jccEffect, branchEffect_components])
    (nomem_writes plain_nomem) (by decide) i1 b1
    ⟨by simpa [testR64R64Effect, BitVec.add_assoc] using e1.rip,
      fun _ ↦ by cases fullState <;> cases keccak <;> cases v <;> decide +kernel⟩
  refine ⟨s2, a1.trans a2, i2, b2, ?_, same_trans f1 f2⟩
  have h := e2.rip
  change s2.RIP = if (StatusFlags.ofRFLAGS s1.RFLAGS).ZF then
    (v.entry keccak fullState).entryAddress + (plainTestOffset v fullState + 3) + 2 + ((if v = .sha512 ∧ fullState = false then 0x36 else if fullState then 0x3a else 0x39) : BitVec 8).signExtend 64 else (v.entry keccak fullState).entryAddress + (plainTestOffset v fullState + 3) + 2 at h
  cases fullState <;> cases keccak <;> cases v <;> simpa [hz, beq_iff_eq, BitVec.add_assoc, plainTestOffset] using h

set_option maxHeartbeats 800000 in
theorem plain_selection [bindings : Bindings] {initial s : RamState}
    {v : Variant} {keccak fullState : Bool} {inputs : Array Input} {split : Nat} (boundary : ReturnBoundary)
    (hCall : ValidInvocation (keccak := keccak) (fullState := fullState) bindings v .plain initial inputs split)
    (inv : Invariant (keccak := keccak) (fullState := fullState) initial v .plain s) (sp : s.GPR[4] ≠ boundary.rsp)
    (ip : s.RIP = (v.entry keccak fullState).entryAddress + plainTestOffset v fullState)
    (stack : stackPtr s = frameBase (keccak := keccak) (fullState := fullState) initial v .plain)
    (count : (Operand.reg 15 : Operand 64).read s = initial.regValue .rsi) :
    ∃ n t, Advances boundary n s t ∧ Invariant (keccak := keccak) (fullState := fullState) initial v .plain t ∧
      t.RIP = (if initial.regValue .rsi = (0 : BitVec 64) then (v.entry keccak fullState).entryAddress + (0x6f : BitVec 64)
        else (v.entry keccak fullState).entryAddress + (0x50 : BitVec 64)) ∧ AgreesExcept plainChanges s t ∧
      (initial.regValue .rsi ≠ (0 : BitVec 64) →
        (Operand.reg 0 : Operand 64).read t = (0 : BitVec 64) ∧
        (Operand.reg 5 : Operand 64).read t = statePointer (keccak := keccak) (fullState := fullState) initial v .plain ∧
        (Operand.reg 13 : Operand 64).read t = statePointer (keccak := keccak) (fullState := fullState) initial v .plain + 200) := by
  obtain ⟨s2, a2, i2, b2, p2, f2⟩ := plainTest boundary hCall inv sp ip count
  by_cases hz : initial.regValue .rsi = (0 : BitVec 64)
  · exact ⟨2, s2, a2, i2, by simpa only [hz, ↓reduceIte] using p2,
      f2, fun hn ↦ (hn hz).elim⟩
  have p2' : s2.RIP = (v.entry keccak fullState).entryAddress + (plainTestOffset v fullState + (5 : BitVec 64)) := by simpa only [hz, ↓reduceIte] using p2
  obtain ⟨u, au, iu, bu, eu, fu⟩ := advance
    (effect := leaR64Effect ((v.entry keccak fullState).entryAddress + (plainTestOffset v fullState + (5 : BitVec 64))) 13
      (.sib 4 none 0 (.d32 (BitVec.ofNat 32 (Mode.plain.stateOffset v false fullState + 200))))) hCall
    (lea_r64_effect_step _ 0x4c (by unfold RexWPrefix; decide) 5
      (.sib 4 none 0 (.d32 (BitVec.ofNat 32 (Mode.plain.stateOffset v false fullState + 200))))
      (by cases fullState <;> cases keccak <;> cases v <;> decide) rfl rfl)
    (by cases fullState <;> cases keccak <;> cases v <;> unfold ImageAt <;> decide +kernel)
    (by simp [plainChanges, leaR64Effect_components])
    (nomem_writes plain_nomem) (by decide) i2 b2 p2'
  obtain ⟨s3, a3, i3, b3, e3, f3⟩ := advance (effect := xorR32R32Effect ((v.entry keccak fullState).entryAddress + (plainTestOffset v fullState + 13)) 2 0 0) hCall
    (xor_r32_r32_effect_step ((v.entry keccak fullState).entryAddress + (plainTestOffset v fullState + 13)) 0xc0 (by decide))
    (by cases fullState <;> cases keccak <;> cases v <;> unfold ImageAt <;> decide +kernel)
    (by simp [plainChanges, xorR32R32Effect_components])
    (nomem_writes plain_nomem) (by decide) iu bu (by simpa [leaR64Effect, leaLen, AddrMode.tail, Disp.bytes, immBytes, BitVec.add_assoc] using eu.rip)
  obtain ⟨s4, a4, i4, b4, e4, f4⟩ := advance (effect := leaR64Effect ((v.entry keccak fullState).entryAddress + plainStateOffset v fullState) 5
      (plainStateAddr v fullState)) hCall
    (lea_r64_effect_step ((v.entry keccak fullState).entryAddress + (plainStateOffset v fullState : BitVec 64)) 0x48 (by unfold RexWPrefix; decide) 5
      (plainStateAddr v fullState) (by cases fullState <;> cases keccak <;> cases v <;> decide) (by cases fullState <;> cases keccak <;> cases v <;> rfl) (by cases fullState <;> cases keccak <;> cases v <;> rfl))
    (by cases fullState <;> cases keccak <;> cases v <;> unfold ImageAt <;> decide +kernel)
    (by simp [plainChanges, leaR64Effect_components])
    (nomem_writes plain_nomem) (by decide) i3 b3
    (by cases fullState <;> cases keccak <;> cases v <;> simpa [xorR32R32Effect, BitVec.add_assoc, plainTestOffset, plainStateOffset] using e3.rip)
  have nopStep : StepEffect (fun t ↦ t.RIP = (v.entry keccak fullState).entryAddress + plainNopOffset v fullState)
      (codeRange ((v.entry keccak fullState).entryAddress + plainNopOffset v fullState)
        (encodeNopM (if v = .sha512 ∧ fullState = false then [] else if fullState then [0x66, 0x66, 0x66, 0x2e] else [0x66, 0x66, 0x2e])
          (if v = .sha512 ∧ fullState = false then .sib 0 (some 0) 0 (.d8 0)
            else .sib 0 (some 0) 0 (.d32 0))))
      (fun _ ↦ nopEffect ((v.entry keccak fullState).entryAddress + plainNopOffset v fullState)
        (if v = .sha512 ∧ fullState = false then 5 else if fullState then 12 else 11)) := by
    cases fullState <;> cases keccak <;> cases v <;> exact nop_m_effect_step _ _ (by decide) (by decide) _ (by decide) rfl rfl
  obtain ⟨s5, a5, i5, _, e5, f5⟩ := advance hCall nopStep
    (by cases fullState <;> cases keccak <;> cases v <;> unfold ImageAt <;> decide +kernel)
    (by simp [plainChanges, nopEffect_components])
    (nomem_writes plain_nomem) (by decide) i4 b4
    (by cases fullState <;> cases keccak <;> cases v <;> simpa [plainStateOffset, plainNopOffset, plainStateAddr, leaR64Effect, leaLen, AddrMode.tail, Disp.bytes, BitVec.add_assoc, immBytes]
      using e4.rip)
  refine ⟨6, s5, a2.trans (au.trans (a3.trans (a4.trans a5))), i5, ?_,
    same_trans f2 (same_trans fu (same_trans f3 (same_trans f4 f5))), fun _ ↦ ⟨?_, ?_, ?_⟩⟩
  · simp only [hz, ↓reduceIte]
    cases fullState <;> cases keccak <;> cases v <;> simpa [plainNopOffset, nopEffect, BitVec.add_assoc] using e5.rip
  · rw [e5.agrees.read (by simp [nopEffect_components]),
      e4.agrees.read (by simp [leaR64Effect_components])]
    have h := e3.writes
    change (Operand.reg 0 : Operand 64).read s3 =
      (((Operand.reg 0 : Operand 32).read u ^^^
        (Operand.reg 0 : Operand 32).read u).setWidth 64) at h
    rw [BitVec.xor_self, BitVec.setWidth_zero] at h
    exact h
  · rw [e5.agrees.read (by simp [nopEffect_components])]
    have h := e4.writes
    have hsp : (Operand.reg 4 : Operand 64).read s3 = frameBase (keccak := keccak) (fullState := fullState) initial v .plain :=
      ((same_trans f2 (same_trans fu f3)).read (by decide)).trans stack
    have he : (Operand.reg 5 : Operand 64).read s4 =
        (Operand.reg 4 : Operand 64).read s3 + BitVec.ofNat 64 (Mode.plain.stateOffset v false fullState) := by
      cases fullState <;> cases keccak <;> cases v <;> exact h
    exact he.trans (congrArg (· + BitVec.ofNat 64 (Mode.plain.stateOffset v false fullState)) hsp)
  · rw [e5.agrees.read (by simp [nopEffect_components]),
      e4.agrees.read (by simp [leaR64Effect_components]),
      e3.agrees.read (by simp [xorR32R32Effect_components])]
    have h := eu.writes
    have hsp : (Operand.reg 4 : Operand 64).read s2 = frameBase (keccak := keccak) (fullState := fullState) initial v .plain :=
      (f2.read (by decide)).trans stack
    have he : (Operand.reg 13 : Operand 64).read u =
        (Operand.reg 4 : Operand 64).read s2 + BitVec.ofNat 64 (Mode.plain.stateOffset v false fullState) + 200 := by
      cases fullState <;> cases keccak <;> cases v <;> rw [BitVec.add_assoc] <;> exact h
    rw [hsp] at he
    exact he

def digestArgumentsOffset (v : Variant) (fullState : Bool := false) : BitVec 64 :=
  if fullState then 0x30 else if v = .sha512 then 0x2f else 0x2c

def digestArgumentChanges : List Component := [.reg 7, .reg 6, .reg 2, .reg 1, .rip]

set_option maxHeartbeats 800000 in
theorem digest_arguments [bindings : Bindings] {initial s : RamState}
    {v : Variant} {keccak fullState : Bool} {inputs : Array Input} {split : Nat}
    (boundary : ReturnBoundary)
    (hCall : ValidInvocation bindings v .digest initial inputs split keccak fullState)
    (inv : Invariant initial v .digest s keccak fullState)
    (sp : s.GPR[4] ≠ boundary.rsp)
    (ip : s.RIP = (Mode.digest.entry v keccak fullState).entryAddress +
      digestArgumentsOffset v fullState)
    (stack : stackPtr s = frameBase initial v .digest keccak fullState)
    (pointer : s.regValue .r12 = statePointer initial v .digest keccak fullState)
    (input : s.regValue .r15 = initial.regValue .rdi)
    (length : s.regValue .r14 = initial.regValue .rsi) :
    ∃ t, Advances boundary 4 s t ∧ Invariant initial v .digest t keccak fullState ∧
      t.GPR[4] ≠ boundary.rsp ∧
      t.RIP = (Mode.digest.entry v keccak fullState).entryAddress +
        digestArgumentsOffset v fullState + (17 : BitVec 64) ∧
      t.regValue .rdi = statePointer initial v .digest keccak fullState + 200 ∧
      t.regValue .rsi = statePointer initial v .digest keccak fullState ∧
      t.regValue .rdx = initial.regValue .rdi ∧
      t.regValue .rcx = initial.regValue .rsi ∧
      AgreesExcept digestArgumentChanges s t := by
  let p := (Mode.digest.entry v keccak fullState).entryAddress +
    digestArgumentsOffset v fullState
  let am : AddrMode := .sib 4 none 0
    (.d32 (BitVec.ofNat 32 (Mode.digest.stateOffset v keccak fullState + 200)))
  have nomem : ∀ c ∈ digestArgumentChanges, ∀ a, ¬ c.Covers a := by
    simp [digestArgumentChanges, Component.Covers]
  obtain ⟨s1, a1, i1, b1, e1, f1⟩ := advance (cs := digestArgumentChanges)
    (effect := leaR64Effect p 7 am) hCall
    (lea_r64_effect_step p 0x48 (by unfold RexWPrefix; decide) 7 am
      (by cases fullState <;> cases keccak <;> cases v <;> decide) rfl rfl)
    (by cases fullState <;> cases keccak <;> cases v <;> unfold ImageAt <;> decide +kernel)
    (by simp [leaR64Effect_components, digestArgumentChanges])
    (nomem_writes nomem) (by decide) inv sp ip
  obtain ⟨s2, a2, i2, b2, e2, f2⟩ := advance (cs := digestArgumentChanges)
    (effect := movR64R64Effect (p + 8) 6 12) hCall
    (mov_r64_r64_effect_step (p + 8) 0x4c 0xe6
      (by unfold RexWPrefix; decide) (by decide))
    (by cases fullState <;> cases keccak <;> cases v <;> unfold ImageAt <;> decide +kernel)
    (by simp [movR64R64Effect_components, digestArgumentChanges])
    (nomem_writes nomem) (by decide) i1 b1
    (by simpa [leaR64Effect, leaLen, am, AddrMode.tail, Disp.bytes, immBytes,
      movR64R64Effect, BitVec.add_assoc] using e1.rip)
  obtain ⟨s3, a3, i3, b3, e3, f3⟩ := advance (cs := digestArgumentChanges)
    (effect := movR64R64Effect (p + 11) 2 15) hCall
    (mov_r64_r64_effect_step (p + 11) 0x4c 0xfa
      (by unfold RexWPrefix; decide) (by decide))
    (by cases fullState <;> cases keccak <;> cases v <;> unfold ImageAt <;> decide +kernel)
    (by simp [movR64R64Effect_components, digestArgumentChanges])
    (nomem_writes nomem) (by decide) i2 b2
    (by simpa [leaR64Effect, leaLen, am, AddrMode.tail, Disp.bytes, immBytes,
      movR64R64Effect, BitVec.add_assoc] using e2.rip)
  obtain ⟨s4, a4, i4, b4, e4, f4⟩ := advance (cs := digestArgumentChanges)
    (effect := movR64R64Effect (p + 14) 1 14) hCall
    (mov_r64_r64_effect_step (p + 14) 0x4c 0xf1
      (by unfold RexWPrefix; decide) (by decide))
    (by cases fullState <;> cases keccak <;> cases v <;> unfold ImageAt <;> decide +kernel)
    (by simp [movR64R64Effect_components, digestArgumentChanges])
    (nomem_writes nomem) (by decide) i3 b3
    (by simpa [leaR64Effect, leaLen, am, AddrMode.tail, Disp.bytes, immBytes,
      movR64R64Effect, BitVec.add_assoc] using e3.rip)
  refine ⟨s4, a1.trans (a2.trans (a3.trans a4)), i4, b4, ?_, ?_, ?_, ?_, ?_,
    same_trans f1 (same_trans f2 (same_trans f3 f4))⟩
  · simpa [movR64R64Effect, p, BitVec.add_assoc] using e4.rip
  · change (Operand.reg 7 : Operand 64).read s4 = _
    rw [e4.agrees.read (by simp [movR64R64Effect_components]),
      e3.agrees.read (by simp [movR64R64Effect_components]),
      e2.agrees.read (by simp [movR64R64Effect_components])]
    have h := e1.writes
    have he : s1.regValue .rdi = stackPtr s +
        BitVec.ofNat 64 (Mode.digest.stateOffset v keccak fullState) + 200 := by
      cases fullState <;> cases keccak <;> cases v <;> rw [BitVec.add_assoc] <;> exact h
    exact he.trans (by rw [stack]; rfl)
  · change (Operand.reg 6 : Operand 64).read s4 = _
    rw [e4.agrees.read (by simp [movR64R64Effect_components]),
      e3.agrees.read (by simp [movR64R64Effect_components])]
    exact e2.writes.trans ((f1.read (by decide)).trans pointer)
  · change (Operand.reg 2 : Operand 64).read s4 = _
    rw [e4.agrees.read (by simp [movR64R64Effect_components])]
    exact e3.writes.trans (((same_trans f1 f2).read (by decide)).trans input)
  · exact e4.writes.trans (((same_trans f1 (same_trans f2 f3)).read (by decide)).trans length)

theorem min_bound (x y : BitVec 64) (hx : x ≠ 0#64) (hy : y ≠ 0#64) :
    (if (x - 1).ult (y - 1) then x - 1 else y - 1) + 1 =
      BitVec.ofNat 64 (min x.toNat y.toNat) := by
  have hxpos : 0 < x.toNat := by
    have hn := BitVec.toNat_ne_iff_ne.mpr hx
    change x.toNat ≠ 0 at hn
    omega
  have hypos : 0 < y.toNat := by
    have hn := BitVec.toNat_ne_iff_ne.mpr hy
    change y.toNat ≠ 0 at hn
    omega
  have hxs : (x - 1).toNat = x.toNat - 1 :=
    BitVec.toNat_sub_of_le (by change (1 : Nat) ≤ x.toNat; omega)
  have hys : (y - 1).toNat = y.toNat - 1 :=
    BitVec.toNat_sub_of_le (by change (1 : Nat) ≤ y.toNat; omega)
  by_cases h : x.toNat < y.toNat
  · have hlt : (x - 1).ult (y - 1) = true := by
      rw [BitVec.ult_iff_toNat_lt, hxs, hys]
      omega
    simp only [hlt, ↓reduceIte, BitVec.sub_add_cancel, Nat.min_eq_left (Nat.le_of_lt h)]
    simp
  · have hlt : (x - 1).ult (y - 1) = false := by
      simp only [BitVec.ult_eq_decide, decide_eq_false_iff_not, hxs, hys]
      omega
    simp only [hlt, Bool.false_eq_true, ↓reduceIte, BitVec.sub_add_cancel,
      Nat.min_eq_right (by omega : y.toNat ≤ x.toNat)]
    simp


def resetMode (finalizing : Bool) (forward : Bool := false) (copied : Bool := false) : Mode := if finalizing then (if copied then (if forward then .digestFinalizeReset else .finalizeFixedReset) else if forward then .digestFinalizeIntoReset else .finalizeReset) else .reset

def splitLayout (v : Variant) (finalizing forward copied fullState : Bool) : Bool :=
  (Setup.firstKind (resetMode finalizing forward copied)).boundReg v fullState == 13

def countSaved (v : Variant) (finalizing forward copied fullState : Bool) : Bool :=
  (Setup.firstKind (resetMode finalizing forward copied)).largeFollower v fullState

def splitRegister (finalizing : Bool) : BitVec 5 := if finalizing then 3 else 13

def boundRegister (finalizing : Bool) : BitVec 5 := if finalizing then 13 else 3

def stateRegister (finalizing : Bool) : BitVec 5 := if finalizing then 3 else 5

def boundAddress (v : Variant) (finalizing : Bool) (keccak : Bool := false) (fullState : Bool := false) (forward : Bool := false) (copied : Bool := false) : BitVec 64 :=
  ((resetMode (copied := copied) (forward := forward) finalizing).entry v keccak fullState).entryAddress + (if finalizing then (if copied then (if fullState then 0x58 else if countSaved v finalizing forward copied fullState then 0x5d else 0x52) else 0x4f) else 0x45)

def boundChanges (finalizing : Bool) : List Component :=
  [.reg 0, .reg (boundRegister finalizing), .reg (splitRegister finalizing), .reg (stateRegister finalizing), .flags, .rip]

private theorem bound_nomem (finalizing : Bool) :
    ∀ c ∈ boundChanges finalizing, ∀ a, ¬ c.Covers a := by
  simp [boundChanges, Component.Covers]

set_option maxHeartbeats 800000 in
theorem bound_steps [bindings : Bindings] {initial s : RamState}
    {mode : Mode} {p : BitVec 64}
    {v : Variant} {keccak fullState : Bool} {inputs : Array Input} {split : Nat} (boundary : ReturnBoundary)
    (finalizing : Bool)
    (hCall : ValidInvocation (keccak := keccak) (fullState := fullState) bindings v mode initial inputs split)
    (inv : Invariant (keccak := keccak) (fullState := fullState) initial v mode s)
    (sp : s.GPR[4] ≠ boundary.rsp)
    (ip : s.RIP = p)
    (x y : BitVec 64) (hx : x ≠ 0#64) (hy : y ≠ 0#64)
    (xval : (Operand.reg (splitRegister finalizing) : Operand 64).read s = x)
    (yval : (Operand.reg 15 : Operand 64).read s = y)
    (images :
      ImageAt p (if finalizing then [0x48, 0xff, 0xcb] else [0x49, 0xff, 0xcd]) ∧
      ImageAt (p + 3) [0x49, 0x8d, 0x47, 0xff] ∧
      ImageAt (p + 7) (if finalizing then [0x48, 0x39, 0xc3] else [0x49, 0x39, 0xc5]) ∧
      ImageAt (p + 10) (if finalizing then [0x48, 0x0f, 0x43, 0xd8] else [0x4c, 0x0f, 0x43, 0xe8]) ∧
      ImageAt (p + 14) (if finalizing then [0x49, 0x89, 0xdd] else [0x4c, 0x89, 0xeb]) ∧
      ImageAt (p + 17) (if finalizing then [0x49, 0xff, 0xc5] else [0x48, 0xff, 0xc3]) := by
        cases finalizing <;> cases fullState <;> cases keccak <;> cases v <;>
          unfold ImageAt <;> decide +kernel) :
    ∃ t, Advances boundary 6 s t ∧ Invariant (keccak := keccak) (fullState := fullState) initial v mode t ∧
      t.GPR[4] ≠ boundary.rsp ∧ t.RIP = p + (20 : BitVec 64) ∧
      (Operand.reg (boundRegister finalizing) : Operand 64).read t = BitVec.ofNat 64 (min x.toNat y.toNat) ∧
      AgreesExcept (boundChanges finalizing) s t ∧
      (Operand.reg 5 : Operand 64).read t = (Operand.reg 5 : Operand 64).read s := by
  let r := splitRegister finalizing
  have decStep : StepEffect (fun t ↦ t.RIP = p)
      (codeRange p (if finalizing then [0x48, 0xff, 0xcb] else [0x49, 0xff, 0xcd]))
      (decR64Effect p r) := by
    cases finalizing with
    | false => exact dec_r13_effect_step p
    | true => exact dec_rbx_effect_step p
  obtain ⟨s1, a1, i1, b1, e1, f1⟩ := advance (cs := boundChanges finalizing) hCall decStep
    images.1
    (by simp [decR64Effect_components, boundChanges, r, boundRegister, stateRegister])
    (nomem_writes (bound_nomem finalizing)) (by cases finalizing <;> decide) inv sp ip
  have rx1 : (Operand.reg r : Operand 64).read s1 = x - 1 := by
    exact e1.writes.trans (congrArg (· - (1 : BitVec 64)) xval)
  obtain ⟨s2, a2, i2, b2, e2, f2⟩ := advance (cs := boundChanges finalizing)
    (effect := leaR64Effect (p + 3) 0 (.base 15 (.d8 0xff))) hCall
    (lea_r64_effect_step (p + 3) 0x49 (by unfold RexWPrefix; decide) 0
      (.base 15 (.d8 0xff)) (by decide) rfl rfl)
    images.2.1
    (by simp [leaR64Effect_components, boundChanges])
    (nomem_writes (bound_nomem finalizing)) (by cases finalizing <;> decide) i1 b1 e1.rip
  have ry2 : (Operand.reg 0 : Operand 64).read s2 = y - 1 := by
    have h := e2.writes
    change (Operand.reg 0 : Operand 64).read s2 =
      (Operand.reg 15 : Operand 64).read s1 + (0xffffffffffffffff : BitVec 64) at h
    rw [e1.agrees.read (by cases finalizing <;> simp [decR64Effect_components, r, splitRegister]),
      yval] at h
    simpa [BitVec.sub_eq_add_neg] using h
  have rx2 : (Operand.reg r : Operand 64).read s2 = x - 1 :=
    (e2.agrees.read (by cases finalizing <;> simp [leaR64Effect_components, r, splitRegister])).trans rx1
  have cmpStep : StepEffect (fun t ↦ t.RIP = p + (7 : BitVec 64))
      (codeRange (p + 7) (if finalizing then [0x48, 0x39, 0xc3] else [0x49, 0x39, 0xc5]))
      (cmpR64R64Effect (p + 7) r 0) := by
    cases finalizing with
    | false => exact cmp_r64_r64_effect_step _ 0x49 0xc5 (by unfold RexWPrefix; decide) (by decide)
    | true => exact cmp_r64_r64_effect_step _ 0x48 0xc3 (by unfold RexWPrefix; decide) (by decide)
  obtain ⟨s3, a3, i3, b3, e3, f3⟩ := advance (cs := boundChanges finalizing) hCall cmpStep
    images.2.2.1
    (by simp [cmpR64R64Effect_components, boundChanges])
    (nomem_writes (bound_nomem finalizing)) (by cases finalizing <;> decide) i2 b2
    (by simpa [leaR64Effect, BitVec.add_assoc, leaLen, AddrMode.tail, Disp.bytes, immBytes] using e2.rip)
  have cf : (StatusFlags.ofRFLAGS s3.RFLAGS).CF = (x - 1).ult (y - 1) := by
    have h := e3.flag .CF
    change (StatusFlags.ofRFLAGS s3.RFLAGS).CF =
      (cmpSpec ((Operand.reg r : Operand 64).read s2) ((Operand.reg 0 : Operand 64).read s2)).CF at h
    simpa only [rx2, ry2, cmpSpec, subSpec, BitVec.ult_eq_decide] using h
  have cmovStep : StepEffect (fun t ↦ t.RIP = p + (10 : BitVec 64))
      (codeRange (p + 10)
        (if finalizing then [0x48, 0x0f, 0x43, 0xd8] else [0x4c, 0x0f, 0x43, 0xe8]))
      (cmovaeR64R64Effect (p + 10) r 0) := by
    cases finalizing with
    | false => exact cmovae_r13_rax_effect_step _
    | true => exact cmovae_rbx_rax_effect_step _
  obtain ⟨s4, a4, i4, b4, e4, f4⟩ := advance (cs := boundChanges finalizing) hCall cmovStep
    images.2.2.2.1
    (by simp [cmovaeR64R64Effect_components, boundChanges, r, boundRegister, stateRegister])
    (nomem_writes (bound_nomem finalizing)) (by cases finalizing <;> decide) i3 b3
    (by simpa [cmpR64R64Effect, BitVec.add_assoc] using e3.rip)
  have rx4 : (Operand.reg r : Operand 64).read s4 =
      if (x - 1).ult (y - 1) then x - 1 else y - 1 := by
    have h := e4.writes
    change (Operand.reg r : Operand 64).read s4 =
      if (StatusFlags.ofRFLAGS s3.RFLAGS).CF then
        (Operand.reg r : Operand 64).read s3 else (Operand.reg 0 : Operand 64).read s3 at h
    rw [cf, e3.agrees.read (by simp [cmpR64R64Effect_components]),
      e3.agrees.read (by simp [cmpR64R64Effect_components]), rx2, ry2] at h
    exact h
  have movStep : StepEffect (fun t ↦ t.RIP = p + (14 : BitVec 64))
      (codeRange (p + 14) (if finalizing then [0x49, 0x89, 0xdd] else [0x4c, 0x89, 0xeb]))
      (movR64R64Effect (p + 14) (boundRegister finalizing) r) := by
    cases finalizing with
    | false => exact mov_r64_r64_effect_step _ 0x4c 0xeb (by unfold RexWPrefix; decide) (by decide)
    | true => exact mov_r64_r64_effect_step _ 0x49 0xdd (by unfold RexWPrefix; decide) (by decide)
  obtain ⟨s5, a5, i5, b5, e5, f5⟩ := advance (cs := boundChanges finalizing) hCall movStep
    images.2.2.2.2.1
    (by simp [movR64R64Effect_components, boundChanges])
    (nomem_writes (bound_nomem finalizing)) (by cases finalizing <;> decide) i4 b4
    (by simpa [cmovaeR64R64Effect, BitVec.add_assoc] using e4.rip)
  have incStep : StepEffect (fun t ↦ t.RIP = p + (17 : BitVec 64))
      (codeRange (p + 17) (if finalizing then [0x49, 0xff, 0xc5] else [0x48, 0xff, 0xc3]))
      (incR64Effect (p + 17) (boundRegister finalizing)) := by
    cases finalizing with
    | false => exact inc_r64_effect_step (p + 17) 0x48 0xc3 (by unfold RexWPrefix; decide) (by decide) (by decide)
    | true => exact inc_r64_effect_step (p + 17) 0x49 0xc5 (by unfold RexWPrefix; decide) (by decide) (by decide)
  obtain ⟨s6, a6, i6, b6, e6, f6⟩ := advance (cs := boundChanges finalizing) hCall incStep
    images.2.2.2.2.2
    (by simp [incR64Effect_components, boundChanges])
    (nomem_writes (bound_nomem finalizing)) (by cases finalizing <;> decide) i5 b5
    (by simpa [movR64R64Effect, BitVec.add_assoc] using e5.rip)
  refine ⟨s6, a1.trans (a2.trans (a3.trans (a4.trans (a5.trans a6)))), i6, b6, ?_, ?_,
    same_trans f1 (same_trans f2 (same_trans f3 (same_trans f4 (same_trans f5 f6)))), ?_⟩
  · simpa [incR64Effect, BitVec.add_assoc] using e6.rip
  · exact e6.writes.trans ((congrArg (· + (1 : BitVec 64)) (e5.writes.trans rx4)).trans
      (min_bound x y hx hy))
  · rw [e6.agrees.read (by cases finalizing <;> simp [incR64Effect_components, boundRegister]),
      e5.agrees.read (by cases finalizing <;> simp [movR64R64Effect_components, boundRegister]),
      e4.agrees.read (by cases finalizing <;> simp [cmovaeR64R64Effect_components, r, splitRegister]),
      e3.agrees.read (by simp [cmpR64R64Effect_components]),
      e2.agrees.read (by simp [leaR64Effect_components]),
      e1.agrees.read (by cases finalizing <;> simp [decR64Effect_components, r, splitRegister])]

def loopStateAddr (v : Variant) (mode : Mode) (keccak fullState : Bool) : AddrMode :=
  .sib 4 none 0 (if mode.stateOffset v keccak fullState < 128 then
    .d8 (BitVec.ofNat 8 (mode.stateOffset v keccak fullState)) else
    .d32 (BitVec.ofNat 32 (mode.stateOffset v keccak fullState)))

theorem enter_loop_state [bindings : Bindings] {initial s : RamState}
    {mode : Mode} {p : BitVec 64} {v : Variant} {keccak fullState : Bool}
    {inputs : Array Input} {split : Nat} (boundary : ReturnBoundary)
    (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState)
    (inv : Invariant initial v mode s keccak fullState) (sp : s.GPR[4] ≠ boundary.rsp)
    (ip : s.RIP = p) (stack : stackPtr s = frameBase initial v mode keccak fullState)
    (dst : BitVec 4) (nonzero : dst.setWidth 5 ≠ 0#5) (nonsp : dst.setWidth 5 ≠ 4#5)
    (images : ImageAt p [0x31, 0xc0] ∧
      ImageAt (p + 2) (encodeLeaR64M dst (loopStateAddr v mode keccak fullState))) :
    ∃ t, Advances boundary 2 s t ∧ Invariant initial v mode t keccak fullState ∧
      t.GPR[4] ≠ boundary.rsp ∧
      t.RIP = p + (2 : BitVec 64) + BitVec.ofNat 64 (leaLen (loopStateAddr v mode keccak fullState)) ∧
      (Operand.reg 0 : Operand 64).read t = 0#64 ∧
      (Operand.reg (dst.setWidth 5) : Operand 64).read t =
        statePointer initial v mode keccak fullState ∧
      AgreesExcept [.reg 0, .reg (dst.setWidth 5), .flags, .rip] s t := by
  let am := loopStateAddr v mode keccak fullState
  let cs : List Component := [.reg 0, .reg (dst.setWidth 5), .flags, .rip]
  have nomem : ∀ c ∈ cs, ∀ a, ¬ c.Covers a := by simp [cs, Component.Covers]
  have nosp : Component.reg 4 ∉ cs := by
    simp only [cs, List.mem_cons, List.not_mem_nil, or_false, Component.reg.injEq]
    intro h
    rcases h with h | h | h | h
    · contradiction
    · exact nonsp h.symm
    · contradiction
    · contradiction
  obtain ⟨s1, a1, i1, b1, e1, f1⟩ := advance (cs := cs)
    (effect := xorR32R32Effect p 2 0 0) hCall
    (xor_r32_r32_effect_step p 0xc0 (by decide)) images.1
    (by simp [xorR32R32Effect_components, cs]) (nomem_writes nomem) nosp inv sp ip
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec dst
  have valid : am.Valid := by
    cases mode <;> cases fullState <;> cases keccak <;> cases v <;> decide
  have step := lea_r64_effect_step (p + 2) _ hrex (regLow dst) am valid hx hb
  rw [hr, gprNumber_reg] at step
  obtain ⟨s2, a2, i2, b2, e2, f2⟩ := advance (cs := cs)
    (effect := leaR64Effect (p + 2) (dst.setWidth 5) am) hCall step images.2
    (by simp [leaR64Effect_components, cs]) (nomem_writes nomem) nosp i1 b1 e1.rip
  refine ⟨s2, a1.trans a2, i2, b2, e2.rip, ?_, ?_, same_trans f1 f2⟩
  · rw [e2.agrees.read (by simp [leaR64Effect_components]; exact Ne.symm nonzero)]
    have h := e1.writes
    change (Operand.reg 0 : Operand 64).read s1 =
      (((Operand.reg 0 : Operand 32).read s ^^^ (Operand.reg 0 : Operand 32).read s).setWidth 64) at h
    simpa only [BitVec.xor_self, BitVec.setWidth_zero] using h
  · have hsp : (Operand.reg 4 : Operand 64).read s1 = frameBase initial v mode keccak fullState :=
      (e1.agrees.read (by simp [xorR32R32Effect_components])).trans stack
    have ha : am.addr s1 (p + 2 + BitVec.ofNat 64 (leaLen am)) =
        (Operand.reg 4 : Operand 64).read s1 + BitVec.ofNat 64 (mode.stateOffset v keccak fullState) := by
      cases mode <;> cases fullState <;> cases keccak <;> cases v <;> rfl
    exact e2.writes.trans (ha.trans (congrArg (· + BitVec.ofNat 64 (mode.stateOffset v keccak fullState)) hsp))

set_option maxHeartbeats 1600000 in
theorem enter_loop [bindings : Bindings] {initial s : RamState}
    {v : Variant} {forward copied keccak fullState : Bool} {inputs : Array Input} {split : Nat}
    (boundary : ReturnBoundary) (finalizing : Bool)
    (hCall : ValidInvocation bindings v (resetMode finalizing forward copied) initial inputs split keccak fullState)
    (inv : Invariant initial v (resetMode finalizing forward copied) s keccak fullState)
    (sp : s.GPR[4] ≠ boundary.rsp)
    (ip : s.RIP = boundAddress v finalizing keccak fullState forward copied + (20 : BitVec 64))
    (stack : stackPtr s = frameBase initial v (resetMode finalizing forward copied) keccak fullState) :
    ∃ n t, Advances boundary n s t ∧
      Invariant initial v (resetMode finalizing forward copied) t keccak fullState ∧
      t.RIP = (Setup.firstKind (resetMode finalizing forward copied)).start v keccak fullState ∧
      (Operand.reg 0 : Operand 64).read t = (0 : BitVec 64) ∧
      (Operand.reg ((Setup.firstKind (resetMode finalizing forward copied)).stateReg v fullState) : Operand 64).read t =
        statePointer initial v (resetMode finalizing forward copied) keccak fullState ∧
      AgreesExcept [.reg 0, .reg ((Setup.firstKind (resetMode finalizing forward copied)).stateReg v fullState), .flags, .rip] s t := by
  let mode := resetMode finalizing forward copied
  let kind := Setup.firstKind mode
  let p := boundAddress v finalizing keccak fullState forward copied + (20 : BitVec 64)
  let r := kind.stateReg v fullState
  let dst := r.setWidth 4
  let cs : List Component := [.reg 0, .reg r, .flags, .rip]
  have regCast : dst.setWidth 5 = r := by
    cases finalizing <;> cases forward <;> cases copied <;> cases fullState <;> cases v <;> rfl
  obtain ⟨s2, a2, i2, b2, p2, index, pointer, fs⟩ :=
    enter_loop_state boundary hCall inv sp ip stack dst
      (by rw [regCast]; cases finalizing <;> cases forward <;> cases copied <;> cases fullState <;> cases v <;> decide)
      (by rw [regCast]; cases finalizing <;> cases forward <;> cases copied <;> cases fullState <;> cases v <;> decide)
      (by cases finalizing <;> cases forward <;> cases copied <;> cases fullState <;> cases keccak <;> cases v <;>
        unfold ImageAt <;> decide +kernel)
  rw [regCast] at pointer fs
  let q := p + 2 + BitVec.ofNat 64 (leaLen (loopStateAddr v mode keccak fullState))
  by_cases hn : (finalizing && (!copied || countSaved v finalizing forward copied fullState)) = true
  · let prefixes : List UInt8 := if copied then (if fullState then [0x66, 0x66, 0x66, 0x66, 0x2e] else []) else [0x66]
    let am : AddrMode := .sib 0 (some 0) 0 (if copied && fullState then .d32 0 else .d8 0)
    let len : Nat := if copied then (if fullState then 13 else 5) else 6
    have step : StepEffect (fun t ↦ t.RIP = q) (codeRange q (encodeNopM prefixes am))
        (fun _ ↦ nopEffect q len) := by
      cases copied <;> cases fullState <;> exact nop_m_effect_step q _ (by decide) (by decide) _ (by decide) rfl rfl
    have nomem : ∀ c ∈ cs, ∀ a, ¬c.Covers a := by simp [cs, Component.Covers]
    obtain ⟨s3, a3, i3, _, e3, f3⟩ := advance (cs := cs) hCall step
      (by cases finalizing <;> cases forward <;> cases copied <;> cases fullState <;> cases keccak <;> cases v <;>
            simp [countSaved, resetMode, Setup.firstKind, Loop.Kind.largeFollower] at hn
          all_goals unfold ImageAt; decide +kernel)
      (by simp [nopEffect_components, cs]) (nomem_writes nomem)
      (by cases finalizing <;> cases forward <;> cases copied <;> cases fullState <;> cases v <;> decide)
      i2 b2 p2
    have target : q + BitVec.ofNat 64 len = kind.start v keccak fullState := by
      cases finalizing <;> cases forward <;> cases copied <;> cases fullState <;> cases keccak <;> cases v <;>
        simp [countSaved, resetMode, Setup.firstKind, Loop.Kind.largeFollower] at hn
      all_goals decide +kernel
    refine ⟨3, s3, a2.trans a3, i3, e3.rip.trans target,
      (e3.agrees.read (by simp [nopEffect_components])).trans index,
      (e3.agrees.read (by simp [nopEffect_components])).trans pointer,
      same_trans fs f3⟩
  · have target : q = kind.start v keccak fullState := by
      cases finalizing <;> cases forward <;> cases copied <;> cases fullState <;> cases keccak <;> cases v <;>
        simp [countSaved, resetMode, Setup.firstKind, Loop.Kind.largeFollower] at hn
      all_goals decide +kernel
    exact ⟨2, s2, a2, i2, p2.trans target, index, pointer, fs⟩

private theorem mergeGPR8_low (v : BitVec 8) (old : BitVec 64) : (mergeGPR 8 v old).setWidth 8 = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [mergeGPR, Nat.reduceEqDiff, ↓reduceIte, BitVec.getLsbD_setWidth, hi,
    decide_true, Bool.true_and]
  rw [getLsbD_setSlice _ _ _ _ _ (by omega)]
  simp [hi]

def testAddress (v : Variant) (finalizing : Bool) (keccak : Bool := false) (fullState : Bool := false) (forward : Bool := false) (copied : Bool := false) : BitVec 64 :=
  ((resetMode (copied := copied) (forward := forward) finalizing).entry v keccak fullState).entryAddress + (if finalizing then (if copied then (if fullState then 0x3b else if countSaved v finalizing forward copied fullState then 0x3c else 0x3d) else 0x3a) else 0x35)

def skipAddress (v : Variant) (finalizing : Bool) (keccak : Bool := false) (fullState : Bool := false) (forward : Bool := false) (copied : Bool := false) : BitVec 64 :=
  ((resetMode (copied := copied) (forward := forward) finalizing).entry v keccak fullState).entryAddress + (if finalizing then (if copied then (if fullState then 0xa4 else if countSaved v finalizing forward copied fullState then 0xa8 else 0x99) else 0x99) else 0x84)

def testChanges : List Component := [.reg 0, .reg 1, .flags, .rip]

private theorem test_nomem : ∀ c ∈ testChanges, ∀ a, ¬ c.Covers a := by
  simp [testChanges, Component.Covers]

set_option maxHeartbeats 800000 in
theorem reset_test_flags [bindings : Bindings] {initial s : RamState}
    {mode : Mode} {p : BitVec 64} {v : Variant} {keccak fullState : Bool}
    {inputs : Array Input} {split : Nat} (boundary : ReturnBoundary) (finalizing : Bool)
    (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState)
    (inv : Invariant initial v mode s keccak fullState)
    (sp : s.GPR[4] ≠ boundary.rsp) (ip : s.RIP = p)
    (x y : BitVec 64)
    (xval : (Operand.reg (splitRegister finalizing) : Operand 64).read s = x)
    (yval : (Operand.reg 15 : Operand 64).read s = y)
    (images :
      ImageAt p (if finalizing then [0x48, 0x85, 0xdb] else [0x4d, 0x85, 0xed]) ∧
      ImageAt (p + 3) [0x0f, 0x94, 0xc0] ∧
      ImageAt (p + 6) [0x4d, 0x85, 0xff] ∧
      ImageAt (p + 9) [0x0f, 0x94, 0xc1] ∧
      ImageAt (p + 12) [0x08, 0xc1] := by
        cases finalizing <;> cases fullState <;> cases keccak <;> cases v <;>
          unfold ImageAt <;> decide +kernel) :
    ∃ t, Advances boundary 5 s t ∧ Invariant initial v mode t keccak fullState ∧
      t.GPR[4] ≠ boundary.rsp ∧ t.RIP = p + (14 : BitVec 64) ∧
      condHolds 5 (StatusFlags.ofRFLAGS t.RFLAGS) = ((x == 0#64) || (y == 0#64)) ∧
      AgreesExcept testChanges s t := by
  let r := splitRegister finalizing
  have tstStep : StepEffect (fun t ↦ t.RIP = p)
      (codeRange p (if finalizing then [0x48, 0x85, 0xdb] else [0x4d, 0x85, 0xed]))
      (testR64R64Effect p r r) := by
    cases finalizing with
    | false => exact test_r64_r64_effect_step _ 0x4d 0xed (by unfold RexWPrefix; decide) (by decide)
    | true => exact test_r64_r64_effect_step _ 0x48 0xdb (by unfold RexWPrefix; decide) (by decide)
  obtain ⟨s1, a1, i1, b1, e1, f1⟩ := advance (cs := testChanges) hCall tstStep
    images.1
    (by simp [testR64R64Effect_components, testChanges])
    (nomem_writes test_nomem) (by decide) inv sp ip
  have zx : (StatusFlags.ofRFLAGS s1.RFLAGS).ZF = (x == 0#64) := by
    have h := e1.flag .ZF
    change (StatusFlags.ofRFLAGS s1.RFLAGS).ZF =
      (((Operand.reg r : Operand 64).read s &&& (Operand.reg r : Operand 64).read s) == 0#64) at h
    rw [xval, BitVec.and_self] at h
    exact h
  obtain ⟨s2, a2, i2, b2, e2, f2⟩ := advance (cs := testChanges) hCall
    (sete_al_effect_step (p + 3))
    images.2.1
    (by simp [seteR8Effect_components, testChanges])
    (nomem_writes test_nomem) (by decide) i1 b1 e1.rip
  have al2 : (Operand.reg 0 : Operand 8).read s2 = (if x == 0#64 then 1#8 else 0#8) := by
    change ((Operand.reg 0 : Operand 64).read s2).setWidth 8 = _
    have h := congrArg (BitVec.setWidth 8) e2.writes
    simpa only [zx, mergeGPR8_low, BitVec.ofNat_eq_ofNat] using h
  obtain ⟨s3, a3, i3, b3, e3, f3⟩ := advance (cs := testChanges)
    (effect := testR64R64Effect (p + 6) 15 15) hCall
    (test_r64_r64_effect_step (p + 6) 0x4d 0xff (by unfold RexWPrefix; decide) (by decide))
    images.2.2.1
    (by simp [testR64R64Effect_components, testChanges])
    (nomem_writes test_nomem) (by decide) i2 b2
    (by simpa [seteR8Effect, BitVec.add_assoc] using e2.rip)
  have zy : (StatusFlags.ofRFLAGS s3.RFLAGS).ZF = (y == 0#64) := by
    have h := e3.flag .ZF
    change (StatusFlags.ofRFLAGS s3.RFLAGS).ZF =
      (((Operand.reg 15 : Operand 64).read s2 &&& (Operand.reg 15 : Operand 64).read s2) == 0#64) at h
    rw [(same_trans f1 f2).read (by decide), yval, BitVec.and_self] at h
    exact h
  obtain ⟨s4, a4, i4, b4, e4, f4⟩ := advance (cs := testChanges) hCall
    (sete_cl_effect_step (p + 9))
    images.2.2.2.1
    (by simp [seteR8Effect_components, testChanges])
    (nomem_writes test_nomem) (by decide) i3 b3
    (by simpa [testR64R64Effect, BitVec.add_assoc] using e3.rip)
  have cl4 : (Operand.reg 1 : Operand 8).read s4 = (if y == 0#64 then 1#8 else 0#8) := by
    change ((Operand.reg 1 : Operand 64).read s4).setWidth 8 = _
    have h := congrArg (BitVec.setWidth 8) e4.writes
    simpa only [zy, mergeGPR8_low, BitVec.ofNat_eq_ofNat] using h
  have al4 : (Operand.reg 0 : Operand 8).read s4 = (if x == 0#64 then 1#8 else 0#8) := by
    rw [e4.agrees.read (by simp [seteR8Effect_components]),
      e3.agrees.read (by simp [testR64R64Effect_components])]
    exact al2
  obtain ⟨s5, a5, i5, b5, e5, f5⟩ := advance (cs := testChanges) hCall
    (or_cl_al_effect_step (p + 12))
    images.2.2.2.2
    (by simp [orR8R8Effect_components, testChanges])
    (nomem_writes test_nomem) (by decide) i4 b4
    (by simpa [seteR8Effect, BitVec.add_assoc] using e4.rip)
  have zf : condHolds 5 (StatusFlags.ofRFLAGS s5.RFLAGS) = ((x == 0#64) || (y == 0#64)) := by
    have h := e5.flag .ZF
    change (StatusFlags.ofRFLAGS s5.RFLAGS).ZF =
      (((Operand.reg 1 : Operand 8).read s4 ||| (Operand.reg 0 : Operand 8).read s4) == 0#8) at h
    rw [cl4, al4] at h
    change (!(StatusFlags.ofRFLAGS s5.RFLAGS).ZF) = _
    rw [h]
    cases (x == 0#64) <;> cases (y == 0#64) <;> decide +kernel
  refine ⟨s5, a1.trans (a2.trans (a3.trans (a4.trans a5))), i5, b5, ?_, zf,
    same_trans f1 (same_trans f2 (same_trans f3 (same_trans f4 f5)))⟩
  simpa [orR8R8Effect, BitVec.add_assoc] using e5.rip

theorem save_register [bindings : Bindings] {initial s : RamState}
    {v : Variant} {keccak fullState : Bool} {mode : Mode} {inputs : Array Input}
    {split : Nat} {p : BitVec 64} (boundary : ReturnBoundary)
    (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState)
    (inv : Invariant initial v mode s keccak fullState) (sp : s.GPR[4] ≠ boundary.rsp)
    (ip : s.RIP = p) (offset : Nat) (hmin : 8 ≤ offset)
    (hbudget : offset ≤ (mode.entry v keccak fullState).minStackBytes)
    (source : BitVec 4) (am : AddrMode) (valid : am.Valid)
    (addr : storeAddrAt p am (3 + am.tail.length) s =
      initial.regValue .rsp - BitVec.ofNat 64 offset)
    (image : ImageAt p (encodeMovM64R64 source am)) :
    ∃ t, Advances boundary 1 s t ∧ Invariant initial v mode t keccak fullState ∧
      t.GPR[4] ≠ boundary.rsp ∧
      t.RIP = p + BitVec.ofNat 64 (3 + am.tail.length) ∧
      (Operand.mem (initial.regValue .rsp - BitVec.ofNat 64 offset) : Operand 64).read t =
        (Operand.reg (source.setWidth 5) : Operand 64).read s ∧
      AgreesExcept [.mem (initial.regValue .rsp - BitVec.ofNat 64 offset) 8, .rip] s t := by
  have read : MemReadable s ((initial.regValue .rsp - BitVec.ofNat 64 offset)) 8 := by
    refine ⟨?_, ?_⟩
    · have hlow := stack_sub_low hCall.stackAvailable hbudget
      change (initial.regValue .rsp - (BitVec.ofNat 64 offset)).toNat + offset < 2 ^ 32 at hlow
      omega
    · intro i hi
      exact inv.grows _ (Option.isSome_iff_exists.mpr
        (stack_sub_allocated (offset := offset) hCall.stackAvailable hbudget (by omega)))
  have writes : WritesWithin [.mem ((initial.regValue .rsp - BitVec.ofNat 64 offset)) 8, .rip]
      (writeRegions (keccak := keccak) (fullState := fullState) initial v mode) := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · obtain ⟨i, hi, rfl⟩ := ha
      refine ⟨Stack.region initial (mode.entry v keccak fullState).minStackBytes,
        stack_mem_writeRegions (keccak := keccak) (fullState := fullState) initial v mode, ?_⟩
      exact stack_sub_contains (offset := offset) hCall.stackAvailable hbudget (by omega)
    · exact ha.elim
  have pre : StorePreReadable p (storeAddrAt p am (3 + am.tail.length)) 8 s := by
    refine ⟨⟨ip, addr ▸ read⟩, ?_⟩
    intro i hi ht
    have ⟨region, hreg, hcontains⟩ := writes (.mem ((initial.regValue .rsp - BitVec.ofNat 64 offset)) 8)
      (by simp) ((initial.regValue .rsp - BitVec.ofNat 64 offset) + BitVec.ofNat 64 i) ⟨i, hi, rfl⟩
    exact writeRegions_avoid hCall region hreg _ hcontains (.inr (addr ▸ ht))
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec source
  have step := mov_m64_r64_effect_step_of_readable p _ hrex (regLow source) am valid hx hb
  rw [hr, gprNumber_reg] at step
  obtain ⟨t, a, it, bt, e, f⟩ := advance
    (cs := [.mem ((initial.regValue .rsp - BitVec.ofNat 64 offset)) 8, .rip])
    (effect := movM64R64Effect p (source.setWidth 5) am) hCall
    step image
    (by
      simp only [movM64R64Effect_components]
      change ∀ c ∈ [Component.mem (storeAddrAt p am (3 + am.tail.length) s) 8, .rip],
        c ∈ [Component.mem ((initial.regValue .rsp - BitVec.ofNat 64 offset)) 8, .rip]
      rw [addr]
      exact fun _ h ↦ h)
    writes (by simp) inv sp pre
  refine ⟨t, a, it, bt, ?_, ?_, f⟩
  · exact e.rip
  · have h := e.writes
    change (Operand.mem (storeAddrAt p am (3 + am.tail.length) s) : Operand 64).read t =
      (Operand.reg (source.setWidth 5) : Operand 64).read s at h
    rwa [addr] at h

def countSlot (initial : RamState) (v : Variant) (finalizing forward copied keccak fullState : Bool) : BitVec 64 :=
  frameBase initial v (resetMode finalizing forward copied) keccak fullState +
    (if fullState then 8 else 0)

private theorem countSlot_sub (initial : RamState) (v : Variant)
    (finalizing forward copied keccak fullState : Bool) :
    countSlot initial v finalizing forward copied keccak fullState =
      initial.regValue .rsp - BitVec.ofNat 64
        ((resetMode finalizing forward copied).frameSize v keccak fullState -
          if fullState then 8 else 0) := by
  cases finalizing <;> cases forward <;> cases copied <;> cases fullState <;> cases v <;>
    simp [countSlot, frameBase, resetMode, Mode.frameSize, BitVec.sub_eq_add_neg, BitVec.add_assoc]

def countSaveChanges (initial : RamState) (v : Variant)
    (finalizing forward copied keccak fullState : Bool) : List Component :=
  if countSaved v finalizing forward copied fullState then
    [.mem (countSlot initial v finalizing forward copied keccak fullState) 8, .rip] else []

theorem save_count [bindings : Bindings] {initial s : RamState}
    {v : Variant} {forward copied keccak fullState : Bool} {inputs : Array Input}
    {split : Nat} (boundary : ReturnBoundary) (finalizing : Bool)
    (hCall : ValidInvocation bindings v (resetMode finalizing forward copied) initial inputs split keccak fullState)
    (inv : Invariant initial v (resetMode finalizing forward copied) s keccak fullState)
    (sp : s.GPR[4] ≠ boundary.rsp)
    (ip : s.RIP = testAddress v finalizing keccak fullState forward copied + (14 : BitVec 64))
    (stack : stackPtr s = frameBase initial v (resetMode finalizing forward copied) keccak fullState) :
    ∃ n t, Advances boundary n s t ∧
      Invariant initial v (resetMode finalizing forward copied) t keccak fullState ∧
      t.GPR[4] ≠ boundary.rsp ∧
      t.RIP = testAddress v finalizing keccak fullState forward copied + (14 : BitVec 64) +
        ((if countSaved v finalizing forward copied fullState then (if fullState then 5 else 4) else 0) : BitVec 64) ∧
      AgreesExcept (countSaveChanges initial v finalizing forward copied keccak fullState) s t ∧
      (countSaved v finalizing forward copied fullState = true →
        (Operand.mem (countSlot initial v finalizing forward copied keccak fullState) : Operand 64).read t =
          (Operand.reg 15 : Operand 64).read s) := by
  by_cases hc : countSaved v finalizing forward copied fullState = true
  · let p := testAddress v finalizing keccak fullState forward copied + (14 : BitVec 64)
    let mode := resetMode finalizing forward copied
    let offset := mode.frameSize v keccak fullState - if fullState then 8 else 0
    let am : AddrMode := .sib 4 none 0 (if fullState then .d8 8 else .none)
    have hmin : 8 ≤ offset := by
      cases finalizing <;> cases forward <;> cases copied <;> cases fullState <;> cases keccak <;> cases v <;> decide
    have hbudget : offset ≤ (mode.entry v keccak fullState).minStackBytes := by
      rw [Mode.stackBudget mode v keccak fullState]
      exact Nat.le_trans (Nat.sub_le _ _) (Nat.le_add_right _ _)
    have addr : storeAddrAt p am (3 + am.tail.length) s = initial.regValue .rsp - BitVec.ofNat 64 offset := by
      rw [← countSlot_sub initial v finalizing forward copied keccak fullState]
      cases fullState <;> exact congrArg (· + _) stack
    obtain ⟨t, a, it, bt, pt, value, ft⟩ := save_register boundary hCall inv sp ip offset hmin hbudget
      15 am (by cases fullState <;> decide) addr
      (by
        cases finalizing <;> cases forward <;> cases copied <;> cases fullState <;> cases keccak <;> cases v <;>
          simp [countSaved, resetMode, Setup.firstKind, Loop.Kind.largeFollower] at hc
        all_goals unfold ImageAt; decide +kernel)
    refine ⟨1, t, a, it, bt, ?_, ?_, fun _ ↦ ?_⟩
    · cases fullState <;> simpa [hc, p, am, AddrMode.tail, Disp.bytes, immBytes] using pt
    · simpa only [countSaveChanges, hc, ↓reduceIte, countSlot_sub] using ft
    · rw [countSlot_sub]
      exact value
  · refine ⟨0, s, (advances_zero _ _ _).mpr rfl, inv, sp, ?_, ?_, fun h ↦ (hc h).elim⟩
    · simpa [hc] using ip
    · simp only [countSaveChanges, hc]
      exact AgreesExcept.refl _ _

private theorem readMem_of_external_eq {s t : RamState} (h : t.external = s.external)
    (a : BitVec 64) : (Operand.mem a : Operand 64).read t =
      (Operand.mem a : Operand 64).read s := by
  change memLoad t.external a 64 = memLoad s.external a 64
  rw [h]

set_option maxHeartbeats 1600000 in
theorem reset_test [bindings : Bindings] {initial s : RamState}
    {v : Variant} {forward copied keccak fullState : Bool} {inputs : Array Input} {split : Nat}
    (boundary : ReturnBoundary) (finalizing : Bool)
    (hCall : ValidInvocation bindings v (resetMode finalizing forward copied) initial inputs split keccak fullState)
    (inv : Invariant initial v (resetMode finalizing forward copied) s keccak fullState)
    (sp : s.GPR[4] ≠ boundary.rsp)
    (ip : s.RIP = testAddress v finalizing keccak fullState forward copied)
    (stack : stackPtr s = frameBase initial v (resetMode finalizing forward copied) keccak fullState)
    (x y : BitVec 64)
    (xval : (Operand.reg (splitRegister (splitLayout v finalizing forward copied fullState)) : Operand 64).read s = x)
    (yval : (Operand.reg 15 : Operand 64).read s = y) :
    ∃ n t, Advances boundary n s t ∧
      Invariant initial v (resetMode finalizing forward copied) t keccak fullState ∧
      t.GPR[4] ≠ boundary.rsp ∧
      t.RIP = (if x = 0#64 ∨ y = 0#64 then skipAddress v finalizing keccak fullState forward copied
        else testAddress v finalizing keccak fullState forward copied + (16 : BitVec 64) +
          ((if countSaved v finalizing forward copied fullState then (if fullState then 5 else 4) else 0) : BitVec 64)) ∧
      AgreesExcept (testChanges ++ countSaveChanges initial v finalizing forward copied keccak fullState) s t ∧
      (countSaved v finalizing forward copied fullState = true →
        (Operand.mem (countSlot initial v finalizing forward copied keccak fullState) : Operand 64).read t =
          (Operand.reg 15 : Operand 64).read s) := by
  let p := testAddress v finalizing keccak fullState forward copied
  let q := p + 14 + (if countSaved v finalizing forward copied fullState then
    (if fullState then 5 else 4) else 0)
  let d := (skipAddress v finalizing keccak fullState forward copied - (q + 2)).setWidth 8
  obtain ⟨s5, a5, i5, b5, p5, zf, f5⟩ :=
    reset_test_flags boundary (splitLayout v finalizing forward copied fullState) hCall inv sp ip x y xval yval
      (by cases finalizing <;> cases forward <;> cases copied <;> cases fullState <;> cases keccak <;> cases v <;>
        unfold ImageAt <;> decide +kernel)
  have sp5 : stackPtr s5 = frameBase initial v (resetMode finalizing forward copied) keccak fullState :=
    (f5.read (r := 4) (n := 64) (by decide)).trans stack
  obtain ⟨nc, sc, ac, ic, bc, pc, fc, saved⟩ := save_count boundary finalizing hCall i5 b5 p5 sp5
  have hflags : StatusFlags.ofRFLAGS sc.RFLAGS = StatusFlags.ofRFLAGS s5.RFLAGS := fc.agree .flags
    (by unfold countSaveChanges; split <;> simp) rfl
  obtain ⟨s6, a6, i6, b6, e6, f6⟩ := advance (cs := testChanges) hCall
    (jcc_rel8_effect_step q 5 d)
    (by cases finalizing <;> cases forward <;> cases copied <;> cases fullState <;> cases keccak <;> cases v <;>
      unfold ImageAt <;> decide +kernel)
    (by simp [jccEffect, branchEffect_components, testChanges])
    (nomem_writes test_nomem) (by decide) ic bc
    ⟨pc, fun _ ↦ by cases finalizing <;> cases forward <;> cases copied <;> cases fullState <;> cases keccak <;> cases v <;> decide +kernel⟩
  refine ⟨5 + (nc + 1), s6, a5.trans (ac.trans a6), i6, b6, ?_, ?_, ?_⟩
  · have h := e6.rip
    change s6.RIP = if condHolds 5 (StatusFlags.ofRFLAGS sc.RFLAGS) then
      q + 2 + d.signExtend 64 else q + 2 at h
    rw [hflags, zf] at h
    have target : q + 2 + d.signExtend 64 = skipAddress v finalizing keccak fullState forward copied := by
      cases finalizing <;> cases forward <;> cases copied <;> cases fullState <;> cases keccak <;> cases v <;> decide +kernel
    rw [target] at h
    cases hc : countSaved v finalizing forward copied fullState <;> cases fullState <;>
      simpa [q, p, hc, Bool.or_eq_true, beq_iff_eq, BitVec.add_assoc] using h

  · apply (f5.trans (fc.trans f6)).mono
    intro c hc
    simp only [List.mem_append] at hc ⊢
    rcases hc with h | h | h
    · exact .inl h
    · exact .inr h
    · exact .inl h
  · intro hc
    rw [readMem_of_external_eq (f6.external test_nomem), saved hc, f5.read (by decide)]


def storeBeforeOutput (finalizing copied fullState : Bool) : Bool :=
  finalizing && !(copied && fullState)

def beforeOutputOperand (initial : RamState) (v : Variant) (forward copied keccak fullState : Bool) : Operand 64 :=
  if copied && fullState then .mem (frameBase initial v (resetMode true forward copied) keccak fullState + 16)
  else .reg 5

def beforeStoreChanges (initial : RamState) (v : Variant)
    (finalizing forward copied keccak fullState : Bool) : List Component :=
  if storeBeforeOutput finalizing copied fullState then
    [.mem (frameBase initial v (resetMode finalizing forward copied) keccak fullState + 8) 8, .rip] else []

def cursorAddress (v : Variant) (finalizing forward copied keccak fullState : Bool) : BitVec 64 :=
  boundAddress v finalizing keccak fullState forward copied -
    (if countSaved v finalizing forward copied fullState then 8 else 0)

private theorem cursorAddress_eq (v : Variant) (finalizing forward copied keccak fullState : Bool) :
    testAddress v finalizing keccak fullState forward copied + 16 +
      (if countSaved v finalizing forward copied fullState then (if fullState then 5 else 4) else 0) +
      (if storeBeforeOutput finalizing copied fullState then 5 else 0) =
      cursorAddress v finalizing forward copied keccak fullState := by
  cases finalizing <;> cases forward <;> cases copied <;> cases fullState <;> cases keccak <;> cases v <;> decide +kernel

set_option maxHeartbeats 1600000 in
theorem save_before_cursor [bindings : Bindings] {initial s : RamState}
    {v : Variant} {forward copied keccak fullState : Bool} {inputs : Array Input} {split : Nat}
    (boundary : ReturnBoundary) (finalizing : Bool)
    (hCall : ValidInvocation bindings v (resetMode finalizing forward copied) initial inputs split keccak fullState)
    (inv : Invariant initial v (resetMode finalizing forward copied) s keccak fullState)
    (sp : s.GPR[4] ≠ boundary.rsp)
    (ip : s.RIP = testAddress v finalizing keccak fullState forward copied + (16 : BitVec 64) +
      ((if countSaved v finalizing forward copied fullState then (if fullState then 5 else 4) else 0) : BitVec 64))
    (stack : stackPtr s = frameBase initial v (resetMode finalizing forward copied) keccak fullState) :
    ∃ n t, Advances boundary n s t ∧
      Invariant initial v (resetMode finalizing forward copied) t keccak fullState ∧
      t.GPR[4] ≠ boundary.rsp ∧ t.RIP = cursorAddress v finalizing forward copied keccak fullState ∧
      AgreesExcept (beforeStoreChanges initial v finalizing forward copied keccak fullState) s t ∧
      (finalizing = true →
        (Operand.mem (frameBase initial v (resetMode finalizing forward copied) keccak fullState +
          (if copied && fullState then 16 else 8)) : Operand 64).read t =
        (beforeOutputOperand initial v forward copied keccak fullState).read s) := by
  let mode := resetMode finalizing forward copied
  let p := testAddress v finalizing keccak fullState forward copied + 16 +
    (if countSaved v finalizing forward copied fullState then (if fullState then 5 else 4) else 0)
  have hslot : frameBase initial v mode keccak fullState + 8 =
      initial.regValue .rsp - BitVec.ofNat 64 (mode.frameSize v keccak fullState - 8) := by
    cases finalizing <;> cases forward <;> cases copied <;> cases fullState <;> cases v <;>
      simp [mode, frameBase, resetMode, Mode.frameSize, BitVec.sub_eq_add_neg, BitVec.add_assoc]
  by_cases hs : storeBeforeOutput finalizing copied fullState = true
  · let am : AddrMode := .sib 4 none 0 (.d8 8)
    have hmin : 8 ≤ mode.frameSize v keccak fullState - 8 := by
      cases finalizing <;> cases forward <;> cases copied <;> cases fullState <;> cases keccak <;> cases v <;> decide
    have hbudget : mode.frameSize v keccak fullState - 8 ≤ (mode.entry v keccak fullState).minStackBytes := by
      rw [Mode.stackBudget mode v keccak fullState]
      omega
    have addr : storeAddrAt p am (3 + am.tail.length) s =
        initial.regValue .rsp - BitVec.ofNat 64 (mode.frameSize v keccak fullState - 8) := by
      rw [← hslot]
      exact congrArg (· + (8 : BitVec 64)) stack
    obtain ⟨t, a, it, bt, pt, value, ft⟩ := save_register boundary hCall inv sp ip _ hmin hbudget
      5 am (by decide) addr
      (by cases finalizing <;> cases forward <;> cases copied <;> cases fullState <;> cases keccak <;> cases v <;>
            simp [storeBeforeOutput] at hs
          all_goals unfold ImageAt; decide +kernel)
    rw [← hslot] at value ft
    have hc := cursorAddress_eq v finalizing forward copied keccak fullState
    simp only [hs, ↓reduceIte] at hc
    refine ⟨1, t, a, it, bt, ?_, ?_, ?_⟩
    · exact pt.trans hc
    · simpa only [beforeStoreChanges, hs, ↓reduceIte] using ft
    · intro hf
      subst finalizing
      have hn : (copied && fullState) = false := by
        cases copied <;> cases fullState <;> first | rfl | simp [storeBeforeOutput] at hs
      simpa [beforeOutputOperand, hn, mode] using value
  · refine ⟨0, s, (advances_zero _ _ _).mpr rfl, inv, sp, ?_, ?_, ?_⟩
    · have hc := cursorAddress_eq v finalizing forward copied keccak fullState
      have hc' : s.RIP = cursorAddress v finalizing forward copied keccak fullState := by
        rw [ip]
        simpa [hs] using hc
      exact hc'
    · simp only [beforeStoreChanges, hs]
      exact AgreesExcept.refl _ _
    · intro hf
      subst finalizing
      cases copied <;> cases fullState <;> simp [storeBeforeOutput] at hs
      rfl

def cursorChanges (v : Variant) (finalizing forward copied fullState : Bool) : List Component :=
  if countSaved v finalizing forward copied fullState then [.reg 5, .rip] else []

set_option maxHeartbeats 800000 in
theorem prepare_cursor [bindings : Bindings] {initial s : RamState}
    {v : Variant} {forward copied keccak fullState : Bool} {inputs : Array Input} {split : Nat}
    (boundary : ReturnBoundary) (finalizing : Bool)
    (hCall : ValidInvocation bindings v (resetMode finalizing forward copied) initial inputs split keccak fullState)
    (inv : Invariant initial v (resetMode finalizing forward copied) s keccak fullState)
    (sp : s.GPR[4] ≠ boundary.rsp)
    (ip : s.RIP = cursorAddress v finalizing forward copied keccak fullState)
    (stack : stackPtr s = frameBase initial v (resetMode finalizing forward copied) keccak fullState) :
    ∃ n t, Advances boundary n s t ∧
      Invariant initial v (resetMode finalizing forward copied) t keccak fullState ∧
      t.GPR[4] ≠ boundary.rsp ∧ t.RIP = boundAddress v finalizing keccak fullState forward copied ∧
      AgreesExcept (cursorChanges v finalizing forward copied fullState) s t ∧
      (countSaved v finalizing forward copied fullState = true →
        (Operand.reg 5 : Operand 64).read t =
          statePointer initial v (resetMode finalizing forward copied) keccak fullState + 200) := by
  by_cases hc : countSaved v finalizing forward copied fullState = true
  · let mode := resetMode finalizing forward copied
    let p := cursorAddress v finalizing forward copied keccak fullState
    let am : AddrMode := .sib 4 none 0 (.d32 (BitVec.ofNat 32 (mode.stateOffset v keccak fullState + 200)))
    have nomem : ∀ c ∈ [Component.reg 5, .rip], ∀ a, ¬c.Covers a := by simp [Component.Covers]
    obtain ⟨t, a, it, bt, e, f⟩ := advance (cs := [.reg 5, .rip])
      (effect := leaR64Effect p 5 am) hCall
      (lea_r64_effect_step p 0x48 (by unfold RexWPrefix; decide) 5 am
        (by cases finalizing <;> cases forward <;> cases copied <;> cases fullState <;> cases keccak <;> cases v <;> decide) rfl rfl)
      (by cases finalizing <;> cases forward <;> cases copied <;> cases fullState <;> cases keccak <;> cases v <;>
            simp [countSaved, resetMode, Setup.firstKind, Loop.Kind.largeFollower] at hc
          all_goals unfold ImageAt; decide +kernel)
      (by simp [leaR64Effect_components]) (nomem_writes nomem) (by decide) inv sp ip
    refine ⟨1, t, a, it, bt, ?_, ?_, fun _ ↦ ?_⟩
    · have h := e.rip
      change t.RIP = p + (8 : BitVec 64) at h
      simpa only [p, cursorAddress, hc, ↓reduceIte, BitVec.sub_add_cancel] using h
    · simpa only [cursorChanges, hc, ↓reduceIte] using f
    · have h := e.writes
      have ha : am.addr s (p + 8) =
          (Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 (mode.stateOffset v keccak fullState) + 200 := by
        cases finalizing <;> cases forward <;> cases copied <;> cases fullState <;> cases keccak <;> cases v <;>
          rw [BitVec.add_assoc] <;> rfl
      exact h.trans (ha.trans (congrArg (fun x ↦ x + BitVec.ofNat 64 (mode.stateOffset v keccak fullState) + 200) stack))
  · refine ⟨0, s, (advances_zero _ _ _).mpr rfl, inv, sp, ?_, ?_, fun h ↦ (hc h).elim⟩
    · simpa [cursorAddress, hc] using ip
    · simp only [cursorChanges, hc]
      exact AgreesExcept.refl _ _

def beforeOutputSlot (initial : RamState) (v : Variant) (keccak : Bool := false) (fullState : Bool := false) (forward : Bool := false) : BitVec 64 := frameBase (keccak := keccak) (fullState := fullState) initial v (resetMode true forward) + 8

private theorem beforeOutputSlot_sub {forward : Bool} (initial : RamState) (v : Variant) (keccak : Bool := false) (fullState : Bool := false) :
    beforeOutputSlot (forward := forward) (keccak := keccak) (fullState := fullState) initial v = initial.regValue .rsp - (480 : BitVec 64) := by
  cases forward <;> simp [beforeOutputSlot, resetMode, frameBase, Mode.frameSize, BitVec.sub_eq_add_neg, BitVec.add_assoc]

theorem save_before_output {forward : Bool} [bindings : Bindings] {initial s : RamState}
    {v : Variant} {keccak fullState : Bool} {inputs : Array Input} {split : Nat} (boundary : ReturnBoundary)
    (hCall : ValidInvocation (keccak := keccak) (fullState := fullState) bindings v (resetMode true forward) initial inputs split)
    (inv : Invariant (keccak := keccak) (fullState := fullState) initial v (resetMode true forward) s)
    (sp : s.GPR[4] ≠ boundary.rsp)
    (ip : s.RIP = testAddress (forward := forward) (keccak := keccak) (fullState := fullState) v true + (16 : BitVec 64))
    (stack : stackPtr s = frameBase (keccak := keccak) (fullState := fullState) initial v (resetMode true forward)) :
    ∃ t, Advances boundary 1 s t ∧ Invariant (keccak := keccak) (fullState := fullState) initial v (resetMode true forward) t ∧
      t.GPR[4] ≠ boundary.rsp ∧ t.RIP = boundAddress (forward := forward) (keccak := keccak) (fullState := fullState) v true ∧
      (Operand.mem (beforeOutputSlot (forward := forward) (keccak := keccak) (fullState := fullState) initial v) : Operand 64).read t =
        (Operand.reg 5 : Operand 64).read s ∧
      AgreesExcept [.mem (beforeOutputSlot (forward := forward) (keccak := keccak) (fullState := fullState) initial v) 8, .rip] s t := by

  let p := testAddress (forward := forward) (keccak := keccak) (fullState := fullState) v true + (16 : BitVec 64)
  let am : AddrMode := .sib 4 none 0 (.d8 8)
  have addr : storeAddrAt p am (3 + am.tail.length) s = initial.regValue .rsp - (480 : BitVec 64) := by
    rw [← beforeOutputSlot_sub (forward := forward) initial v keccak fullState]
    exact congrArg (· + (8 : BitVec 64)) stack
  have hbudget : 480 ≤ ((resetMode true forward).entry v keccak fullState).minStackBytes := by
    rw [Mode.stackBudget (keccak := keccak) (fullState := fullState)]; cases forward <;> cases fullState <;> cases keccak <;> cases v <;> decide
  obtain ⟨t, a, it, bt, pt, value, ft⟩ := save_register boundary hCall inv sp ip 480
    (by decide) hbudget 5 am (by decide) addr
    (by cases forward <;> cases fullState <;> cases keccak <;> cases v <;> unfold ImageAt <;> decide +kernel)
  refine ⟨t, a, it, bt, ?_, ?_, ?_⟩
  · change t.RIP = p + (5 : BitVec 64) at pt
    simpa only [p, am, testAddress, boundAddress, resetMode, Bool.false_eq_true, ↓reduceIte,
      BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using pt
  · rw [beforeOutputSlot_sub (keccak := keccak) (fullState := fullState)]
    exact value
  · rw [beforeOutputSlot_sub (keccak := keccak) (fullState := fullState)]
    exact ft

def saveChanges (initial : RamState) (v : Variant) (finalizing : Bool) (keccak : Bool := false) (fullState : Bool := false) (forward : Bool := false) : List Component :=
  if finalizing then [.mem (beforeOutputSlot (forward := forward) (keccak := keccak) (fullState := fullState) initial v) 8, .rip] else []

def resetChanges (initial : RamState) (v : Variant) (finalizing : Bool)
    (keccak : Bool := false) (fullState : Bool := false) (forward : Bool := false)
    (copied : Bool := false) : List Component :=
  if copied then
    testChanges ++ countSaveChanges initial v finalizing forward copied keccak fullState ++
      boundChanges (splitLayout v finalizing forward copied fullState) ++
      beforeStoreChanges initial v finalizing forward copied keccak fullState ++
      cursorChanges v finalizing forward copied fullState ++
      [.reg ((Setup.firstKind (resetMode finalizing forward copied)).stateReg v fullState)]
  else testChanges ++ boundChanges finalizing ++ saveChanges initial v finalizing keccak fullState forward

private theorem save_if_needed [bindings : Bindings] {initial s : RamState}
    {v : Variant} {forward copied keccak fullState : Bool} {inputs : Array Input} {split : Nat}
    (boundary : ReturnBoundary) (finalizing : Bool)
    (hCall : ValidInvocation bindings v (resetMode finalizing forward copied) initial inputs split keccak fullState)
    (inv : Invariant initial v (resetMode finalizing forward copied) s keccak fullState)
    (sp : s.GPR[4] ≠ boundary.rsp)
    (ip : s.RIP = testAddress v finalizing keccak fullState forward copied + (16 : BitVec 64) +
      ((if countSaved v finalizing forward copied fullState then (if fullState then 5 else 4) else 0) : BitVec 64))
    (stack : stackPtr s = frameBase initial v (resetMode finalizing forward copied) keccak fullState) :
    ∃ n t, Advances boundary n s t ∧
      Invariant initial v (resetMode finalizing forward copied) t keccak fullState ∧
      t.GPR[4] ≠ boundary.rsp ∧ t.RIP = boundAddress v finalizing keccak fullState forward copied ∧
      AgreesExcept (beforeStoreChanges initial v finalizing forward copied keccak fullState ++
        cursorChanges v finalizing forward copied fullState) s t ∧
      (finalizing = true →
        (Operand.mem (frameBase initial v (resetMode finalizing forward copied) keccak fullState +
          (if copied && fullState then 16 else 8)) : Operand 64).read t =
        (beforeOutputOperand initial v forward copied keccak fullState).read s) ∧
      (countSaved v finalizing forward copied fullState = true →
        (Operand.reg 5 : Operand 64).read t =
          statePointer initial v (resetMode finalizing forward copied) keccak fullState + 200) := by
  obtain ⟨n1, s1, a1, i1, b1, p1, f1, saved⟩ :=
    save_before_cursor boundary finalizing hCall inv sp ip stack
  have sp1 : stackPtr s1 = frameBase initial v (resetMode finalizing forward copied) keccak fullState :=
    (f1.read (r := 4) (n := 64) (by unfold beforeStoreChanges; split <;> simp)).trans stack
  obtain ⟨n2, s2, a2, i2, b2, p2, f2, cursor⟩ :=
    prepare_cursor boundary finalizing hCall i1 b1 p1 sp1
  refine ⟨n1 + n2, s2, a1.trans a2, i2, b2, p2, f1.trans f2, ?_, cursor⟩
  intro hf
  have ext : s2.external = s1.external := f2.external
    (by unfold cursorChanges; split <;> simp [Component.Covers])
  exact (readMem_of_external_eq ext _).trans (saved hf)

private theorem test_before_output {initial s t : RamState} {v : Variant}
    {forward copied keccak fullState : Bool}
    (ha : AgreesExcept (testChanges ++ countSaveChanges initial v true forward copied keccak fullState) s t) :
    (beforeOutputOperand initial v forward copied keccak fullState).read t =
      (beforeOutputOperand initial v forward copied keccak fullState).read s := by
  by_cases hm : (copied && fullState) = true
  · have hh : copied = true ∧ fullState = true := by simpa only [Bool.and_eq_true] using hm
    obtain ⟨hc, hf⟩ := hh
    subst copied
    subst fullState
    apply memLoad_congr
    intro i hi
    simp only [memByte, PhysicalMemory.read]
    rw [ha.byte]
    intro c hc hcover
    have cs : testChanges ++ countSaveChanges initial v true forward true keccak true =
        [.reg 0, .reg 1, .flags, .rip,
          .mem (frameBase initial v (resetMode true forward true) keccak true + 8) 8, .rip] := by
      cases forward <;> rfl
    rw [cs] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> try exact hcover.elim
    obtain ⟨j, hj, he⟩ := hcover
    have apart : OffsetsApart (8 : BitVec 64) 8 (16 : BitVec 64) 8 := by unfold OffsetsApart; decide +kernel
    exact apart.ne (frameBase initial v (resetMode true forward true) keccak true) hj hi (by decide) he.symm
  · have hr := ha.read (r := 5) (n := 64) (by
      unfold countSaveChanges
      split <;> simp [testChanges])
    simpa only [beforeOutputOperand, hm, Bool.false_eq_true, ↓reduceIte] using hr

private theorem save_count_preserved {initial s t : RamState} {v : Variant}
    {finalizing forward copied keccak fullState : Bool}
    (ha : AgreesExcept (beforeStoreChanges initial v finalizing forward copied keccak fullState ++
      cursorChanges v finalizing forward copied fullState) s t)
    (hc : countSaved v finalizing forward copied fullState = true) :
    (Operand.mem (countSlot initial v finalizing forward copied keccak fullState) : Operand 64).read t =
      (Operand.mem (countSlot initial v finalizing forward copied keccak fullState) : Operand 64).read s := by
  have hf : finalizing = true := by
    cases finalizing <;> simp [countSaved, resetMode, Setup.firstKind, Loop.Kind.largeFollower] at hc ⊢
  have hcopy : copied = true := by
    cases copied <;> cases finalizing <;> cases forward <;>
      simp [countSaved, resetMode, Setup.firstKind, Loop.Kind.largeFollower] at hc ⊢
  subst finalizing
  subst copied
  cases fullState with
  | true =>
    apply readMem_of_external_eq
    apply ha.external
    cases forward <;>
      simp [beforeStoreChanges, storeBeforeOutput, cursorChanges, countSaved, resetMode,
        Setup.firstKind, Loop.Kind.largeFollower, Component.Covers]
  | false =>
    apply memLoad_congr
    intro i hi
    simp only [memByte, PhysicalMemory.read]
    rw [ha.byte]
    intro c hm hcover
    have cs : beforeStoreChanges initial v true forward true keccak false ++ cursorChanges v true forward true false =
        [.mem (frameBase initial v (resetMode true forward true) keccak false + 8) 8, .rip, .reg 5, .rip] := by
      simp [beforeStoreChanges, storeBeforeOutput, cursorChanges, hc]
    rw [cs] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl <;> try exact hcover.elim
    obtain ⟨j, hj, he⟩ := hcover
    have apart : OffsetsApart (8 : BitVec 64) 8 (0 : BitVec 64) 8 := by unfold OffsetsApart; decide +kernel
    exact apart.ne (frameBase initial v (resetMode true forward true) keccak false) hj hi (by decide) he.symm

set_option maxHeartbeats 1600000 in
theorem reset_selection [bindings : Bindings] {initial s : RamState}
    {v : Variant} {forward copied keccak fullState : Bool} {inputs : Array Input} {split : Nat}
    (boundary : ReturnBoundary) (finalizing : Bool)
    (hCall : ValidInvocation bindings v (resetMode finalizing forward copied) initial inputs split keccak fullState)
    (inv : Invariant initial v (resetMode finalizing forward copied) s keccak fullState)
    (sp : s.GPR[4] ≠ boundary.rsp)
    (ip : s.RIP = testAddress v finalizing keccak fullState forward copied)
    (stack : stackPtr s = frameBase initial v (resetMode finalizing forward copied) keccak fullState)
    (x y : BitVec 64)
    (xval : (Operand.reg (splitRegister (splitLayout v finalizing forward copied fullState)) : Operand 64).read s = x)
    (yval : (Operand.reg 15 : Operand 64).read s = y)
    (emptyBound : (Operand.reg (boundRegister (splitLayout v finalizing forward copied fullState)) : Operand 64).read s = (0 : BitVec 64)) :
    ∃ n t, Advances boundary n s t ∧
      Invariant initial v (resetMode finalizing forward copied) t keccak fullState ∧
      t.RIP = (if x = 0#64 ∨ y = 0#64 then skipAddress v finalizing keccak fullState forward copied
        else (Setup.firstKind (resetMode finalizing forward copied)).start v keccak fullState) ∧
      (Operand.reg (boundRegister (splitLayout v finalizing forward copied fullState)) : Operand 64).read t =
        BitVec.ofNat 64 (min x.toNat y.toNat) ∧
      AgreesExcept (resetChanges initial v finalizing keccak fullState forward copied) s t ∧
      (¬(x = 0#64 ∨ y = 0#64) →
        (Operand.reg 0 : Operand 64).read t = (0 : BitVec 64) ∧
        (Operand.reg ((Setup.firstKind (resetMode finalizing forward copied)).stateReg v fullState) : Operand 64).read t =
          statePointer initial v (resetMode finalizing forward copied) keccak fullState ∧
        (finalizing = true →
          (Operand.mem (frameBase initial v (resetMode finalizing forward copied) keccak fullState +
            (if copied && fullState then 16 else 8)) : Operand 64).read t =
            (beforeOutputOperand initial v forward copied keccak fullState).read s) ∧
        (countSaved v finalizing forward copied fullState = true →
          (Operand.reg 5 : Operand 64).read t =
            statePointer initial v (resetMode finalizing forward copied) keccak fullState + 200)) ∧
      (x = 0#64 ∨ y = 0#64 → finalizing = true →
        (beforeOutputOperand initial v forward copied keccak fullState).read t =
          (beforeOutputOperand initial v forward copied keccak fullState).read s) ∧
      (countSaved v finalizing forward copied fullState = true →
        (Operand.mem (countSlot initial v finalizing forward copied keccak fullState) : Operand 64).read t =
          (Operand.reg 15 : Operand 64).read s) := by
  obtain ⟨nt, s1, a1, i1, b1, p1, f1, saved1⟩ :=
    reset_test boundary finalizing hCall inv sp ip stack x y xval yval
  have f1' : AgreesExcept (resetChanges initial v finalizing keccak fullState forward copied) s s1 :=
    f1.mono (by
      intro c hc
      cases copied with
      | false =>
        have hc' : c ∈ testChanges := by
          cases finalizing <;> cases forward <;> exact hc
        simp only [resetChanges, Bool.false_eq_true, ↓reduceIte, List.mem_append]
        exact .inl (.inl hc')
      | true =>
        exact List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_left _ (List.mem_append_left _ hc))))
  by_cases hz : x = 0#64 ∨ y = 0#64
  · refine ⟨nt, s1, a1, i1, ?_, ?_, f1', fun hn ↦ (hn hz).elim, ?_, saved1⟩
    · simpa only [hz, ↓reduceIte] using p1
    · rw [f1.read (by
        cases hl : splitLayout v finalizing forward copied fullState <;>
          unfold countSaveChanges <;> split <;> simp [testChanges, boundRegister]), emptyBound]
      rcases hz with rfl | rfl <;> simp
    · intro _ hf
      subst finalizing
      exact test_before_output f1
  have p1' := p1
  simp only [hz, ↓reduceIte] at p1'
  have sp1 : stackPtr s1 = frameBase initial v (resetMode finalizing forward copied) keccak fullState :=
    (f1.read (r := 4) (n := 64) (by unfold countSaveChanges; split <;> simp [testChanges])).trans stack
  obtain ⟨n2, s2, a2, i2, b2, p2, f2, save2, cursor2⟩ :=
    save_if_needed boundary finalizing hCall i1 b1 p1' sp1
  have f2' : AgreesExcept (resetChanges initial v finalizing keccak fullState forward copied) s1 s2 :=
    f2.mono (by
      intro c hc
      cases copied with
      | false =>
        have hc' : c ∈ saveChanges initial v finalizing keccak fullState forward := by
          cases finalizing with
          | false =>
            simp [beforeStoreChanges, cursorChanges, storeBeforeOutput, countSaved, resetMode,
              Setup.firstKind, Loop.Kind.largeFollower] at hc
          | true =>
            cases forward <;>
              simpa [beforeStoreChanges, cursorChanges, storeBeforeOutput, countSaved, resetMode,
                Setup.firstKind, Loop.Kind.largeFollower, saveChanges, beforeOutputSlot] using hc
        simp only [resetChanges, Bool.false_eq_true, ↓reduceIte, List.mem_append]
        exact .inr hc'
      | true =>
        simp only [List.mem_append] at hc
        rcases hc with h | h
        · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))
        · exact List.mem_append_left _ (List.mem_append_right _ h))
  have rx2 : (Operand.reg (splitRegister (splitLayout v finalizing forward copied fullState)) : Operand 64).read s2 = x := by
    rw [f2.read (by
      cases hl : splitLayout v finalizing forward copied fullState <;>
        unfold beforeStoreChanges cursorChanges <;> split <;> split <;> simp [splitRegister]),
      f1.read (by
        cases hl : splitLayout v finalizing forward copied fullState <;>
          unfold countSaveChanges <;> split <;> simp [testChanges, splitRegister])]
    exact xval
  have ry2 : (Operand.reg 15 : Operand 64).read s2 = y := by
    rw [f2.read (by unfold beforeStoreChanges cursorChanges; split <;> split <;> simp),
      f1.read (by unfold countSaveChanges; split <;> simp [testChanges])]
    exact yval
  obtain ⟨s3, a3, i3, b3, p3, bound3, f3, rbp3⟩ :=
    bound_steps boundary (splitLayout v finalizing forward copied fullState) hCall i2 b2 p2 x y
      (fun h ↦ hz (.inl h)) (fun h ↦ hz (.inr h)) rx2 ry2
      (by cases finalizing <;> cases forward <;> cases copied <;> cases fullState <;> cases keccak <;> cases v <;>
        unfold ImageAt <;> decide +kernel)
  have f3' : AgreesExcept (resetChanges initial v finalizing keccak fullState forward copied) s2 s3 :=
    f3.mono (by
      intro c hc
      cases copied with
      | false =>
        have hc' : c ∈ boundChanges finalizing := by
          cases finalizing <;> cases forward <;> exact hc
        simp only [resetChanges, Bool.false_eq_true, ↓reduceIte, List.mem_append]
        exact .inl (.inr hc')
      | true =>
        exact List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_left _ (List.mem_append_right _ hc))))
  have sp3 : stackPtr s3 = frameBase initial v (resetMode finalizing forward copied) keccak fullState := by
    change (Operand.reg 4 : Operand 64).read s3 = _
    rw [f3.read (by cases hl : splitLayout v finalizing forward copied fullState <;> decide),
      f2.read (by unfold beforeStoreChanges cursorChanges; split <;> split <;> simp)]
    exact sp1
  obtain ⟨n4, s4, a4, i4, p4, index4, state4, f4⟩ :=
    enter_loop boundary finalizing hCall i3 b3 p3 sp3
  have f4' : AgreesExcept (resetChanges initial v finalizing keccak fullState forward copied) s3 s4 :=
    f4.mono (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals cases copied <;> cases finalizing <;> cases forward <;>
        simp [resetChanges, testChanges, boundChanges, boundRegister, stateRegister, splitRegister,
          resetMode, Setup.firstKind, Loop.Kind.stateReg, Loop.Kind.largeFollower])
  have ext43 : s4.external = s3.external := f4.external (by simp [Component.Covers])
  have ext32 : s3.external = s2.external := f3.external (bound_nomem _)
  refine ⟨nt + (n2 + (6 + n4)), s4, a1.trans (a2.trans (a3.trans a4)), i4, ?_, ?_,
    same_trans f1' (same_trans f2' (same_trans f3' f4')), ?_, fun h ↦ (hz h).elim, ?_⟩
  · simpa only [hz, ↓reduceIte] using p4
  · exact (f4.read (by
      cases finalizing <;> cases forward <;> cases copied <;> cases fullState <;> cases v <;> decide)).trans bound3
  · intro _
    refine ⟨index4, state4, ?_, ?_⟩
    · intro hf
      rw [readMem_of_external_eq (ext43.trans ext32), save2 hf]
      subst finalizing
      exact test_before_output f1
    · intro hc
      have preserved : (Operand.reg 5 : Operand 64).read s4 = (Operand.reg 5 : Operand 64).read s3 :=
        f4.read (by
          cases finalizing <;> cases forward <;> cases copied <;> cases fullState <;> cases v <;>
            simp [countSaved, resetMode, Setup.firstKind, Loop.Kind.largeFollower] at hc
          all_goals decide)
      exact preserved.trans (rbp3.trans (cursor2 hc))
  · intro hc
    rw [readMem_of_external_eq (ext43.trans ext32), save_count_preserved f2 hc, saved1 hc]

private theorem resetChanges_covers {forward : Bool} {initial : RamState} {v : Variant} {keccak fullState : Bool} {finalizing : Bool}
    {c : Component} {address : BitVec 64}
    (hc : c ∈ resetChanges (forward := forward) (keccak := keccak) (fullState := fullState) initial v finalizing) (ha : c.Covers address) :
    finalizing = true ∧ ∃ i, i < 8 ∧ address = beforeOutputSlot (forward := forward) (keccak := keccak) (fullState := fullState) initial v + BitVec.ofNat 64 i := by
  cases finalizing <;>
    simp only [resetChanges, testChanges, boundChanges, saveChanges, Bool.false_eq_true,
      ↓reduceIte, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  · rcases hc with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl) <;> exact ha.elim
  · rcases hc with ((rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl)) | (rfl | rfl)
    all_goals try exact ha.elim
    exact ⟨rfl, ha⟩

private theorem resetChanges_frame {initial : RamState} {v : Variant}
    {finalizing forward copied keccak fullState : Bool} {c : Component} {address : BitVec 64}
    (hc : c ∈ resetChanges initial v finalizing keccak fullState forward copied) (ha : c.Covers address) :
    finalizing = true ∧ ∃ offset : Nat, (offset = 0 ∨ offset = 8) ∧
      ∃ i, i < 8 ∧ address = frameBase initial v (resetMode finalizing forward copied) keccak fullState +
        BitVec.ofNat 64 offset + BitVec.ofNat 64 i := by
  cases copied with
  | false =>
    obtain ⟨hf, i, hi, he⟩ := resetChanges_covers hc ha
    subst finalizing
    exact ⟨rfl, 8, .inr rfl, i, hi, he⟩
  | true =>
    simp only [resetChanges, ↓reduceIte, List.mem_append] at hc
    rcases hc with (((((h | h) | h) | h) | h) | h)
    · exact (test_nomem c h address ha).elim
    · unfold countSaveChanges at h
      split at h
      next hs =>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl
        · have hf : finalizing = true := by
            cases finalizing <;> simp [countSaved, resetMode, Setup.firstKind, Loop.Kind.largeFollower] at hs ⊢
          subst finalizing
          obtain ⟨i, hi, he⟩ := ha
          cases fullState
          · exact ⟨rfl, 0, .inl rfl, i, hi, he⟩
          · exact ⟨rfl, 8, .inr rfl, i, hi, he⟩
        · exact ha.elim
      next => simp at h
    · exact (bound_nomem _ c h address ha).elim
    · unfold beforeStoreChanges at h
      split at h
      next hs =>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl
        · have hf : finalizing = true := by
            cases finalizing <;> simp [storeBeforeOutput] at hs ⊢
          subst finalizing
          obtain ⟨i, hi, he⟩ := ha
          exact ⟨rfl, 8, .inr rfl, i, hi, he⟩
        · exact ha.elim
      next => simp at h
    · unfold cursorChanges at h
      split at h
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl <;> exact ha.elim
      · simp at h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      subst c
      exact ha.elim

theorem plain_initialized {initial s t : RamState} {v : Variant} {keccak fullState : Bool}
    (initialized : Initialized (keccak := keccak) (fullState := fullState) initial v .plain s) (ha : AgreesExcept plainChanges s t) :
    Initialized (keccak := keccak) (fullState := fullState) initial v .plain t := by
  have he := ha.external plain_nomem
  refine ⟨(ha.read (r := 4) (n := 64) (by decide)).trans initialized.stack,
    ⟨fun i ↦ (readMem_of_external_eq he _).trans (initialized.saved.saved i),
      (readMem_of_external_eq he _).trans initialized.saved.returnSlot⟩, ?_⟩
  intro i hi
  rw [he]
  exact initialized.zero i hi

set_option maxHeartbeats 1600000 in
theorem reset_initialized {initial s t : RamState} {v : Variant}
    {finalizing forward copied keccak fullState : Bool}
    (initialized : Initialized initial v (resetMode finalizing forward copied) s keccak fullState)
    (ha : AgreesExcept (resetChanges initial v finalizing keccak fullState forward copied) s t) :
    Initialized initial v (resetMode finalizing forward copied) t keccak fullState := by
  refine ⟨(ha.read (r := 4) (n := 64) (by
    cases finalizing <;> cases forward <;> cases copied <;> cases fullState <;> cases v <;>
      simp [resetChanges, testChanges, boundChanges, boundRegister, stateRegister, splitRegister,
        saveChanges, countSaveChanges, beforeStoreChanges, cursorChanges, countSaved, storeBeforeOutput,
        splitLayout, resetMode, Setup.firstKind, Loop.Kind.boundReg, Loop.Kind.stateReg, Loop.Kind.largeFollower])).trans initialized.stack,
    initialized.saved.of_localFrame (v := v) (mode := resetMode finalizing forward copied)
      (keccak := keccak) ha ?_, ?_⟩
  · intro c hc address hcover
    obtain ⟨hf, offset, ho, i, hi, he⟩ := resetChanges_frame hc hcover
    subst finalizing
    refine ⟨offset + i + 8, ?_, ?_⟩
    · rcases ho with rfl | rfl <;> cases forward <;> cases copied <;> cases fullState <;> cases v <;>
        simp [resetMode, Mode.frameSize, Mode.pushCount] <;> omega
    · rw [he]
      rcases ho with rfl | rfl
      · simp only [Nat.zero_add, BitVec.ofNat_add, BitVec.ofNat_eq_ofNat,
          BitVec.sub_eq_add_neg, BitVec.add_zero, BitVec.add_assoc]
        rw [BitVec.add_comm (BitVec.ofNat 64 i) 8#64]
        rw [← BitVec.add_assoc (-8#64) 8#64 (BitVec.ofNat 64 i)]
        simp only [BitVec.reduceNeg, BitVec.reduceAdd, BitVec.zero_add]
      · simp only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat,
          BitVec.sub_eq_add_neg, BitVec.add_assoc]
        rw [BitVec.add_comm (BitVec.ofNat 64 i) 8#64]
        rw [← BitVec.add_assoc (-8#64) 8#64 (8#64 + BitVec.ofNat 64 i)]
        simp only [BitVec.reduceNeg, BitVec.reduceAdd, BitVec.zero_add]
  · intro i hi
    rw [ha.byte]
    · exact initialized.zero i hi
    · intro c hc hcover
      obtain ⟨hf, offset, ho, j, hj, he⟩ := resetChanges_frame hc hcover
      subst finalizing
      have apart : OffsetsApart (BitVec.ofNat 64 offset) 8
          (BitVec.ofNat 64 ((resetMode true forward copied).stateOffset v keccak fullState)) 201 := by
        rcases ho with rfl | rfl <;> cases forward <;> cases copied <;> cases fullState <;> cases keccak <;> cases v <;>
          unfold OffsetsApart <;> decide +kernel
      exact apart.ne (frameBase initial v (resetMode true forward copied) keccak fullState) hj hi (by decide) he.symm

set_option maxHeartbeats 800000 in
theorem reset_outputSlot {initial s t : RamState} {v : Variant}
    {finalizing forward copied keccak fullState : Bool}
    (ha : AgreesExcept (resetChanges initial v finalizing keccak fullState forward copied) s t) :
    (Operand.mem (outputSlot initial v (resetMode finalizing forward copied) keccak fullState) : Operand 64).read t =
      (Operand.mem (outputSlot initial v (resetMode finalizing forward copied) keccak fullState) : Operand 64).read s := by
  apply memLoad_congr
  intro i hi
  simp only [memByte, PhysicalMemory.read]
  rw [ha.byte]
  intro c hc hcover
  obtain ⟨hf, offset, ho, j, hj, he⟩ := resetChanges_frame hc hcover
  subst finalizing
  have apart : OffsetsApart (BitVec.ofNat 64 offset) 8
      (BitVec.ofNat 64 ((resetMode true forward copied).outputSlotOffset v keccak fullState)) 8 := by
    rcases ho with rfl | rfl <;> cases forward <;> cases copied <;> cases fullState <;> cases keccak <;> cases v <;>
      unfold OffsetsApart <;> decide +kernel
  exact apart.ne (frameBase initial v (resetMode true forward copied) keccak fullState) hj hi (by decide) he.symm

set_option maxHeartbeats 800000 in
theorem reset_table_registers {initial s t : RamState} {v : Variant}
    {finalizing forward copied keccak fullState : Bool}
    (ha : AgreesExcept (resetChanges initial v finalizing keccak fullState forward copied) s t) :
    (Operand.reg 12 : Operand 64).read t = (Operand.reg 12 : Operand 64).read s ∧
    (Operand.reg 14 : Operand 64).read t = (Operand.reg 14 : Operand 64).read s ∧
    (Operand.reg 15 : Operand 64).read t = (Operand.reg 15 : Operand 64).read s := by
  refine ⟨ha.read ?_, ha.read ?_, ha.read ?_⟩ <;>
    cases finalizing <;> cases forward <;> cases copied <;> cases fullState <;> cases v <;>
      simp [resetChanges, testChanges, boundChanges, boundRegister, stateRegister, splitRegister,
        saveChanges, countSaveChanges, beforeStoreChanges, cursorChanges, countSaved, storeBeforeOutput,
        splitLayout, resetMode, Setup.firstKind, Loop.Kind.boundReg, Loop.Kind.stateReg, Loop.Kind.largeFollower]

theorem finalize_reset_before_output {forward : Bool} {initial s t : RamState} {v : Variant} {keccak fullState : Bool}
    (ha : AgreesExcept (resetChanges (forward := forward) (keccak := keccak) (fullState := fullState) initial v true) s t) :
    (Operand.reg 5 : Operand 64).read t = (Operand.reg 5 : Operand 64).read s := by
  exact ha.read (by simp [resetChanges, testChanges, boundChanges, boundRegister, stateRegister, splitRegister, saveChanges])

end Selection

end Sha3.Proofs.Wrapper
