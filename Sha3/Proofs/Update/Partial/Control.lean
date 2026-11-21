import Sha3.Proofs.Update.Partial.Code
import Sha3.Proofs.X86.Instructions.Test.Triple
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Program.Compose
import Sha3.Proofs.Permutation.LoadStore.Memory

namespace Sha3.Proofs.Update.Partial

open X86 X86.Machine X86.UserProcess X86Proofs Sha3.Spec.Program

theorem scalar_advance [Bindings] {v : Variant} {boundary : ReturnBoundary}
    {p : BitVec 64} {bytes : List UInt8} {effect : RamState → Effect}
    {pre : RamState → Prop} {s : RamState}
    (step : StepEffect pre (codeRange p bytes) effect)
    (hmem : (p, bytes) ∈ instructionBytes v)
    (hready : ReadyToStep s) (hcode : CodeIn Extracted.programImage s) (hpre : pre s)
    (hnoMem : ∀ c ∈ (effect s).components, ∀ x, ¬ c.Covers x)
    (hnext : InProgram (effect s).rip) (hb : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      (effect s).Holds s t := by
  obtain ⟨t, hrun, hready', heffect⟩ := step.advances hready
    (instruction_codeIn hcode hmem) hpre (fun he ↦ hb (he ▸ hnext))
  exact ⟨t, hrun, hready', heffect.codeIn (Effect.Avoids.of_noMem hnoMem _) hcode,
    heffect⟩

theorem scalar_model_advance [Bindings] {v : Variant} {boundary : ReturnBoundary}
    {s model : RamState} {p : BitVec 64} {bytes : List UInt8}
    {pre : RamState → Prop} {effect : RamState → Effect} {components : List Component}
    (step : StepEffect pre (codeRange p bytes) effect)
    (image : (p, bytes) ∈ instructionBytes v)
    (full : ∀ t, ∀ w ∈ (effect t).writes, w.Full)
    (localWrites : ∀ a b, Obs a b → (effect a).writes = (effect b).writes)
    (frame : ∀ c ∈ (effect s).components, c ∈ components)
    (nomem : ∀ c ∈ components, ∀ x, ¬ c.Covers x)
    (next : InProgram (effect s).rip)
    (ready : ReadyToStep s) (loaded : CodeIn Extracted.programImage s)
    (hb : ¬ InProgram boundary.rip) (hp : pre s) (obs : Obs model s) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      (effect s).Holds s t ∧ Obs (applyWrites model (effect model).writes) t ∧
      AgreesExcept components s t := by
  obtain ⟨t, ht, hr, hl, he⟩ := scalar_advance step image ready loaded hp
    (fun c hc ↦ nomem c (frame c hc)) next hb
  refine ⟨t, ht, hr, hl, he, ?_, he.agrees.mono frame⟩
  rw [localWrites model s obs]
  exact he.obs obs (full s)

theorem saveCursor [Bindings] (v : Variant) (offset : Nat)
    (hoffset : offset = 0x48 ∨ offset = 0x60) {boundary : ReturnBoundary}
    (hb : ¬ InProgram boundary.rip) {s : RamState}
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hip : s.RIP = v.updateAddress + BitVec.ofNat 64 offset)
    (hm : MemReadable s (s.regValue .rsp) 8)
    (ha : ∀ i < 8, ¬ (InProgram (s.regValue .rsp + BitVec.ofNat 64 i) ∨
      InPageTables (s.regValue .rsp + BitVec.ofNat 64 i))) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = v.updateAddress + BitVec.ofNat 64 offset + 4#64 ∧
      (Operand.mem (s.regValue .rsp) : Operand 64).read t = s.regValue .rdi ∧
      AgreesExcept [.mem (s.regValue .rsp) 8, .rip] s t := by
  let am : AddrMode := .sib 4 none 0 .none
  have hstep := mov_m64_r64_effect_step_of_readable
    (v.updateAddress + BitVec.ofNat 64 offset) 0x48
    (by unfold RexWPrefix; decide +kernel) 7 am (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hcode : CodeIn (codeRange (v.updateAddress + BitVec.ofNat 64 offset)
      (0x48 :: 0x89 :: am.modrm 7 :: am.tail)) s := by
    apply instruction_codeIn (v := v) hc
    rcases hoffset with rfl | rfl <;> cases v <;> decide +kernel
  have haddr : storeAddrAt (v.updateAddress + BitVec.ofNat 64 offset) am (3 + am.tail.length) s = s.regValue .rsp := by
    change s.regValue .rsp + 0#64 = s.regValue .rsp
    exact BitVec.add_zero _
  have hpre : StorePreReadable (v.updateAddress + BitVec.ofNat 64 offset)
      (storeAddrAt (v.updateAddress + BitVec.ofNat 64 offset) am (3 + am.tail.length)) 8 s := by
    refine ⟨⟨hip, ?_⟩, ?_⟩
    · simpa only [haddr] using hm
    · simpa only [haddr] using (fun i hi hpage ↦ ha i hi (Or.inr hpage))
  obtain ⟨t, ht, rt, he⟩ := hstep.advances hr hcode hpre (by
    change v.updateAddress + BitVec.ofNat 64 offset + 4#64 ≠ boundary.rip
    intro heq
    apply hb (heq ▸ ?_)
    rw [BitVec.add_assoc]
    change InProgram (v.updateAddress + (BitVec.ofNat 64 offset + BitVec.ofNat 64 4))
    rw [← BitVec.ofNat_add]
    exact offset_inProgram v (offset + 4) (by rcases hoffset with rfl | rfl <;> decide))
  have hf : AgreesExcept [.mem (s.regValue .rsp) 8, .rip] s t := by
    simpa only [movM64R64Effect_components, haddr] using he.agrees
  have hv : (Operand.mem (s.regValue .rsp) : Operand 64).read t = s.regValue .rdi := by
    have hv := he.writes
    change (Operand.mem (storeAddrAt (v.updateAddress + BitVec.ofNat 64 offset) am (3 + am.tail.length) s) : Operand 64).read t = s.regValue .rdi at hv
    simpa only [haddr] using hv
  refine ⟨t, ht, rt, he.codeIn ?_ hc, he.rip, hv, hf⟩
  intro x hx c hcm hcover
  simp only [movM64R64Effect_components, haddr] at hcm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcm
  rcases hcm with rfl | rfl
  · obtain ⟨i, hi, heq⟩ := hcover
    exact ha i hi (Or.inl (heq ▸ ⟨x.2, hx⟩))
  · exact hcover.elim

theorem zero_cursor [Bindings] (v : Variant) (boundary : ReturnBoundary)
    (hb : ¬ InProgram boundary.rip) (s : RamState)
    (hready : ReadyToStep s) (hcode : CodeIn Extracted.programImage s)
    (hm : MemReadable s (s.regValue .rsp) 8)
    (havoid : ∀ i < 8, ¬ (InProgram (s.regValue .rsp + BitVec.ofNat 64 i) ∨
      InPageTables (s.regValue .rsp + BitVec.ofNat 64 i)))
    (hip : s.RIP = partialAddress v) (hcursor : (Operand.reg 0 : Operand 64).read s = 0) :
    ∃ t, Advances boundary 5 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = divisionAddress v ∧
      (Operand.reg 12 : Operand 64).read t = (Operand.reg 1 : Operand 64).read s ∧
      (Operand.mem (s.regValue .rsp) : Operand 64).read t = s.regValue .rdi ∧
      AgreesExcept [.mem (s.regValue .rsp) 8, .reg 12, .flags, .rip] s t := by
  obtain ⟨s1, a1, r1, c1, e1⟩ := scalar_advance (v := v)
    (effect := testR64R64Effect (v.updateAddress + 0x14#64) 0#5 0#5)
    (test_r64_r64_effect_step (v.updateAddress + 0x14#64) 0x48 0xc0
      (by unfold RexWPrefix; decide) (by decide))
    (by cases v <;> decide +kernel) hready hcode hip
    (by simp [Component.Covers])
    (by simpa only [testR64R64Effect, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSignExtend, BitVec.ofNat_eq_ofNat] using
      offset_inProgram v 0x17 (by decide)) hb
  have hz : condHolds 4#4 (StatusFlags.ofRFLAGS s1.RFLAGS) = true := by
    have h := e1.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS s1.RFLAGS).ZF =
      (((Operand.reg 0 : Operand 64).read s &&& (Operand.reg 0 : Operand 64).read s) == 0) at h
    change (StatusFlags.ofRFLAGS s1.RFLAGS).ZF = true
    simpa only [hcursor, BitVec.and_self, beq_self_eq_true] using h
  have htarget : branchTarget (v.updateAddress + 0x17#64) 2
      (BitVec.signExtend 64 0x2f#8) = v.updateAddress + 0x48#64 := by
    simp only [branchTarget, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSignExtend]
  obtain ⟨s2, a2, r2, c2, e2⟩ := scalar_advance (v := v)
    (jcc_rel8_effect_step (v.updateAddress + 0x17#64) 4#4 0x2f#8)
    (by cases v <;> decide +kernel) r1 c1
    ⟨by simpa only [testR64R64Effect, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSignExtend, BitVec.ofNat_eq_ofNat] using e1.rip,
      fun _ ↦ by rw [htarget]; cases v <;> decide⟩
    (by simp [jccEffect, Component.Covers])
    (by simpa only [jccEffect, branchEffect, hz, ↓reduceIte, htarget] using
      offset_inProgram v 0x48 (by decide)) hb
  have ip2 : s2.RIP = v.updateAddress + 0x48#64 := by
    simpa only [jccEffect, branchEffect, hz, ↓reduceIte, htarget] using e2.rip
  have f12 := e1.agrees.trans e2.agrees
  have hrsp : s2.regValue .rsp = s.regValue .rsp :=
    f12.read (n := 64) (r := 4) (by simp [testR64R64Effect_components, jccEffect, branchEffect_components])
  have hrdi : s2.regValue .rdi = s.regValue .rdi :=
    f12.read (n := 64) (r := 7) (by simp [testR64R64Effect_components, jccEffect, branchEffect_components])
  obtain ⟨s2', aSave, rSave, cSave, ipSave, slotSave, fSave⟩ :=
    saveCursor v 0x48 (Or.inl rfl) hb r2 c2 ip2
      (by rw [hrsp]; exact ⟨hm.low, fun i hi ↦ f12.grow _ (hm.mem i hi)⟩)
      (by simpa only [hrsp] using havoid)
  obtain ⟨s3, a3, r3, c3, e3⟩ := scalar_advance (v := v)
    (effect := movR64R64Effect (v.updateAddress + 0x4c#64) 12#5 1#5)
    (mov_r64_r64_effect_step (v.updateAddress + 0x4c#64) 0x49 0xcc
      (by unfold RexWPrefix; decide) (by decide))
    (by cases v <;> decide +kernel) rSave cSave
    (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using ipSave)
    (by simp [Component.Covers])
    (by simpa only [movR64R64Effect, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSignExtend, BitVec.ofNat_eq_ofNat] using
      offset_inProgram v 0x4f (by decide)) hb
  have htarget' : branchTarget (v.updateAddress + 0x4f#64) 5
      (BitVec.signExtend 64 0x98#32) = divisionAddress v := by
    simp only [branchTarget, divisionAddress, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSignExtend, BitVec.ofNat_eq_ofNat]
  obtain ⟨t, a4, r4, c4, e4⟩ := scalar_advance (v := v)
    (jmp_rel32_effect_step (v.updateAddress + 0x4f#64) 0x98#32
      (by rw [htarget']; cases v <;> decide))
    (by cases v <;> decide +kernel) r3 c3
    (by simpa only [movR64R64Effect, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSignExtend, BitVec.ofNat_eq_ofNat] using e3.rip)
    (by simp [Component.Covers])
    (by simpa only [jmpEffect, htarget', divisionAddress, BitVec.ofNat_eq_ofNat] using
      offset_inProgram v 0xec (by decide)) hb
  refine ⟨t, (((a1.trans a2).trans aSave).trans a3).trans a4, r4, c4,
    e4.rip.trans htarget', ?_, ?_, ?_⟩
  · have hreg : (Operand.reg 12 : Operand 64).read s3 =
        (Operand.reg 1 : Operand 64).read s2' := e3.writes
    rw [e4.agrees.read (by simp), hreg, fSave.read (by simp), e2.agrees.read (by simp [jccEffect]),
      e1.agrees.read (by simp)]
  · have hex := (e3.agrees.trans e4.agrees).external (by
      simp [movR64R64Effect_components, jmpEffect_components, Component.Covers])
    have hs : (Operand.mem (s2.regValue .rsp) : Operand 64).read t =
        (Operand.mem (s2.regValue .rsp) : Operand 64).read s2' := by
      apply memLoad_congr
      intro j hj
      rw [hex]
    rw [hrsp, hrdi] at slotSave
    rw [hrsp] at hs
    exact hs.trans slotSave
  · have fSave' : AgreesExcept [.mem (s.regValue .rsp) 8, .rip] s2 s2' := by
      simpa only [hrsp] using fSave
    apply ((((e1.agrees.trans e2.agrees).trans fSave').trans e3.agrees).trans e4.agrees).mono
    simp only [testR64R64Effect_components, jccEffect, branchEffect_components,
      movR64R64Effect_components, jmpEffect_components]
    intro c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with ((((rfl | rfl) | rfl) | rfl | rfl) | rfl | rfl) | rfl <;> simp

end Sha3.Proofs.Update.Partial
