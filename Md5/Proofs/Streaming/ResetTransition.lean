import Md5.Proofs.Block.Entry
import Md5.Proofs.Block.Execution
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Lea.Triple

namespace Md5.Proofs.Streaming

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Block

structure ResetTransitionPost (nonempty : Bool) (s t : RamState) : Prop where
  rip : t.RIP = if nonempty then 0x1009c7 else 0x100a90
  context : nonempty = true → (Operand.reg 3 : Operand 64).read t = stackPtr s + 8
  memcpy : nonempty = true → (Operand.reg 15 : Operand 64).read t = 0x1024b0
  agrees : AgreesExcept [.reg 3, .reg 15, .flags, .rip] s t

theorem ResetTransitionPost.index {nonempty : Bool} {s t : RamState}
    (h : ResetTransitionPost nonempty s t) :
    (Operand.reg 5 : Operand 64).read t = (Operand.reg 5 : Operand 64).read s :=
  h.agrees.read (by simp)

theorem ResetTransitionPost.total {nonempty : Bool} {s t : RamState}
    (h : ResetTransitionPost nonempty s t) :
    (Operand.reg 12 : Operand 64).read t = (Operand.reg 12 : Operand 64).read s :=
  h.agrees.read (by simp)

theorem ResetTransitionPost.rsp {nonempty : Bool} {s t : RamState}
    (h : ResetTransitionPost nonempty s t) : stackPtr t = stackPtr s :=
  h.agrees.read (r := 4) (n := 64) (by simp)

theorem ResetTransitionPost.memory {nonempty : Bool} {s t : RamState}
    (h : ResetTransitionPost nonempty s t) : t.external = s.external :=
  h.agrees.external (by simp [Component.Covers])

def resetTransitionSetupEffect (s : RamState) : Effect where
  rip := 0x1009c7
  writes := [⟨(.reg 3 : Operand 64), stackPtr s + 8⟩,
    ⟨(.reg 15 : Operand 64), 0x1024b0⟩]

theorem reset_transition_setup [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x100992) Extracted.programImage
      resetTransitionSetupEffect := by
  intro s hReady hCode hRip
  have hLeaMemcpy : StepEffect (fun s ↦ s.RIP = 0x100992)
      (codeRange 0x100992 [0x4c, 0x8d, 0x3d, 0x17, 0x1b, 0, 0])
      (leaR64Effect 0x100992 15 (.rip 0x1b17)) :=
    lea_r64_effect_step 0x100992 0x4c (by unfold RexWPrefix; decide)
      7 (.rip 0x1b17) (by decide) (by decide) (by decide)
  obtain ⟨u, hRun₁, hReady₁, hEffect₁⟩ := hLeaMemcpy.advances hReady
    (program_text_slice hCode 0x992 7 (by decide +kernel)) hRip
    (text_address_ne_return hOutside 0x999 (by decide +kernel))
  have hCode₁ := hEffect₁.agrees.codeIn (by simp [Component.Covers]) hCode
  have hLeaContext : StepEffect (fun s ↦ s.RIP = 0x100999)
      (codeRange 0x100999 [0x48, 0x8d, 0x5c, 0x24, 8])
      (leaR64Effect 0x100999 3 (.sib 4 none 0 (.d8 8))) :=
    lea_r64_effect_step 0x100999 0x48 (by unfold RexWPrefix; decide)
      3 (.sib 4 none 0 (.d8 8)) (by decide) (by decide) (by decide)
  obtain ⟨v, hRun₂, hReady₂, hEffect₂⟩ := hLeaContext.advances hReady₁
    (program_text_slice hCode₁ 0x999 5 (by decide +kernel)) hEffect₁.rip
    (text_address_ne_return hOutside 0x99e (by decide +kernel))
  have hCode₂ := hEffect₂.agrees.codeIn (by simp [Component.Covers]) hCode₁
  obtain ⟨t, hRun₃, hReady₃, hEffect₃⟩ :=
    (jmp_rel8_effect_step 0x10099e 0x27 (by decide +kernel)).advances hReady₂
      (program_text_slice hCode₂ 0x99e 2 (by decide +kernel)) hEffect₂.rip
      (text_address_ne_return hOutside 0x9c7 (by decide +kernel))
  have hAgrees : AgreesExcept [.reg 3, .reg 15, .rip] s t :=
    (hEffect₁.agrees.trans (hEffect₂.agrees.trans hEffect₃.agrees)).mono (by simp)
  refine ⟨3, t, hRun₁.trans (hRun₂.trans hRun₃), hReady₃,
    hAgrees.codeIn (by simp [Component.Covers]) hCode,
    ⟨hEffect₃.rip, ⟨?_, ?_⟩, trivial, hAgrees⟩⟩
  · have hContext : (Operand.reg 3 : Operand 64).read v = stackPtr u + 8 := hEffect₂.writes
    have hRsp : stackPtr u = stackPtr s := hEffect₁.agrees.read (r := 4) (n := 64) (by simp)
    exact (hEffect₃.agrees.read (r := 3) (n := 64) (by simp)).trans (hRsp ▸ hContext)
  · have hMemcpy : (Operand.reg 15 : Operand 64).read u = 0x1024b0 := hEffect₁.writes
    exact (hEffect₃.agrees.read (r := 15) (n := 64) (by simp)).trans
      ((hEffect₂.agrees.read (r := 15) (n := 64) (by simp)).trans hMemcpy)

theorem reset_transition [Bindings] {boundary : ReturnBoundary}
    (hOutside : ¬ InProgram boundary.rip) {s : RamState} (hReady : ReadyToStep s)
    (hCode : CodeIn Extracted.programImage s) (hRip : s.RIP = 0x100989) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧
      ResetTransitionPost (decide (((Operand.reg 5 : Operand 64).read s).toNat <
        ((Operand.reg 12 : Operand 64).read s).toNat)) s t := by
  have hCmp : StepEffect (fun s ↦ s.RIP = 0x100989)
      (codeRange 0x100989 [0x4c, 0x39, 0xe5]) (cmpR64R64Effect 0x100989 5 12) :=
    cmp_r64_r64_effect_step 0x100989 0x4c 0xe5
      (by unfold RexWPrefix; decide) (by decide)
  obtain ⟨u, hCmpRun, hCmpReady, hCmpEffect⟩ := hCmp.advances hReady
    (program_text_slice hCode 0x989 3 (by decide +kernel)) hRip
    (text_address_ne_return hOutside 0x98c (by decide +kernel))
  have hCode₁ := hCmpEffect.codeIn (cmpR64R64Effect_avoids _ _ _ _ _) hCode
  have hCarry : (StatusFlags.ofRFLAGS u.RFLAGS).CF =
      decide (((Operand.reg 5 : Operand 64).read s).toNat <
        ((Operand.reg 12 : Operand 64).read s).toNat) := hCmpEffect.flags.1
  have hNext : (jccEffect 0x10098c 6 3 ((0xfe#32).signExtend 64) u).rip =
      if ((Operand.reg 5 : Operand 64).read s).toNat <
          ((Operand.reg 12 : Operand 64).read s).toNat then 0x100992 else 0x100a90 := by
    simp [jccEffect, branchEffect, condHolds, hCarry, branchTarget, -Nat.not_lt]
  have hNe : (jccEffect 0x10098c 6 3 ((0xfe#32).signExtend 64) u).rip ≠ boundary.rip := by
    rw [hNext]
    split
    · exact text_address_ne_return hOutside 0x992 (by decide +kernel)
    · exact text_address_ne_return hOutside 0xa90 (by decide +kernel)
  obtain ⟨v, hBranchRun, hBranchReady, hBranchEffect⟩ :=
    (jcc_rel32_effect_step 0x10098c 3 0xfe).advances hCmpReady
      (program_text_slice hCode₁ 0x98c 6 (by decide +kernel))
      ⟨hCmpEffect.rip, fun _ ↦ by decide +kernel⟩ hNe
  have hBefore : AgreesExcept [.flags, .rip] s v :=
    (hCmpEffect.agrees.trans hBranchEffect.agrees).mono (by simp [jccEffect])
  have hCode₂ := hBefore.codeIn (by simp [Component.Covers]) hCode
  have hPc := hBranchEffect.rip.trans hNext
  by_cases hlt : ((Operand.reg 5 : Operand 64).read s).toNat <
      ((Operand.reg 12 : Operand 64).read s).toNat
  · have hEntry : v.RIP = 0x100992 := by simpa only [ite_eq_left hlt] using hPc
    obtain ⟨fuel, t, hSetupRun, hSetupReady, hSetupCode, hSetupEffect⟩ :=
      reset_transition_setup boundary hOutside v hBranchReady hCode₂ hEntry
    have hRsp : stackPtr v = stackPtr s := hBefore.read (r := 4) (n := 64) (by simp)
    refine ⟨2 + fuel, t, (hCmpRun.trans hBranchRun).trans hSetupRun,
      hSetupReady, hSetupCode, ?_⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [resetTransitionSetupEffect, decide_eq_true hlt, Bool.true_eq, ite_true]
        using hSetupEffect.rip
    · intro _
      exact hRsp ▸ hSetupEffect.writes.1
    · intro _
      exact hSetupEffect.writes.2
    · exact (hBefore.trans hSetupEffect.agrees).mono (by
        simp [resetTransitionSetupEffect, Effect.components])
  · refine ⟨2, v, hCmpRun.trans hBranchRun, hBranchReady, hCode₂, ?_⟩
    refine ⟨?_, ?_, ?_, hBefore.mono (by simp)⟩
    · simpa only [ite_eq_right hlt, decide_eq_false hlt, Bool.false_eq_true, ite_false] using hPc
    · simp only [decide_eq_true_eq]
      exact fun h ↦ (hlt h).elim
    · simp only [decide_eq_true_eq]
      exact fun h ↦ (hlt h).elim

theorem reset_transition_of_indices [Bindings] {boundary : ReturnBoundary}
    (hOutside : ¬ InProgram boundary.rip) {s : RamState} {first total : Nat}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s) (hRip : s.RIP = 0x100989)
    (hFirst : (Operand.reg 5 : Operand 64).read s = BitVec.ofNat 64 first)
    (hTotal : (Operand.reg 12 : Operand 64).read s = BitVec.ofNat 64 total)
    (hle : first ≤ total) (hBound : total < 2^64) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ ResetTransitionPost (decide (first < total)) s t := by
  obtain ⟨fuel, t, hRun, hReady', hCode', hPost⟩ := reset_transition hOutside hReady hCode hRip
  refine ⟨fuel, t, hRun, hReady', hCode', ?_⟩
  simpa only [hFirst, hTotal, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hBound,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hle hBound)] using hPost

end Md5.Proofs.Streaming
