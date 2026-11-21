import Sha1.Proofs.Entry.UpdateFinalize.Iteration.Transport
import Sha1.Proofs.Buffered.Finalize.Geometry
import X86Proofs.Instructions.Inc.Generated.R.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Branch.Triple

namespace Sha1.Proofs.Entry.UpdateFinalize

open Sha1.Spec Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Buffered Sha1.Proofs.Streaming.UpdateFinalize
open Sha1.Proofs.Buffered.Finalize (text_address_ne_return)
open Sha1.Proofs.Compress.Machine (program_text_slice)

private theorem increment_compare [Bindings] {boundary : ReturnBoundary}
    {pc : BitVec 64} {s : RamState} (hReady : ReadyToStep s)
    (hIncCode : CodeIn (codeRange pc [0x49, 0xff, 0xc7]) s)
    (hCmpCode : CodeIn (codeRange (pc + 3#64) [0x4d, 0x39, 0xfc]) s)
    (hRip : s.RIP = pc) (hIncCont : pc + 3#64 ≠ boundary.rip)
    (hCmpCont : pc + 6#64 ≠ boundary.rip) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ t.RIP = pc + 6#64 ∧
      t.regValue .r15 = s.regValue .r15 + 1 ∧
      (StatusFlags.ofRFLAGS t.RFLAGS).ZF = (s.regValue .r12 == s.regValue .r15 + 1) ∧
      AgreesExcept [.reg 15, .flags, .rip] s t := by
  have hInc : StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0xff, 0xc7]) (incR64Effect pc 15) :=
    inc_r64_effect_step pc 0x49 0xc7 (by unfold RexWPrefix; decide) (by decide) (by decide)
  have hCmp : StepEffect (fun s ↦ s.RIP = pc + 3#64)
      (codeRange (pc + 3#64) [0x4d, 0x39, 0xfc]) (cmpR64R64Effect (pc + 3#64) 12 15) :=
    cmp_r64_r64_effect_step (pc + 3#64) 0x4d 0xfc (by unfold RexWPrefix; decide) (by decide)
  have hNext : pc + 3#64 + 3#64 = pc + 6#64 := by rw [BitVec.add_assoc]; rfl
  obtain ⟨u, hIncRun, huReady, hu⟩ := hInc.advances hReady hIncCode hRip hIncCont
  obtain ⟨t, hCmpRun, htReady, ht⟩ := hCmp.advances (boundary := boundary) huReady
    (hu.codeIn (incR64Effect_avoids _ _ _ _) hCmpCode) hu.rip
    (by change pc + 3#64 + 3#64 ≠ boundary.rip; rwa [hNext])
  have hIdx : u.regValue .r15 = s.regValue .r15 + 1 := hu.writes
  have hCount : u.regValue .r12 = s.regValue .r12 :=
    hu.agrees.read (n := 64) (r := 12) (by rw [incR64Effect_components]; decide)
  refine ⟨t, hIncRun.trans hCmpRun, htReady, ht.rip.trans hNext, ?_, ?_, ?_⟩
  · have hKeep := ht.agrees.read (n := 64) (r := 15) (by rw [cmpR64R64Effect_components]; decide)
    exact hKeep.trans hIdx
  · have hz : (StatusFlags.ofRFLAGS t.RFLAGS).ZF =
        ((u.regValue .r12 - u.regValue .r15) == 0#64) := ht.flags.2.2.2.1
    rw [hz, hCount, hIdx]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, BitVec.sub_eq_iff_eq_add, BitVec.zero_add]
  · apply (hu.agrees.trans ht.agrees).mono
    intro c hc
    simp only [incR64Effect_components, cmpR64R64Effect_components, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    exact hc.elim id Or.inr

theorem loop_latch [bindings : Bindings] {initial : RamState} {inputs : Array Slices.Input}
    {i : Nat} {s : RamState} (hi : i < inputs.size) (hcount : inputs.size < 2^29)
    (hOutside : ¬ InProgram (returnBoundary initial).rip) (h : Frame initial s)
    (hAbs : Absorbed (stackPtr s + 0xd8) (Slices.message (inputs.extract 0 (i+1))) s)
    (hrip : s.RIP ∈ UpdateKind.updateFinalize.exits)
    (hidx : s.regValue .r15 = BitVec.ofNat 64 i) (hsize : s.regValue .r12 = BitVec.ofNat 64 inputs.size) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ Header initial inputs (i+1) t := by
  have hEntry : s.RIP = 0x101cd1 ∨ s.RIP = 0x101daf := by
    simpa only [UpdateKind.exits, List.mem_cons, List.not_mem_nil, or_false] using hrip
  have hInstructions :
      CodeIn (codeRange s.RIP [0x49, 0xff, 0xc7]) s ∧
      CodeIn (codeRange (BitVec.add s.RIP 3#64) [0x4d, 0x39, 0xfc]) s ∧
      BitVec.add s.RIP 3#64 ≠ (returnBoundary initial).rip ∧
      BitVec.add s.RIP 6#64 ≠ (returnBoundary initial).rip := by
    rcases hEntry with hp | hp
    · rw [hp]
      exact ⟨program_text_slice h.code 0x1cd1 3 (by decide +kernel),
        program_text_slice h.code 0x1cd4 3 (by decide +kernel),
        text_address_ne_return hOutside 0x1cd4 (by decide +kernel),
        text_address_ne_return hOutside 0x1cd7 (by decide +kernel)⟩
    · rw [hp]
      exact ⟨program_text_slice h.code 0x1daf 3 (by decide +kernel),
        program_text_slice h.code 0x1db2 3 (by decide +kernel),
        text_address_ne_return hOutside 0x1db2 (by decide +kernel),
        text_address_ne_return hOutside 0x1db5 (by decide +kernel)⟩
  obtain ⟨hIncCode, hCmpCode, hIncCont, hCmpCont⟩ := hInstructions
  obtain ⟨u, hRun, huReady, huRip, huIdx, huZero, huAgrees⟩ :=
    increment_compare h.ready hIncCode hCmpCode rfl hIncCont hCmpCont
  have hNextIdx : u.regValue .r15 = BitVec.ofNat 64 (i + 1) := by
    rw [huIdx, hidx, BitVec.ofNat_add]
    rfl
  have hZero : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = decide (¬ i + 1 < inputs.size) := by
    rw [huZero, hsize, huIdx.symm.trans hNextIdx]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show inputs.size < 2^64 by omega),
      Nat.mod_eq_of_lt (show i + 1 < 2^64 by omega)]
    omega
  have huCode := huAgrees.codeIn (by simp [Component.Covers]) h.code
  have finish {fuel : Nat} {t : RamState} (hRun' : Advances (returnBoundary initial) fuel u t)
      (htReady : ReadyToStep t) (htRip : t.RIP = if i + 1 < inputs.size then 0x101cdd else 0x101dcb)
      (htAgrees : AgreesExcept [.rip] u t) :
      ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ Header initial inputs (i + 1) t := by
    have hag := huAgrees.trans htAgrees
    have hsp : stackPtr t = stackPtr s := hag.read (n := 64) (r := 4) (by decide)
    have hm := hag.external (by simp [Component.Covers])
    have hdf : DirectionFlagUnset t := ⟨(hag.df (by decide)).trans h.df.df⟩
    refine ⟨_, t, hRun.trans hRun', readOnly_frame h htReady (h.code.of_external_eq hm)
      hdf hsp hm hag.rest, ?_, htRip, fun _ ↦ ⟨?_, ?_⟩⟩
    · rw [hsp]
      exact readOnly_absorbed hAbs hm
    · exact (htAgrees.read (n := 64) (r := 15) (by decide)).trans hNextIdx
    · exact (hag.read (n := 64) (r := 12) (by decide)).trans hsize
  rcases hEntry with hp | hp
  · have hNext : (jccEffect 0x101cd7 6 4 ((0xee#32).signExtend 64) u).rip =
        if i + 1 < inputs.size then 0x101cdd else 0x101dcb := by
      simp only [jccEffect, branchEffect, condHolds_4, hZero, decide_eq_true_eq, ite_not]
      rfl
    have hCont : (jccEffect 0x101cd7 6 4 ((0xee#32).signExtend 64) u).rip ≠
        (returnBoundary initial).rip := by
      rw [hNext]
      split
      · exact text_address_ne_return hOutside 0x1cdd (by decide +kernel)
      · exact text_address_ne_return hOutside 0x1dcb (by decide +kernel)
    obtain ⟨t, hBranch, htReady, ht⟩ := (jcc_rel32_effect_step 0x101cd7 4 0xee).advances
      huReady (program_text_slice huCode 0x1cd7 6 (by decide +kernel))
      ⟨by rw [huRip, hp]; rfl, fun _ ↦ by decide +kernel⟩ hCont
    exact finish hBranch htReady (ht.rip.trans hNext) ht.agrees
  · have hNext : (jccEffect 0x101db5 6 5 ((0xffffff22#32).signExtend 64) u).rip =
        if i + 1 < inputs.size then 0x101cdd else 0x101dbb := by
      simp only [jccEffect, branchEffect, condHolds_5, hZero, decide_not,
        Bool.not_not, decide_eq_true_eq]
      rfl
    have hCont : (jccEffect 0x101db5 6 5 ((0xffffff22#32).signExtend 64) u).rip ≠
        (returnBoundary initial).rip := by
      rw [hNext]
      split
      · exact text_address_ne_return hOutside 0x1cdd (by decide +kernel)
      · exact text_address_ne_return hOutside 0x1dbb (by decide +kernel)
    obtain ⟨v, hBranch, hvReady, hv⟩ := (jcc_rel32_effect_step 0x101db5 5 0xffffff22).advances
      huReady (program_text_slice huCode 0x1db5 6 (by decide +kernel))
      ⟨by rw [huRip, hp]; rfl, fun _ ↦ by decide +kernel⟩ hCont
    have hvAgrees : AgreesExcept [.rip] u v := hv.agrees
    by_cases hlt : i + 1 < inputs.size
    · apply finish hBranch hvReady _ hvAgrees
      simpa only [ite_eq_left hlt] using hv.rip.trans hNext
    · have hvRip : v.RIP = 0x101dbb := (hv.rip.trans hNext).trans (ite_eq_right hlt)
      have hvCode := hvAgrees.codeIn (by simp [Component.Covers]) huCode
      obtain ⟨t, hJump, htReady, ht⟩ := (jmp_rel8_effect_step 0x101dbb 0x0e
        (by decide +kernel)).advances hvReady
          (program_text_slice hvCode 0x1dbb 2 (by decide +kernel)) hvRip
          (text_address_ne_return hOutside 0x1dcb (by decide +kernel))
      refine finish (hBranch.trans hJump) htReady ?_ ((hvAgrees.trans ht.agrees).mono ?_)
      · exact ht.rip.trans (ite_eq_right hlt).symm
      · simp

end Sha1.Proofs.Entry.UpdateFinalize
