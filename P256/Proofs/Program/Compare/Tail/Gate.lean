import P256.Proofs.Program.Compare.Tail.Prepare
import P256.Proofs.Program.Compare.Tail.Control

namespace P256.Proofs.Program.Compare.Tail

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Spec.Program P256.Spec.Program.Routines

def eightGateEffect (s : RamState) : Effect :=
  { eightPrepareEffect s with
    rip := if maskedLength s 24 == 0 then 0x11cd70 else 0x11cd40 }

theorem eight_gate [Bindings] :
    RegisterBlock (fun s ↦ s.RIP = 0x11cd30) Extracted.programSections.toCodeMap eightGateEffect := by
  intro boundary s hReady hCode hPre hBoundary
  have hc : CodeIn (codeRange 0x11cd30 eightPrepareBytes) s :=
    program_text_slice hCode 0x1cd30 14 (by decide +kernel)
  obtain ⟨na, u, ha, hu, _, he, hsp⟩ :=
    eight_prepare boundary s hReady hc hPre hBoundary
  have hcu : CodeIn Extracted.programSections.toCodeMap u :=
    he.codeIn (Effect.Avoids.of_noMem (by simp [eightPrepareEffect, Effect.components,
      Write.component, Operand.component, Component.Covers]) _) hCode
  have hcb : CodeIn (codeRange 0x11cd3e (jccOpcode8 4 :: immBytes 8 0x30)) u :=
    program_text_slice hcu 0x1cd3e 2 (by decide +kernel)
  obtain ⟨nb, t, hb, ht, _, hf, hsp'⟩ :=
    branch8 0x11cd3e 4 0x30 (by unfold InRoutine; decide +kernel)
      (by unfold InRoutine; decide +kernel) boundary u hu hcb he.rip
      (hBoundary.of_stack_eq hsp)
  have hct : CodeIn Extracted.programSections.toCodeMap t :=
    hf.codeIn (branchEffect_avoids _ _ _ _) hcu
  refine ⟨na + nb, t, ha.trans hb, ht, hct, ?_, hsp'.trans hsp⟩
  have hz : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = (maskedLength s 24 == 0) :=
    he.flags.2.2.2.1
  apply holds_after_rip he (by simpa only [jccEffect, branchEffect_components] using hf.agrees)
  · rw [hf.rip]
    change (if (StatusFlags.ofRFLAGS u.RFLAGS).ZF then 0x11cd70 else 0x11cd40) = _
    rw [hz]
  · simp [eightPrepareEffect, Write.Full, Operand.Full]

def fourGateEffect (s : RamState) : Effect :=
  { fourPrepareEffect s with
    rip := if maskedLength s 4 == 0 then 0x11cdaf else 0x11cd80 }

theorem four_gate [Bindings] :
    RegisterBlock (fun s ↦ s.RIP = 0x11cd70) Extracted.programSections.toCodeMap fourGateEffect := by
  intro boundary s hReady hCode hPre hBoundary
  have hc : CodeIn (codeRange 0x11cd70 fourPrepareBytes) s :=
    program_text_slice hCode 0x1cd70 14 (by decide +kernel)
  obtain ⟨na, u, ha, hu, _, he, hsp⟩ :=
    four_prepare boundary s hReady hc hPre hBoundary
  have hcu : CodeIn Extracted.programSections.toCodeMap u :=
    he.codeIn (Effect.Avoids.of_noMem (by simp [fourPrepareEffect, Effect.components,
      Write.component, Operand.component, Component.Covers]) _) hCode
  have hcb : CodeIn (codeRange 0x11cd7e (jccOpcode8 4 :: immBytes 8 0x2f)) u :=
    program_text_slice hcu 0x1cd7e 2 (by decide +kernel)
  obtain ⟨nb, t, hb, ht, _, hf, hsp'⟩ :=
    branch8 0x11cd7e 4 0x2f (by unfold InRoutine; decide +kernel)
      (by unfold InRoutine; decide +kernel) boundary u hu hcb he.rip
      (hBoundary.of_stack_eq hsp)
  have hct : CodeIn Extracted.programSections.toCodeMap t :=
    hf.codeIn (branchEffect_avoids _ _ _ _) hcu
  refine ⟨na + nb, t, ha.trans hb, ht, hct, ?_, hsp'.trans hsp⟩
  have hz : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = (maskedLength s 4 == 0) :=
    he.flags.2.2.2.1
  apply holds_after_rip he (by simpa only [jccEffect, branchEffect_components] using hf.agrees)
  · rw [hf.rip]
    change (if (StatusFlags.ofRFLAGS u.RFLAGS).ZF then 0x11cdaf else 0x11cd80) = _
    rw [hz]
  · simp [fourPrepareEffect, Write.Full, Operand.Full]

def twoGateEffect (s : RamState) : Effect :=
  { twoPrepareEffect s with
    rip := if ((Operand.reg 1 : Operand 32).read s &&& 2) == 0 then 0x11cdf0 else 0x11cdb8 }

theorem two_gate [Bindings] :
    RegisterBlock (fun s ↦ s.RIP = 0x11cdaf) Extracted.programSections.toCodeMap twoGateEffect := by
  intro boundary s hReady hCode hPre hBoundary
  have hc : CodeIn (codeRange 0x11cdaf twoPrepareBytes) s :=
    program_text_slice hCode 0x1cdaf 7 (by decide +kernel)
  obtain ⟨na, u, ha, hu, _, he, hsp⟩ :=
    two_prepare boundary s hReady hc hPre hBoundary
  have hcu : CodeIn Extracted.programSections.toCodeMap u :=
    he.codeIn (Effect.Avoids.of_noMem (by simp [twoPrepareEffect, Effect.components,
      Write.component, Operand.component, Component.Covers]) _) hCode
  have hcb : CodeIn (codeRange 0x11cdb6 (jccOpcode8 4 :: immBytes 8 0x38)) u :=
    program_text_slice hcu 0x1cdb6 2 (by decide +kernel)
  obtain ⟨nb, t, hb, ht, _, hf, hsp'⟩ :=
    branch8 0x11cdb6 4 0x38 (by unfold InRoutine; decide +kernel)
      (by unfold InRoutine; decide +kernel) boundary u hu hcb he.rip
      (hBoundary.of_stack_eq hsp)
  have hct : CodeIn Extracted.programSections.toCodeMap t :=
    hf.codeIn (branchEffect_avoids _ _ _ _) hcu
  refine ⟨na + nb, t, ha.trans hb, ht, hct, ?_, hsp'.trans hsp⟩
  have hz : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = (((Operand.reg 1 : Operand 32).read s &&& 2) == 0) :=
    he.flags.2.2.2.1
  apply holds_after_rip he (by simpa only [jccEffect, branchEffect_components] using hf.agrees)
  · rw [hf.rip]
    change (if (StatusFlags.ofRFLAGS u.RFLAGS).ZF then 0x11cdf0 else 0x11cdb8) = _
    rw [hz]
  · simp [twoPrepareEffect, Write.Full, Operand.Full]

end P256.Proofs.Program.Compare.Tail
