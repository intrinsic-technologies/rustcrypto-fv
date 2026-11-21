import P256.Proofs.Program.Compare.Tail.Control
import P256.Proofs.Program.Compare.Tail.Compare
import P256.Proofs.Program.Compare.Tail.Byte

namespace P256.Proofs.Program.Compare.Tail

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Spec.Program P256.Spec.Program.Routines

def eightDispatchEffect (s : RamState) : Effect :=
  { eightCompareEffect s with
    rip := if (Operand.mem (eightLeft s) : Operand 64).read s =
        (Operand.mem (eightRight s) : Operand 64).read s
      then 0x11cd61 else 0x11ce0e }

set_option maxRecDepth 2048 in
theorem eight_dispatch [Bindings] :
    RegisterBlock EightComparePre Extracted.programSections.toCodeMap eightDispatchEffect := by
  intro boundary s hReady hCode hPre hBoundary
  have hc : CodeIn (codeRange 0x11cd50 eightCompareBytes) s :=
    program_text_slice hCode 0x1cd50 11 (by decide +kernel)
  obtain ⟨na, u, ha, hu, _, he, hsp⟩ :=
    eight_compare boundary s hReady hc hPre hBoundary
  have hcu : CodeIn Extracted.programSections.toCodeMap u :=
    he.codeIn (Effect.Avoids.of_noMem (by simp [eightCompareEffect, Effect.components,
      Write.component, Operand.component, Component.Covers]) _) hCode
  have hb := hBoundary.of_stack_eq hsp
  have hcb : CodeIn (codeRange 0x11cd5b (0x0f :: jccOpcode32 5 :: immBytes 32 0xad)) u :=
    program_text_slice hcu 0x1cd5b 6 (by decide +kernel)
  obtain ⟨nb, t, hbRun, ht, _, hf, hsp'⟩ :=
    branch32 0x11cd5b 5 0xad (by unfold InRoutine; decide +kernel) (by unfold InRoutine; decide +kernel)
      boundary u hu hcb he.rip hb
  have hct : CodeIn Extracted.programSections.toCodeMap t :=
    hf.codeIn (branchEffect_avoids _ _ _ _) hcu
  refine ⟨na + nb, t, ha.trans hbRun, ht, hct, ?_, hsp'.trans hsp⟩
  have hz := he.flags.2.2.2.1
  change (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
    (((Operand.mem (eightLeft s) : Operand 64).read s - (Operand.mem (eightRight s) : Operand 64).read s) == 0) at hz
  apply holds_after_rip he (by simpa only [jccEffect, branchEffect_components] using hf.agrees)
  · rw [hf.rip]
    by_cases heq : (Operand.mem (eightLeft s) : Operand 64).read s = (Operand.mem (eightRight s) : Operand 64).read s
    · simp [jccEffect, branchEffect, condHolds, hz,
        heq]
    · simp [jccEffect, branchEffect, condHolds, branchTarget, hz,
        heq, BitVec.sub_eq_iff_eq_add]
  · simp [eightCompareEffect, Write.Full, Operand.Full]


def fourDispatchEffect (s : RamState) : Effect :=
  { fourCompareEffect s with
    rip := if (Operand.mem (fourLeft s) : Operand 32).read s =
        (Operand.mem (fourRight s) : Operand 32).read s
      then 0x11cda0 else 0x11ce4d }

set_option maxRecDepth 2048 in
theorem four_dispatch [Bindings] :
    RegisterBlock FourComparePre Extracted.programSections.toCodeMap fourDispatchEffect := by
  intro boundary s hReady hCode hPre hBoundary
  have hc : CodeIn (codeRange 0x11cd90 fourCompareBytes) s :=
    program_text_slice hCode 0x1cd90 10 (by decide +kernel)
  obtain ⟨na, u, ha, hu, _, he, hsp⟩ :=
    four_compare boundary s hReady hc hPre hBoundary
  have hcu : CodeIn Extracted.programSections.toCodeMap u :=
    he.codeIn (Effect.Avoids.of_noMem (by simp [fourCompareEffect, Effect.components,
      Write.component, Operand.component, Component.Covers]) _) hCode
  have hb := hBoundary.of_stack_eq hsp
  have hcb : CodeIn (codeRange 0x11cd9a (0x0f :: jccOpcode32 5 :: immBytes 32 0xad)) u :=
    program_text_slice hcu 0x1cd9a 6 (by decide +kernel)
  obtain ⟨nb, t, hbRun, ht, _, hf, hsp'⟩ :=
    branch32 0x11cd9a 5 0xad (by unfold InRoutine; decide +kernel) (by unfold InRoutine; decide +kernel)
      boundary u hu hcb he.rip hb
  have hct : CodeIn Extracted.programSections.toCodeMap t :=
    hf.codeIn (branchEffect_avoids _ _ _ _) hcu
  refine ⟨na + nb, t, ha.trans hbRun, ht, hct, ?_, hsp'.trans hsp⟩
  have hz := he.flags.2.2.2.1
  change (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
    (((Operand.mem (fourLeft s) : Operand 32).read s - (Operand.mem (fourRight s) : Operand 32).read s) == 0) at hz
  apply holds_after_rip he (by simpa only [jccEffect, branchEffect_components] using hf.agrees)
  · rw [hf.rip]
    by_cases heq : (Operand.mem (fourLeft s) : Operand 32).read s = (Operand.mem (fourRight s) : Operand 32).read s
    · simp [jccEffect, branchEffect, condHolds, hz,
        heq]
    · simp [jccEffect, branchEffect, condHolds, branchTarget, hz,
        heq, BitVec.sub_eq_iff_eq_add]
  · simp [fourCompareEffect, Write.Full, Operand.Full]


def byteDispatchEffect (s : RamState) : Effect :=
  { byteCompareEffect s with
    rip := if lastByteLeft s = lastByteRight s
      then 0x11ce9e else 0x11ce09 }

set_option maxRecDepth 2048 in
theorem byte_dispatch [Bindings] :
    RegisterBlock ByteComparePre Extracted.programSections.toCodeMap byteDispatchEffect := by
  intro boundary s hReady hCode hPre hBoundary
  have hc : CodeIn (codeRange 0x11cdfb byteCompareBytes) s :=
    program_text_slice hCode 0x1cdfb 8 (by decide +kernel)
  obtain ⟨na, u, ha, hu, _, he, hsp⟩ :=
    byte_compare boundary s hReady hc hPre hBoundary
  have hcu : CodeIn Extracted.programSections.toCodeMap u :=
    he.codeIn (Effect.Avoids.of_noMem (by simp [byteCompareEffect, Effect.components,
      Write.component, Operand.component, Component.Covers]) _) hCode
  have hb := hBoundary.of_stack_eq hsp
  have hcb : CodeIn (codeRange 0x11ce03 (0x0f :: jccOpcode32 4 :: immBytes 32 0x95)) u :=
    program_text_slice hcu 0x1ce03 6 (by decide +kernel)
  obtain ⟨nb, t, hbRun, ht, _, hf, hsp'⟩ :=
    branch32 0x11ce03 4 0x95 (by unfold InRoutine; decide +kernel) (by unfold InRoutine; decide +kernel)
      boundary u hu hcb he.rip hb
  have hct : CodeIn Extracted.programSections.toCodeMap t :=
    hf.codeIn (branchEffect_avoids _ _ _ _) hcu
  refine ⟨na + nb, t, ha.trans hbRun, ht, hct, ?_, hsp'.trans hsp⟩
  have hz := he.flags.2.2.2.1
  change (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
    ((lastByteLeft s - lastByteRight s) == 0) at hz
  apply holds_after_rip he (by simpa only [jccEffect, branchEffect_components] using hf.agrees)
  · rw [hf.rip]
    by_cases heq : lastByteLeft s = lastByteRight s
    · simp [jccEffect, branchEffect, condHolds, branchTarget, hz,
        heq]
    · simp [jccEffect, branchEffect, condHolds, hz,
        heq, BitVec.sub_eq_iff_eq_add]
  · simp [byteCompareEffect, Write.Full, Operand.Full]


end P256.Proofs.Program.Compare.Tail
