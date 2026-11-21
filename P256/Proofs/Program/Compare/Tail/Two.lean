import P256.Proofs.Program.Compare.Execution
import P256.Proofs.Program.Compare.Model
import P256.Proofs.Program.Compare.WordInstructions.MovzxLoad
import P256.Proofs.Program.Compare.WordInstructions.Cmp
import P256.Proofs.Program.Compare.Tail.Control

namespace P256.Proofs.Program.Compare.Tail

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Spec.Program P256.Spec.Program.Routines WordInstructions

def twoLeft (s : RamState) : BitVec 64 :=
  (Operand.reg 0 : Operand 64).read s + (Operand.reg 11 : Operand 64).read s

def twoRight (s : RamState) : BitVec 64 :=
  (Operand.reg 2 : Operand 64).read s + (Operand.reg 11 : Operand 64).read s

structure TwoComparePre (s : RamState) : Prop where
  rip : s.RIP = 0x11cdd0
  left : MemReadable s (twoLeft s) 2
  right : MemReadable s (twoRight s) 2

def twoCompareBytes : List UInt8 :=
  [0x46, 0x0f, 0xb7, 0x04, 0x18, 0x42, 0x0f, 0xb7, 0x3c, 0x1a, 0x66, 0x41, 0x39, 0xf8]

def twoCompareEffect (s : RamState) : Effect :=
  { rip := 0x11cdde
    writes := [⟨(Operand.reg 8 : Operand 64),
      ((Operand.mem (twoLeft s) : Operand 16).read s).setWidth 64⟩,
      ⟨(Operand.reg 7 : Operand 64),
      ((Operand.mem (twoRight s) : Operand 16).read s).setWidth 64⟩]
    flags := some (.ofStatusFlags (cmpSpec
      ((Operand.mem (twoLeft s) : Operand 16).read s)
      ((Operand.mem (twoRight s) : Operand 16).read s))) }

attribute [local x86_compose] twoLeft twoRight BitVec.shiftLeft_zero BitVec.add_zero

set_option maxRecDepth 2048 in
theorem two_compare [Bindings] :
    RegisterBlock TwoComparePre (codeRange 0x11cdd0 twoCompareBytes)
      twoCompareEffect := by
  unfold twoCompareBytes
  p256_memcmp_run_begin tail_word_left_step
  case pre =>
    intro s hP
    refine ⟨hP.rip, ?_⟩
    x86_norm
    exact hP.left
  p256_memcmp_run_then tail_word_right_step
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11cdd0) (all := twoCompareBytes) 5
      (by decide +kernel)
  try (case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
    · x86_norm
      exact hP.right
    · x86_avoid)
  p256_memcmp_run_then X86Proofs.cmp_r16_r16_rex_effect_step 0x11cdda 0x41 0xf8
    (by unfold RexNoWPrefix; decide) (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11cdd0) (all := twoCompareBytes) 10
      (by decide +kernel)
  p256_memcmp_run_finish [twoCompareEffect, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]

theorem two_compare_zero_iff [Bindings] {s t : RamState}
    (h : (twoCompareEffect s).Holds s t) :
    (StatusFlags.ofRFLAGS t.RFLAGS).ZF = true ↔
      BytesEqual s (twoLeft s) (twoRight s) 2 := by
  have hz := h.flags.2.2.2.1
  change (StatusFlags.ofRFLAGS t.RFLAGS).ZF =
    (((Operand.mem (twoLeft s) : Operand 16).read s -
      (Operand.mem (twoRight s) : Operand 16).read s) == 0) at hz
  rw [hz, beq_iff_eq, BitVec.sub_eq_iff_eq_add]
  simpa using bytesEqual_iff_load.symm

def twoDispatchEffect (s : RamState) : Effect :=
  { twoCompareEffect s with
    rip := if (Operand.mem (twoLeft s) : Operand 16).read s =
        (Operand.mem (twoRight s) : Operand 16).read s
      then 0x11cde4 else 0x11ce78 }

set_option maxRecDepth 2048 in
theorem two_dispatch [Bindings] :
    RegisterBlock TwoComparePre Extracted.programSections.toCodeMap twoDispatchEffect := by
  intro boundary s hReady hCode hPre hBoundary
  have hc : CodeIn (codeRange 0x11cdd0 twoCompareBytes) s :=
    program_text_slice hCode 0x1cdd0 14 (by decide +kernel)
  obtain ⟨na, u, ha, hu, _, he, hsp⟩ :=
    two_compare boundary s hReady hc hPre hBoundary
  have hcu : CodeIn Extracted.programSections.toCodeMap u :=
    he.codeIn (Effect.Avoids.of_noMem (by simp [twoCompareEffect, Effect.components,
      Write.component, Operand.component, Component.Covers]) _) hCode
  have hb := hBoundary.of_stack_eq hsp
  have hcb : CodeIn (codeRange 0x11cdde (0x0f :: jccOpcode32 5 :: immBytes 32 0x94)) u :=
    program_text_slice hcu 0x1cdde 6 (by decide +kernel)
  obtain ⟨nb, t, hbRun, ht, _, hf, hsp'⟩ :=
    branch32 0x11cdde 5 0x94 (by unfold InRoutine; decide +kernel) (by unfold InRoutine; decide +kernel)
      boundary u hu hcb he.rip hb
  have hct : CodeIn Extracted.programSections.toCodeMap t :=
    hf.codeIn (branchEffect_avoids _ _ _ _) hcu
  refine ⟨na + nb, t, ha.trans hbRun, ht, hct, ?_, hsp'.trans hsp⟩
  have hz := he.flags.2.2.2.1
  change (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
    (((Operand.mem (twoLeft s) : Operand 16).read s - (Operand.mem (twoRight s) : Operand 16).read s) == 0) at hz
  apply holds_after_rip he (by simpa only [jccEffect, branchEffect_components] using hf.agrees)
  · rw [hf.rip]
    by_cases heq : (Operand.mem (twoLeft s) : Operand 16).read s = (Operand.mem (twoRight s) : Operand 16).read s
    · simp [jccEffect, branchEffect, condHolds, hz,
        heq]
    · simp [jccEffect, branchEffect, condHolds, branchTarget, hz,
        heq, BitVec.sub_eq_iff_eq_add]
  · simp [twoCompareEffect, Write.Full, Operand.Full]

end P256.Proofs.Program.Compare.Tail
