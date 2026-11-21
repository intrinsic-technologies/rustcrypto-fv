import ChaCha20Poly1305.Proofs.MemoryRoutines.Memcpy.Preparation
import ChaCha20Poly1305.Proofs.MemoryRoutines.Register.Compose
import ChaCha20Poly1305.Proofs.MemoryRoutines.Register.Cmov
import ChaCha20Poly1305.Proofs.MemoryRoutines.Code

namespace ChaCha20Poly1305.Proofs.MemoryRoutines

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.MemoryRoutines.Machine
open ChaCha20Poly1305.Proofs.MemoryRoutines.Register

def memcpyAlignmentBytes : List UInt8 :=
  [0x48, 0x89, 0xf8, 0x41, 0x89, 0xc0, 0x41, 0xf7, 0xd8, 0x41, 0x83, 0xe0, 0x07,
    0x4c, 0x39, 0xc2]

def memcpyAlignmentEffect (s : RamState) : Effect :=
  let a := ((-(rdi.read s).setWidth 32) &&& (7 : BitVec 32)).setWidth 64
  { rip := 0x102dd0
    writes := [⟨rax, rdi.read s⟩, ⟨r8, a⟩]
    flags := some (.ofStatusFlags (cmpSpec (rdx.read s) a)) }

theorem memcpy_alignment_prepare [Bindings] (boundary : ReturnBoundary)
    (hout : boundary.rip.toNat < 0x102dc0 ∨ 0x102def ≤ boundary.rip.toNat) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x102dc0)
      (codeRange 0x102dc0 memcpyAlignmentBytes) memcpyAlignmentEffect := by
  have hne (pc : BitVec 64) (hl : 0x102dc0 ≤ pc.toNat) (hu : pc.toNat < 0x102def) :
      pc ≠ boundary.rip := by intro he; subst pc; omega
  unfold memcpyAlignmentBytes
  routine_run_begin mov_r64_r64_effect_step 0x102dc0 0x48 0xf8
    (by unfold RexWPrefix; decide) (by decide)
  case boundary => intro _ _; exact hne 0x102dc3 (by decide) (by decide)
  routine_run_then mov_r32_r32_rex_effect_step 0x102dc3 0x41 0xc0
    (by unfold RexNoWPrefix; decide) (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x102dc0) (all := memcpyAlignmentBytes)
      3 (by decide +kernel)
  case boundary => intro _ _; exact hne 0x102dc6 (by decide) (by decide)
  routine_run_then neg_r8d_effect_step 0x102dc6
  case sub =>
    exact codeRange_mem_of_drop (p := 0x102dc0) (all := memcpyAlignmentBytes)
      6 (by decide +kernel)
  case boundary => intro _ _; exact hne 0x102dc9 (by decide) (by decide)
  routine_run_then and_r32_imm8_rex_effect_step 0x102dc9 0x41 0xe0 7
    (by unfold RexNoWPrefix; decide) (by decide) (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x102dc0) (all := memcpyAlignmentBytes)
      9 (by decide +kernel)
  case boundary => intro _ _; exact hne 0x102dcd (by decide) (by decide)
  routine_run_then cmp_r64_r64_effect_step 0x102dcd 0x4c 0xc2
    (by unfold RexWPrefix; decide) (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x102dc0) (all := memcpyAlignmentBytes)
      13 (by decide +kernel)
  case boundary => intro _ _; exact hne 0x102dd0 (by decide) (by decide)
  apply AdvancesBlock.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [memcpyAlignmentEffect]
  · x86_norm [memcpyAlignmentEffect, r8]
    simp [Operand.read, gprNumber, rexR, modrmReg]
  · intro i; cases i <;> x86_norm [memcpyAlignmentEffect, rdx, r8]
    all_goals simp [Operand.read, gprNumber, rexB, rexR, modrmRm, modrmReg]
  · x86_norm [memcpyAlignmentEffect, rdx, r8]

def memcpyHeadEffect (s : RamState) : Effect :=
  let n := BitVec.ofNat 64 (alignmentPrefix (rdi.read s) (rdx.read s).toNat)
  { rip := 0x102dd7
    writes := [⟨rax, rdi.read s⟩, ⟨r8, n⟩, ⟨rcx, n⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem memcpy_head_prepare [Bindings] (boundary : ReturnBoundary)
    (hout : boundary.rip.toNat < 0x102dc0 ∨ 0x102def ≤ boundary.rip.toNat) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x102dc0)
      ChaCha20Poly1305.Spec.Program.Extracted.programImage memcpyHeadEffect := by
  intro s hs hc hrip
  have hne (pc : BitVec 64) (hl : 0x102dc0 ≤ pc.toNat) (hu : pc.toNat < 0x102def) :
      pc ≠ boundary.rip := by intro he; subst pc; omega
  have hca : CodeIn (codeRange 0x102dc0 memcpyAlignmentBytes) s :=
    (memcpy_code hc).mono (codeRange_mem_of_take (by decide +kernel))
  obtain ⟨na, u, ha, hu, _, hea⟩ := memcpy_alignment_prepare boundary hout s hs hca hrip
  have hcu : CodeIn ChaCha20Poly1305.Spec.Program.Extracted.programImage u := hea.agrees.codeIn (by
    simp [memcpyAlignmentEffect, Effect.components, Component.Covers, r8]) hc
  have hcm : CodeIn (codeRange 0x102dd0 [0x4c, 0x0f, 0x42, 0xc2]) u :=
    program_text_slice hcu 0x2dd0 4 (by decide +kernel)
  obtain ⟨v, hb, hv, heb⟩ := (cmovb_r8_rdx_effect_step 0x102dd0).advances hu hcm hea.rip
    (hne 0x102dd4 (by decide) (by decide))
  have hcv := heb.codeIn (cmovbR64R64Effect_avoids _ _ _ _ _) hcu
  have hrdx : rdx.read u = rdx.read s := hea.agrees.read (by
    simp [memcpyAlignmentEffect, Effect.components, r8])
  have hcf := hea.flags.1
  change (StatusFlags.ofRFLAGS u.RFLAGS).CF =
    decide ((rdx.read s).toNat <
      (((-(rdi.read s).setWidth 32) &&& (7 : BitVec 32)).setWidth 64).toNat) at hcf
  have hr8 : r8.read v =
      BitVec.ofNat 64 (alignmentPrefix (rdi.read s) (rdx.read s).toNat) := by
    have hb8 := heb.writes
    change r8.read v = (if (StatusFlags.ofRFLAGS u.RFLAGS).CF then rdx.read u else r8.read u) at hb8
    rw [hcf, hrdx, hea.writes.2, select_min_toNat] at hb8
    simpa only [alignmentPrefix, BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)] using hb8
  have hmv : CodeIn (codeRange 0x102dd4 [0x4c, 0x89, 0xc1]) v :=
    program_text_slice hcv 0x2dd4 3 (by decide +kernel)
  have hMove : StepEffect (fun u ↦ u.RIP = 0x102dd4)
      (codeRange 0x102dd4 [0x4c, 0x89, 0xc1]) (movR64R64Effect 0x102dd4 1 8) :=
    mov_r64_r64_effect_step 0x102dd4 0x4c 0xc1 (by unfold RexWPrefix; decide) (by decide)
  obtain ⟨t, hd, ht, hed⟩ := hMove.advances hv hmv heb.rip
    (hne 0x102dd7 (by decide) (by decide))
  refine ⟨na + 1 + 1, t, (ha.trans hb).trans hd, ht,
    hed.codeIn (Effect.avoids_of_components_reg_rip rfl _) hcv, ?_⟩
  refine ⟨hed.rip, ?_, by trivial, ?_⟩
  · change rax.read t = rdi.read s ∧ r8.read t = _ ∧ rcx.read t = _
    refine ⟨?_, ?_, ?_⟩
    · exact (hed.agrees.read (by simp)).trans
        ((heb.agrees.read (by simp [cmovbR64R64Effect_components])).trans hea.writes.1)
    · exact (hed.agrees.read (by simp)).trans hr8
    · exact hed.writes.trans hr8
  · apply ((hea.agrees.trans heb.agrees).trans hed.agrees).mono
    simp [memcpyAlignmentEffect, cmovbR64R64Effect, movR64R64Effect, memcpyHeadEffect,
      Effect.components, r8, rdx, rax, rcx]

end ChaCha20Poly1305.Proofs.MemoryRoutines
