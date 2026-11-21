import Base16ct.Proofs.EncodeStr.Lower.Machine.Interface
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.NopMem.Triple

namespace Base16ct.Proofs.EncodeStr.Lower

open Base16ct.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def maskBranchEffect (s : RamState) : Effect :=
  { rip := if ((Operand.reg 2 : Operand 64).read s &&& 0x3fffffffffffffff) = 0
      then 0x100521 else 0x1004c7
    writes := [⟨(.reg 8 : Operand 64), 0x3fffffffffffffff⟩,
      ⟨(.reg 2 : Operand 64), (Operand.reg 2 : Operand 64).read s &&& 0x3fffffffffffffff⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem mask_branch_run [Bindings] {boundary : ReturnBoundary}
    (hOutside : ¬ InProgram boundary.rip) {s : RamState}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hRip : s.RIP = 0x1004b8) :
    ∃ t, Advances boundary 3 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      (maskBranchEffect s).Holds s t := by
  have hMovCode : CodeIn (codeRange 0x1004b8
      [0x49, 0xb8, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x3f]) s :=
    program_text_slice hCode 0x4b8 10 (by decide +kernel)
  obtain ⟨a, hRun₁, hReady₁, hMov⟩ :=
    (mov_r64_imm64_effect_step 0x1004b8 0x49 0xb8 (by simp [RexWPrefix])
      (by decide +kernel) 0x3fffffffffffffff).advances
      hReady hMovCode hRip (text_address_ne_return hOutside 0x4c2 (by decide +kernel))
  change (movR64Imm64Effect 0x1004b8 8 0x3fffffffffffffff s).Holds s a at hMov
  have hCode₁ := hMov.agrees.codeIn (by simp [Effect.components, movR64Imm64Effect,
    Component.Covers]) hCode
  have hAndCode : CodeIn (codeRange 0x1004c2 [0x4c, 0x21, 0xc2]) a :=
    program_text_slice hCode₁ 0x4c2 3 (by decide +kernel)
  obtain ⟨b, hRun₂, hReady₂, hAnd⟩ :=
    (and_r64_r64_effect_step 0x1004c2 0x4c 0xc2 (by simp [RexWPrefix]) (by decide)).advances
      hReady₁ hAndCode hMov.rip (text_address_ne_return hOutside 0x4c5 (by decide +kernel))
  change (andR64R64Effect 0x1004c2 2 8 a).Holds a b at hAnd
  have hCode₂ := hAnd.agrees.codeIn (by simp [Component.Covers]) hCode₁
  have hRdx : (Operand.reg 2 : Operand 64).read a = (Operand.reg 2 : Operand 64).read s :=
    hMov.agrees.read (by simp)
  have hR8 : (Operand.reg 8 : Operand 64).read a = 0x3fffffffffffffff := hMov.writes
  have hValue : (Operand.reg 2 : Operand 64).read b =
      (Operand.reg 2 : Operand 64).read s &&& 0x3fffffffffffffff := by
    simpa only [andR64R64Effect, Write.AllHold, hRdx, hR8] using hAnd.writes
  have hZero : (StatusFlags.ofRFLAGS b.RFLAGS).ZF =
      (((Operand.reg 2 : Operand 64).read s &&& 0x3fffffffffffffff) == 0) := by
    simpa only [andR64R64Effect, Effect.FlagsHold, andFlags, StatusFlagsOutcome.Allows,
      FlagAllows, hRdx, hR8] using hAnd.flags.2.2.2.1
  have hNext : (jccEffect 0x1004c5 2 4 ((90#8).signExtend 64) b).rip =
      (maskBranchEffect s).rip := by
    change (if (StatusFlags.ofRFLAGS b.RFLAGS).ZF then 0x100521 else 0x1004c7) = _
    rw [hZero]
    simp only [maskBranchEffect, beq_iff_eq]
  have hBoundary : (maskBranchEffect s).rip ≠ boundary.rip := by
    unfold maskBranchEffect
    split
    · exact text_address_ne_return hOutside 0x521 (by decide +kernel)
    · exact text_address_ne_return hOutside 0x4c7 (by decide +kernel)
  have hJumpCode : CodeIn (codeRange 0x1004c5 [0x74, 0x5a]) b :=
    program_text_slice hCode₂ 0x4c5 2 (by decide +kernel)
  obtain ⟨t, hRun₃, hReady₃, hJump⟩ :=
    (jcc_rel8_effect_step 0x1004c5 4 90).advances hReady₂ hJumpCode
      ⟨hAnd.rip, fun _ => by decide +kernel⟩ (hNext ▸ hBoundary)
  have hAgrees : AgreesExcept [.rip] b t := hJump.agrees
  refine ⟨t, (hRun₁.trans hRun₂).trans hRun₃, hReady₃,
    hAgrees.codeIn (by simp [Component.Covers]) hCode₂, hJump.rip.trans hNext, ?_, ?_, ?_⟩
  · exact ⟨(hAgrees.read (n := 64) (r := 8) (by simp)).trans
      ((hAnd.agrees.read (by simp)).trans hR8),
      (hAgrees.read (n := 64) (r := 2) (by simp)).trans hValue⟩
  · simp [maskBranchEffect, Effect.FlagsHold, StatusFlagsOutcome.Allows, FlagAllows]
  · apply ((hMov.agrees.trans hAnd.agrees).trans hAgrees).mono
    simp [maskBranchEffect, Effect.components, movR64Imm64Effect, andR64R64Effect]

def indexInitEffect : Effect :=
  { rip := 0x1004d0
    writes := [⟨(.reg 8 : Operand 64), 0⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem index_init_run [Bindings] {boundary : ReturnBoundary}
    (hOutside : ¬ InProgram boundary.rip) {s : RamState}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hRip : s.RIP = 0x1004c7) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      indexInitEffect.Holds s t := by
  have hXorCode : CodeIn (codeRange 0x1004c7 [0x45, 0x31, 0xc0]) s :=
    program_text_slice hCode 0x4c7 3 (by decide +kernel)
  obtain ⟨a, hRun₁, hReady₁, hXor⟩ :=
    (xor_r32_r32_rex_effect_step 0x1004c7 0x45 0xc0
      (by unfold RexNoWPrefix; decide +kernel) (by decide)).advances
      hReady hXorCode hRip (text_address_ne_return hOutside 0x4ca (by decide +kernel))
  change (xorR32R32Effect 0x1004c7 3 8 8 s).Holds s a at hXor
  have hCode₁ := hXor.agrees.codeIn (by simp [Component.Covers]) hCode
  have hNopCode : CodeIn (codeRange 0x1004ca [0x66, 0x0f, 0x1f, 0x44, 0, 0]) a :=
    program_text_slice hCode₁ 0x4ca 6 (by decide +kernel)
  obtain ⟨t, hRun₂, hReady₂, hNop⟩ :=
    (nop_m_effect_step 0x1004ca [0x66] (by decide) (by decide)
      (.sib 0 (some 0) 0 (.d8 0)) ⟨by decide, fun h => by cases h⟩ rfl rfl).advances
      hReady₁ hNopCode hXor.rip (text_address_ne_return hOutside 0x4d0 (by decide +kernel))
  change (nopEffect 0x1004ca 6).Holds a t at hNop
  refine ⟨t, hRun₁.trans hRun₂, hReady₂,
    hNop.agrees.codeIn (by simp [Component.Covers]) hCode₁, hNop.rip, ?_, ?_, ?_⟩
  · have hv : (Operand.reg 8 : Operand 64).read a = 0 := by
      simpa [xorR32R32Effect, Write.AllHold] using hXor.writes
    exact (hNop.agrees.read (n := 64) (r := 8) (by simp)).trans hv
  · simp [indexInitEffect, Effect.FlagsHold, StatusFlagsOutcome.Allows, FlagAllows]
  · apply (hXor.agrees.trans hNop.agrees).mono
    simp [indexInitEffect, Effect.components, xorR32R32Effect, nopEffect]

end Base16ct.Proofs.EncodeStr.Lower
