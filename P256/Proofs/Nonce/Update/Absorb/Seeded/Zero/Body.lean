import P256.Proofs.Program.Copy.Body

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Absorb.Seeded.Zero

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Program.Copy

theorem middle [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (code : CodeIn Extracted.programSections.toCodeMap s)
    (outside : ¬ InProgram boundary.rip) (rip : s.RIP = 0x11c949)
    (count : s.regValue .rdx = 0#64) (head : s.regValue .r8 = 0#64) :
    ∃ t, Advances boundary 3 s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programSections.toCodeMap t ∧ t.RIP = 0x11c953 ∧
      t.regValue .rdx = 0#64 ∧ rcx.read t = 0#64 ∧
      AgreesExcept [.reg 2, .reg 1, .flags, .rip] s t := by
  obtain ⟨u, runU, readyU, effectU⟩ :=
    (sub_r64_r64_effect_step 0x11c949 0x4c 0xc2 (by simp [RexWPrefix]) rfl).advances ready
      (programText_slice code 0x1c949 _ (by decide) (by decide +kernel)) rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x1c94c (by decide)))
  change (subR64R64Effect 0x11c949 2 8 s).Holds s u at effectU
  have codeU := effectU.codeIn
    (Effect.Avoids.of_noMem (by simp [subR64R64Effect, Effect.components, Component.Covers]) _) code
  have countU : u.regValue .rdx = 0#64 := by
    have h : u.regValue .rdx = s.regValue .rdx - s.regValue .r8 := effectU.writes
    simpa only [count, head, BitVec.sub_self] using h
  obtain ⟨v, runV, readyV, effectV⟩ :=
    (mov_r64_r64_effect_step 0x11c94c 0x48 0xd1 (by simp [RexWPrefix]) rfl).advances readyU
      (programText_slice codeU 0x1c94c _ (by decide) (by decide +kernel)) effectU.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x1c94f (by decide)))
  change (movR64R64Effect 0x11c94c 1 2 u).Holds u v at effectV
  have codeV := effectV.codeIn
    (Effect.Avoids.of_noMem (by simp [movR64R64Effect_components, Component.Covers]) _) codeU
  have counterV : rcx.read v = 0#64 := effectV.writes.trans countU
  obtain ⟨t, runT, readyT, effectT⟩ :=
    (shr_r64_imm8_effect_step 0x11c94f 0x48 0xe9 3
      (by simp [RexWPrefix]) rfl rfl).advances readyV
      (programText_slice codeV 0x1c94f _ (by decide) (by decide +kernel)) effectV.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x1c953 (by decide)))
  change (shrR64Effect 0x11c94f 4 1 3 v).Holds v t at effectT
  have codeT := effectT.codeIn
    (Effect.Avoids.of_noMem (by simp [shrR64Effect_components, Component.Covers]) _) codeV
  refine ⟨t, (runU.trans runV).trans runT, readyT, codeT, effectT.rip, ?_, ?_, ?_⟩
  · exact (effectT.agrees.read (n := 64) (r := 2) (by simp)).trans
      ((effectV.agrees.read (n := 64) (r := 2) (by simp)).trans countU)
  · have h : rcx.read t = rcx.read v >>> 3 := effectT.writes
    simpa only [counterV, BitVec.zero_ushiftRight] using h
  · exact ((effectU.agrees.trans effectV.agrees).trans effectT.agrees).mono (by
      simp [subR64R64Effect, movR64R64Effect, shrR64Effect, Effect.components])

theorem tail [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (code : CodeIn Extracted.programSections.toCodeMap s)
    (outside : ¬ InProgram boundary.rip) (rip : s.RIP = 0x11c956)
    (count : s.regValue .rdx = 0#64) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programSections.toCodeMap t ∧ t.RIP = 0x11c95c ∧
      rcx.read t = 0#64 ∧ AgreesExcept [.reg 2, .reg 1, .flags, .rip] s t := by
  obtain ⟨u, runU, readyU, effectU⟩ :=
    (and_r32_imm8_effect_step 0x11c956 0xe2 7 rfl rfl).advances ready
      (programText_slice code 0x1c956 _ (by decide) (by decide +kernel)) rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x1c959 (by decide)))
  change (andR32Imm8Effect 0x11c956 3 2 7 s).Holds s u at effectU
  have codeU := effectU.codeIn
    (Effect.Avoids.of_noMem (by simp [andR32Imm8Effect, Effect.components, Component.Covers]) _) code
  have countU : u.regValue .rdx = 0#64 := by
    have h : u.regValue .rdx = ((s.regValue .rdx).setWidth 32 &&& (7#32)).setWidth 64 := effectU.writes
    simpa only [count, BitVec.setWidth_zero, BitVec.zero_and] using h
  obtain ⟨t, runT, readyT, effectT⟩ :=
    (mov_r64_r64_effect_step 0x11c959 0x48 0xd1 (by simp [RexWPrefix]) rfl).advances readyU
      (programText_slice codeU 0x1c959 _ (by decide) (by decide +kernel)) effectU.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x1c95c (by decide)))
  change (movR64R64Effect 0x11c959 1 2 u).Holds u t at effectT
  have codeT := effectT.codeIn
    (Effect.Avoids.of_noMem (by simp [movR64R64Effect_components, Component.Covers]) _) codeU
  refine ⟨t, runU.trans runT, readyT, codeT, effectT.rip, effectT.writes.trans countU, ?_⟩
  exact (effectU.agrees.trans effectT.agrees).mono (by
    simp [andR32Imm8Effect, movR64R64Effect, Effect.components])

end P256.Proofs.Nonce.Update.Absorb.Seeded.Zero
