import Base16ct.Proofs.Base16ctUpperDecodeCorrect.Entry
import Base16ct.Proofs.Base16ctUpperDecodeCorrect.Decoder

namespace Base16ct.Proofs.Base16ctUpperDecodeCorrect.Instructions

variable {alphabet : Base16ct.Proofs.Base16ctUpperDecodeCorrect.RFC4648.Alphabet}
open Base16ct.Spec Base16ct.Spec.Program Base16ct.Spec.Program.Extracted
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

set_option maxRecDepth 100000 in
theorem decode_mov_eax_one [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hentry : EntryReady programImage s) (hp : s.RIP = (decodeAddress alphabet))
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧
      CodeIn programImage t ∧
      (movR32Imm32Effect s.RIP 5 (gprNumber 0 0 (opcodeReg 0xB8)) (1#32) s).Holds s t := by
  have hs := mov_r32_imm32_effect_step (p := s.RIP) (op := 0xB8)
      (imm := 1#32) (by decide)
  apply advanceInProgram hs hentry.ready hentry.code
  · rw [hp]
    cases alphabet <;> decide +kernel
  · rfl
  · exact hret
  · change InProgram (BitVec.add s.RIP (5#64))
    rw [hp]
    exact ⟨0x40, by (cases alphabet <;> decide +kernel)⟩
  · exact Effect.avoids_of_components_reg_rip
      (movR32Imm32Effect_components _ _ _ _ _) _

set_option maxRecDepth 100000 in
theorem decode_test_sil_one [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hentry : EntryReady programImage s) (hp : s.RIP = (decodeAddress alphabet) + 5#64)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧
      CodeIn programImage t ∧
      (testR8Imm8Effect s.RIP (gprNumber 0 (rexB 0x40#8) (modrmRm 0xc6)) (1#8) s).Holds s t := by
  have hs := test_r8_imm8_effect_step (p := s.RIP) (rex := 0x40) (modrm := 0xc6) (imm := 1#8)
      (by unfold RexPrefix; decide) (by decide) (by decide)
  apply advanceInProgram hs hentry.ready hentry.code
  · rw [hp]
    cases alphabet <;> decide +kernel
  · rfl
  · exact hret
  · change InProgram (BitVec.add s.RIP (4#64))
    rw [hp]
    exact ⟨0x0f, by (cases alphabet <;> decide +kernel)⟩
  · exact testR8Imm8Effect_avoids _ _ _ _ _

set_option maxRecDepth 100000 in
theorem decode_jne_after_test [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hentry : EntryReady programImage s) (hp : s.RIP = (decodeAddress alphabet) + 9#64)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧
      CodeIn programImage t ∧
      (jccEffect s.RIP 6 (5#4) ((0xe1#32).signExtend 64) s).Holds s t := by
  have hs := jcc_rel32_effect_step (p := s.RIP) (cc := 5#4) (disp := 0xe1#32)
  apply advanceInProgram hs hentry.ready hentry.code
  · rw [hp]
    cases alphabet <;> decide +kernel
  · constructor
    · rfl
    · intro _
      rw [hp]
      (cases alphabet <;> decide +kernel)
  · exact hret
  · unfold jccEffect branchEffect InProgram
    by_cases hc : condHolds (5#4) (StatusFlags.ofRFLAGS s.RFLAGS) = true
    · rw [hc]
      refine ⟨0xc3, ?_⟩
      rw [hp]
      (cases alphabet <;> decide +kernel)
    · have hc' : condHolds (5#4) (StatusFlags.ofRFLAGS s.RFLAGS) = false := by
        exact (Bool.eq_false_iff).2 hc
      rw [hc']
      refine ⟨0x49, ?_⟩
      rw [hp]
      (cases alphabet <;> decide +kernel)
  · exact branchEffect_avoids _ _ _ _

set_option maxRecDepth 100000 in
theorem decode_mov_r9_rsi [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hentry : EntryReady programImage s) (hp : s.RIP = (decodeAddress alphabet) + 15#64)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn programImage t ∧
      (movR64R64Effect s.RIP (gprNumber 0 (rexB (0x49#8)) (modrmRm 0xf1))
        (gprNumber 0 (rexR (0x49#8)) (modrmReg 0xf1)) s).Holds s t := by
  have hs := mov_r64_r64_effect_step (p := s.RIP) (rex := 0x49) (modrm := 0xf1)
      (by unfold RexWPrefix; decide) (by decide)
  apply advanceInProgram hs hentry.ready hentry.code
  · rw [hp]
    cases alphabet <;> decide +kernel
  · rfl
  · exact hret
  · change InProgram (BitVec.add s.RIP (3#64))
    rw [hp]
    exact ⟨0x49, by (cases alphabet <;> decide +kernel)⟩
  · exact Effect.avoids_of_components_reg_rip (movR64R64Effect_components _ _ _ _) _

set_option maxRecDepth 100000 in
theorem decode_shr_r9_one [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hentry : EntryReady programImage s) (hp : s.RIP = (decodeAddress alphabet) + 18#64)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn programImage t ∧
      (shrR64Effect s.RIP 3 (gprNumber 0 (rexB (0x49#8)) (modrmRm 0xe9)) 1 s).Holds s t := by
  have hs := shr_r64_one_effect_step (p := s.RIP) (rex := 0x49) (modrm := 0xe9)
      (by unfold RexWPrefix; decide) (by decide) (by decide)
  apply advanceInProgram hs hentry.ready hentry.code
  · rw [hp]
    cases alphabet <;> decide +kernel
  · rfl
  · exact hret
  · change InProgram (BitVec.add s.RIP (3#64))
    rw [hp]
    exact ⟨0x4d, by (cases alphabet <;> decide +kernel)⟩
  · exact shrR64Effect_avoids _ _ _ _ _ _

set_option maxRecDepth 100000 in
theorem decode_cmp_r9_r8 [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hentry : EntryReady programImage s) (hp : s.RIP = (decodeAddress alphabet) + 21#64)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn programImage t ∧
      (cmpR64R64Effect s.RIP (gprNumber 0 (rexB (0x4d#8)) (modrmRm 0xc1))
        (gprNumber 0 (rexR (0x4d#8)) (modrmReg 0xc1)) s).Holds s t := by
  have hs := cmp_r64_r64_effect_step (p := s.RIP) (rex := 0x4d) (modrm := 0xc1)
      (by unfold RexWPrefix; decide) (by decide)
  apply advanceInProgram hs hentry.ready hentry.code
  · rw [hp]
    cases alphabet <;> decide +kernel
  · rfl
  · exact hret
  · change InProgram (BitVec.add s.RIP (3#64))
    rw [hp]
    exact ⟨0x0f, by (cases alphabet <;> decide +kernel)⟩
  · exact cmpR64R64Effect_avoids _ _ _ _ _

set_option maxRecDepth 100000 in
theorem decode_ja_after_cmp [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hentry : EntryReady programImage s) (hp : s.RIP = (decodeAddress alphabet) + 24#64)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn programImage t ∧
      (jccEffect s.RIP 6 (7#4) ((0xd2#32).signExtend 64) s).Holds s t := by
  have hs := jcc_rel32_effect_step (p := s.RIP) (cc := 7#4) (disp := 0xd2#32)
  apply advanceInProgram hs hentry.ready hentry.code
  · rw [hp]
    cases alphabet <;> decide +kernel
  · constructor
    · rfl
    · intro _
      rw [hp]
      (cases alphabet <;> decide +kernel)
  · exact hret
  · unfold jccEffect branchEffect InProgram
    by_cases hc : condHolds (7#4) (StatusFlags.ofRFLAGS s.RFLAGS) = true
    · rw [hc]
      refine ⟨0xc3, ?_⟩
      rw [hp]
      (cases alphabet <;> decide +kernel)
    · have hc' : condHolds (7#4) (StatusFlags.ofRFLAGS s.RFLAGS) = false := by
        exact (Bool.eq_false_iff).2 hc
      rw [hc']
      refine ⟨0x48, ?_⟩
      rw [hp]
      (cases alphabet <;> decide +kernel)
  · exact branchEffect_avoids _ _ _ _

set_option maxRecDepth 100000 in
theorem decode_test_rsi_rsi [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hentry : EntryReady programImage s) (hp : s.RIP = (decodeAddress alphabet) + 30#64)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn programImage t ∧
      (testR64R64Effect s.RIP (gprNumber 0 (rexB (0x48#8)) (modrmRm 0xf6))
        (gprNumber 0 (rexR (0x48#8)) (modrmReg 0xf6)) s).Holds s t := by
  have hs := test_r64_r64_effect_step (p := s.RIP) (rex := 0x48) (modrm := 0xf6)
      (by unfold RexWPrefix; decide) (by decide)
  apply advanceInProgram hs hentry.ready hentry.code
  · rw [hp]
    cases alphabet <;> decide +kernel
  · rfl
  · exact hret
  · change InProgram (BitVec.add s.RIP (3#64))
    rw [hp]
    exact ⟨0x0f, by (cases alphabet <;> decide +kernel)⟩
  · exact testR64R64Effect_avoids _ _ _ _ _

set_option maxRecDepth 100000 in
theorem decode_je_empty [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hentry : EntryReady programImage s) (hp : s.RIP = (decodeAddress alphabet) + 33#64)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn programImage t ∧
      (jccEffect s.RIP 6 (4#4) ((0x000000ca#32).signExtend 64) s).Holds s t := by
  have hs := jcc_rel32_effect_step (p := s.RIP) (cc := 4#4) (disp := 0x000000ca#32)
  apply advanceInProgram hs hentry.ready hentry.code
  · rw [hp]
    cases alphabet <;> decide +kernel
  · constructor
    · rfl
    · intro _
      rw [hp]
      (cases alphabet <;> decide +kernel)
  · exact hret
  · unfold jccEffect branchEffect InProgram
    by_cases hc : condHolds (4#4) (StatusFlags.ofRFLAGS s.RFLAGS) = true
    · rw [hc]
      refine ⟨0x48, ?_⟩
      rw [hp]
      (cases alphabet <;> decide +kernel)
    · have hc' : condHolds (4#4) (StatusFlags.ofRFLAGS s.RFLAGS) = false := by
        exact (Bool.eq_false_iff).2 hc
      rw [hc']
      refine ⟨0x55, ?_⟩
      rw [hp]
      (cases alphabet <;> decide +kernel)
  · exact branchEffect_avoids _ _ _ _

set_option maxRecDepth 100000 in
theorem decode_empty_test_rcx [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hentry : EntryReady programImage s) (hp : s.RIP = (decodeAddress alphabet) + 241#64)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn programImage t ∧
      (testR64R64Effect s.RIP (gprNumber 0 (rexB (0x48#8)) (modrmRm 0xc9))
        (gprNumber 0 (rexR (0x48#8)) (modrmReg 0xc9)) s).Holds s t := by
  have hs := test_r64_r64_effect_step (p := s.RIP) (rex := 0x48) (modrm := 0xc9)
      (by unfold RexWPrefix; decide) (by decide)
  apply advanceInProgram hs hentry.ready hentry.code
  · rw [hp]
    cases alphabet <;> decide +kernel
  · rfl
  · exact hret
  · change InProgram (BitVec.add s.RIP (3#64))
    rw [hp]
    exact ⟨0x74, by (cases alphabet <;> decide +kernel)⟩
  · exact testR64R64Effect_avoids _ _ _ _ _

set_option maxRecDepth 100000 in
theorem decode_empty_je_null [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hentry : EntryReady programImage s) (hp : s.RIP = (decodeAddress alphabet) + 244#64)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn programImage t ∧
      (jccEffect s.RIP 2 (4#4) ((0x06#8).signExtend 64) s).Holds s t := by
  have hs := jcc_rel8_effect_step (p := s.RIP) (cc := 4#4) (disp := 0x06#8)
  apply advanceInProgram hs hentry.ready hentry.code
  · rw [hp]
    cases alphabet <;> decide +kernel
  · constructor
    · rfl
    · intro _
      rw [hp]
      (cases alphabet <;> decide +kernel)
  · exact hret
  · unfold jccEffect branchEffect InProgram
    by_cases hc : condHolds (4#4) (StatusFlags.ofRFLAGS s.RFLAGS) = true
    · rw [hc]
      refine ⟨0xb8, ?_⟩
      rw [hp]
      (cases alphabet <;> decide +kernel)
    · have hc' : condHolds (4#4) (StatusFlags.ofRFLAGS s.RFLAGS) = false := by
        exact (Bool.eq_false_iff).2 hc
      rw [hc']
      refine ⟨0x4c, ?_⟩
      rw [hp]
      (cases alphabet <;> decide +kernel)
  · exact branchEffect_avoids _ _ _ _

end Base16ct.Proofs.Base16ctUpperDecodeCorrect.Instructions
