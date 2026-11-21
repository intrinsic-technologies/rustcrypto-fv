import Base16ct.Proofs.Base16ctUpperDecodeCorrect.Entry
import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Basic
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.Call.Triple
import X86Proofs.Instructions.Test.Generated.R8Imm8.Triple
import X86Proofs.Instructions.Branch.Triple

namespace Base16ct.Proofs.Common

open Base16ct.Spec Base16ct.Spec.Program Base16ct.Spec.Program.Extracted
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Base16ct.Proofs.Base16ctUpperDecodeCorrect

private theorem code_slice {s : RamState} (h : CodeIn programImage s) :
    CodeIn (codeRange (0x100020 : BitVec 64) [0x48, 0x01, 0xf6]) s := by
  have h' := Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.program_text_slice h 0x20 3
    (by decide +kernel)
  have hb : textBytes.toListFrom 0x20 3 = [0x48, 0x01, 0xf6] := by decide +kernel
  simpa only [hb, show textAddress + BitVec.ofNat 64 0x20 = (0x100020 : BitVec 64) by decide +kernel]
    using h'

theorem encoded_len_add_step [bindings : Machine.Bindings]
    {initial : RamState} {boundary : ReturnBoundary}
    (hEntry : EntryReady programImage initial)
    (hRip : initial.RIP = 0x100020)
    (hOutside : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 initial t ∧ ReadyToStep t ∧
      CodeIn programImage t ∧
      (addR64R64Effect initial.RIP 6 6 initial).Holds initial t := by
  have hstep := add_r64_r64_effect_step (p := (0x100020 : BitVec 64))
    (rex := 0x48) (modrm := 0xf6)
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)
  obtain ⟨t, ht, hr, he⟩ := hstep.advances (boundary := boundary) hEntry.ready
    (code_slice hEntry.code) hRip
    (Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.text_address_ne_return hOutside 0x23
      (by decide +kernel))
  refine ⟨t, ht, hr, ?_, ?_⟩
  · exact he.codeIn (addR64R64Effect_avoids _ _ _ initial programImage) hEntry.code
  · simpa [hRip, gprNumber, rexB, rexR, modrmRm, modrmReg] using he

theorem decoded_len_initial_step [bindings : Machine.Bindings]
    {initial : RamState} {boundary : ReturnBoundary}
    (hEntry : EntryReady programImage initial)
    (hRip : initial.RIP = 0x100000)
    (hOutside : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 initial t ∧ ReadyToStep t ∧
      CodeIn programImage t ∧
      (movR32Imm32Effect initial.RIP 5 0 (1#32) initial).Holds initial t := by
  have hstep := mov_r32_imm32_effect_step (p := (0x100000 : BitVec 64))
    (op := 0xb8) (imm := 1#32) (by decide +kernel)
  obtain ⟨t, ht, hr, he⟩ := hstep.advances (boundary := boundary) hEntry.ready
    (by
      have h' := Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.program_text_slice hEntry.code 0x0 5
        (by decide +kernel)
      have hb : textBytes.toListFrom 0x0 5 = (0xb8 :: immBytes 32 (1#32)) := by decide +kernel
      simpa only [hb, show textAddress + BitVec.ofNat 64 0x0 = (0x100000 : BitVec 64) by decide +kernel]
        using h') hRip
    (Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.text_address_ne_return hOutside 0x5
      (by decide +kernel))
  refine ⟨t, ht, hr, ?_, ?_⟩
  · exact he.codeIn (Effect.avoids_of_components_reg_rip
      (movR32Imm32Effect_components _ _ _ _ _) _) hEntry.code
  · simpa [hRip, gprNumber, opcodeReg] using he

theorem decoded_len_test_step [bindings : Machine.Bindings]
    {initial : RamState} {boundary : ReturnBoundary}
    (hEntry : EntryReady programImage initial)
    (hRip : initial.RIP = 0x100005)
    (hOutside : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 initial t ∧ ReadyToStep t ∧
      CodeIn programImage t ∧
      (testR8Imm8Effect initial.RIP (gprNumber 0 (rexB 0x40#8) (modrmRm 0xc6))
        (1#8) initial).Holds initial t := by
  have hs := test_r8_imm8_effect_step (p := (0x100005 : BitVec 64))
    (rex := 0x40) (modrm := 0xc6) (imm := 1#8)
    (by unfold RexPrefix; decide +kernel) (by decide) (by decide)
  rw [hRip]
  apply advanceInProgram hs hEntry.ready hEntry.code
  · decide +kernel
  · exact hRip
  · exact hOutside
  · simp [testR8Imm8Effect]
    exact ⟨0x75, by decide +kernel⟩
  · exact testR8Imm8Effect_avoids _ _ _ _ _

theorem decoded_len_jne_step [bindings : Machine.Bindings]
    {initial : RamState} {boundary : ReturnBoundary}
    (hEntry : EntryReady programImage initial)
    (hRip : initial.RIP = 0x100009)
    (hOutside : ¬ InProgram boundary.rip)
    (hCond : condHolds (5#4) (StatusFlags.ofRFLAGS initial.RFLAGS) = true) :
    ∃ t, Advances boundary 1 initial t ∧ ReadyToStep t ∧
      CodeIn programImage t ∧
      (jccEffect initial.RIP 2 (5#4) ((8#8).signExtend 64) initial).Holds initial t := by
  have hs := jcc_rel8_effect_step (p := (0x100009 : BitVec 64))
    (cc := 5#4) (disp := 8#8)
  rw [hRip]
  apply advanceInProgram hs hEntry.ready hEntry.code
  · decide +kernel
  · refine ⟨hRip, ?_⟩
    intro _
    decide +kernel
  · exact hOutside
  · simp [jccEffect, branchEffect, hCond]
    exact ⟨0xc3, by decide +kernel⟩
  · exact branchEffect_avoids _ _ _ _

theorem decoded_len_jne_not_taken_step [bindings : Machine.Bindings]
    {initial : RamState} {boundary : ReturnBoundary}
    (hEntry : EntryReady programImage initial)
    (hRip : initial.RIP = 0x100009)
    (hOutside : ¬ InProgram boundary.rip)
    (hCond : condHolds (5#4) (StatusFlags.ofRFLAGS initial.RFLAGS) = false) :
    ∃ t, Advances boundary 1 initial t ∧ ReadyToStep t ∧
      CodeIn programImage t ∧
      (jccEffect initial.RIP 2 (5#4) ((8#8).signExtend 64) initial).Holds initial t := by
  have hs := jcc_rel8_effect_step (p := (0x100009 : BitVec 64))
    (cc := 5#4) (disp := 8#8)
  rw [hRip]
  apply advanceInProgram hs hEntry.ready hEntry.code
  · decide +kernel
  · refine ⟨hRip, ?_⟩
    intro _
    decide +kernel
  · exact hOutside
  · simp [jccEffect, branchEffect, hCond]
    exact ⟨0x48, by decide +kernel⟩
  · exact branchEffect_avoids _ _ _ _

theorem decoded_len_shr_step [bindings : Machine.Bindings]
    {initial : RamState} {boundary : ReturnBoundary}
    (hEntry : EntryReady programImage initial)
    (hRip : initial.RIP = 0x10000b)
    (hOutside : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 initial t ∧ ReadyToStep t ∧
      CodeIn programImage t ∧
      (shrR64Effect initial.RIP 3 (gprNumber 0 (rexB 0x48#8) (modrmRm 0xee)) 1 initial).Holds initial t := by
  have hs := shr_r64_one_effect_step (p := (0x10000b : BitVec 64))
    (rex := 0x48) (modrm := 0xee)
    (by unfold RexWPrefix; decide +kernel) (by decide) (by decide)
  rw [hRip]
  apply advanceInProgram hs hEntry.ready hEntry.code
  · decide +kernel
  · exact hRip
  · exact hOutside
  · simp [shrR64Effect]
    exact ⟨0x48, by decide +kernel⟩
  · exact shrR64Effect_avoids _ _ _ _ _ _

theorem decoded_len_xor_step [bindings : Machine.Bindings]
    {initial : RamState} {boundary : ReturnBoundary}
    (hEntry : EntryReady programImage initial)
    (hRip : initial.RIP = 0x100011)
    (hOutside : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 initial t ∧ ReadyToStep t ∧
      CodeIn programImage t ∧
      (xorR32R32Effect initial.RIP 2 0 0 initial).Holds initial t := by
  have hs := xor_r32_r32_effect_step (p := (0x100011 : BitVec 64))
    (modrm := 0xc0) (by decide +kernel)
  rw [hRip]
  apply advanceInProgram hs hEntry.ready hEntry.code
  · decide +kernel
  · exact hRip
  · exact hOutside
  · simp [xorR32R32Effect]
    exact ⟨0xc3, by decide +kernel⟩
  · exact xorR32R32Effect_avoids _ _ _ _ _ _

theorem decoded_len_ret_step [bindings : Machine.Bindings] {initial u : RamState}
    (hReady : ReadyToStep u)
    (hCode : CodeIn (codeRange 0x100013 [0xc3]) u)
    (hPre : RetPre 0x100013 u)
    (hTop : stackTop u = (returnBoundary initial).rip)
    (hRsp : stackPtr u + 8#64 = (returnBoundary initial).rsp) :
    ∃ final, Returns (returnBoundary initial) 1 u final ∧ ReadyToStep final ∧
      AgreesExcept [.reg 4, .rip] u final := by
  obtain ⟨final, hstep, hready, he⟩ := ret_effect_step 0x100013 u hReady hCode hPre
  refine ⟨final, ?_, hready, he.agrees⟩
  apply Returns.of_step hstep
  · exact he.rip.trans hTop
  · have hw := he.writes
    change final.GPR[4] = stackPtr u + 8#64 at hw
    exact hw.trans hRsp

end Base16ct.Proofs.Common
