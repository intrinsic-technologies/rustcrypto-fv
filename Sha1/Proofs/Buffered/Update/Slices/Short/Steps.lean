import Sha1.Proofs.Buffered.Update.Slices.BranchState
import Sha1.Proofs.Buffered.Update.SiteCalls
import Sha1.Proofs.Buffered.Finalize.Geometry
import Sha1.Proofs.Buffered.DigestPrepare.Position
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import X86Proofs.Instructions.Add.Generated.R8.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Triple

namespace Sha1.Proofs.Buffered.Update.Slices

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Buffered.Finalize (pageApart_of_avoids rangeApart_text text_address_ne_return)
open Sha1.Proofs.Compress.Machine (program_text_slice)

theorem short_prepare [Bindings] {boundary : ReturnBoundary} {s : RamState}
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hout : ¬ InProgram boundary.rip) (hip : s.RIP = 0x101cb0) :
    ∃ n t, Advances boundary n s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = 0x101cc1 ∧
      rdi.read t = stackPtr s + (Operand.reg 13 : Operand 64).read s + 216 ∧
      rsi.read t = (Operand.reg 14 : Operand 64).read s ∧
      MemoryRoutines.rdx.read t = (Operand.reg 3 : Operand 64).read s ∧
      AgreesExcept [.reg 7, .reg 6, .reg 2, .flags, .rip] s t := by
  have hLea : StepEffect (fun v ↦ v.RIP = 0x101cb0)
      (codeRange 0x101cb0 [0x4a, 0x8d, 0x3c, 0x2c])
      (leaR64Effect 0x101cb0 7 (.sib 4 (some 13) 0 .none)) :=
    lea_r64_effect_step 0x101cb0 0x4a (by unfold RexWPrefix; decide)
      7 (.sib 4 (some 13) 0 .none) (by decide) (by decide) (by decide)
  have hLeaBytes : CodeIn (codeRange 0x101cb0 [0x4a, 0x8d, 0x3c, 0x2c]) s :=
    program_text_slice hc 0x1cb0 4 (by decide +kernel)
  obtain ⟨u, hau, hru, heu⟩ := hLea.advances hr hLeaBytes hip
    (text_address_ne_return hout 0x1cb4 (by decide +kernel))
  have hcu := heu.agrees.codeIn (by simp [Component.Covers]) hc
  have hdiu : rdi.read u = stackPtr s + (Operand.reg 13 : Operand 64).read s := by
    have hw := heu.writes
    change rdi.read u = stackPtr s + ((Operand.reg 13 : Operand 64).read s <<< 0) + 0 at hw
    rw [hw, BitVec.shiftLeft_zero]
    exact BitVec.add_zero _
  have hAdd : StepEffect (fun v ↦ v.RIP = 0x101cb4)
      (codeRange 0x101cb4 [0x48, 0x81, 0xc7, 0xd8, 0, 0, 0])
      (addR64Imm32Effect 0x101cb4 7 216) :=
    add_r64_imm32_effect_step 0x101cb4 0x48 0xc7 216 (by decide) (by decide) (by decide)
  have hAddBytes : CodeIn (codeRange 0x101cb4 [0x48, 0x81, 0xc7, 0xd8, 0, 0, 0]) u :=
    program_text_slice hcu 0x1cb4 7 (by decide +kernel)
  obtain ⟨v, hav, hrv, hev⟩ := hAdd.advances hru hAddBytes heu.rip
    (text_address_ne_return hout 0x1cbb (by decide +kernel))
  have hcv := hev.agrees.codeIn (by simp [Component.Covers]) hcu
  have hdiv : rdi.read v = rdi.read u + 216 := hev.writes
  have hMovSrc : StepEffect (fun v ↦ v.RIP = 0x101cbb)
      (codeRange 0x101cbb [0x4c, 0x89, 0xf6]) (movR64R64Effect 0x101cbb 6 14) :=
    mov_r64_r64_effect_step 0x101cbb 0x4c 0xf6 (by unfold RexWPrefix; decide) (by decide)
  have hSrcBytes : CodeIn (codeRange 0x101cbb [0x4c, 0x89, 0xf6]) v :=
    program_text_slice hcv 0x1cbb 3 (by decide +kernel)
  obtain ⟨w, haw, hrw, hew⟩ := hMovSrc.advances hrv hSrcBytes hev.rip
    (text_address_ne_return hout 0x1cbe (by decide +kernel))
  have hcw := hew.agrees.codeIn (by simp [Component.Covers]) hcv
  have hMovLen : StepEffect (fun v ↦ v.RIP = 0x101cbe)
      (codeRange 0x101cbe [0x48, 0x89, 0xda]) (movR64R64Effect 0x101cbe 2 3) :=
    mov_r64_r64_effect_step 0x101cbe 0x48 0xda (by unfold RexWPrefix; decide) (by decide)
  have hLenBytes : CodeIn (codeRange 0x101cbe [0x48, 0x89, 0xda]) w :=
    program_text_slice hcw 0x1cbe 3 (by decide +kernel)
  obtain ⟨t, hat, hrt, het⟩ := hMovLen.advances hrw hLenBytes hew.rip
    (text_address_ne_return hout 0x1cc1 (by decide +kernel))
  have hct := het.agrees.codeIn (by simp [Component.Covers]) hcw
  have huv := heu.trans hev
  have hvw := huv.trans hew.agrees
  have hvt := hew.trans het
  refine ⟨4, t, ((hau.trans hav).trans haw).trans hat, hrt, hct, het.rip, ?_, ?_, ?_, ?_⟩
  · have hdit : rdi.read t = rdi.read v := hvt.read (by simp)
    rw [hdit, hdiv, hdiu]
  · have hSit : rsi.read t = rsi.read w := het.agrees.read (by simp)
    have hSiw : rsi.read w = (Operand.reg 14 : Operand 64).read v := hew.writes
    exact hSit.trans (hSiw.trans (huv.read (by simp)))
  · have hDx : MemoryRoutines.rdx.read t = (Operand.reg 3 : Operand 64).read w := het.writes
    exact hDx.trans (hvw.read (by simp))
  · exact (huv.trans hvt).mono (by simp)

theorem short_finish [Bindings] {boundary : ReturnBoundary} {s : RamState}
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hout : ¬ InProgram boundary.rip) (hip : s.RIP = 0x101cc7)
    (hw : MemoryRoutines.WritableRange s (stackPtr s + 279) 1) :
    ∃ n t, Advances boundary n s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = 0x101cd1 ∧ (Operand.mem (stackPtr s + 279) : Operand 8).read t =
        (Operand.reg 3 : Operand 8).read s + (Operand.reg 13 : Operand 8).read s ∧
      AgreesExcept [.reg 3, .flags, .rip, .mem (stackPtr s + 279) 1] s t := by
  have hAdd : StepEffect (fun v ↦ v.RIP = 0x101cc7)
      (codeRange 0x101cc7 [0x44, 0x00, 0xeb]) (addR8R8Effect 0x101cc7 3 3 13) :=
    add_r8_r8_rex_effect_step 0x101cc7 0x44 0xeb (by unfold RexPrefix; decide) (by decide)
  have hAddBytes : CodeIn (codeRange 0x101cc7 [0x44, 0x00, 0xeb]) s :=
    program_text_slice hc 0x1cc7 3 (by decide +kernel)
  obtain ⟨u, hau, hru, heu⟩ := hAdd.advances hr hAddBytes hip
    (text_address_ne_return hout 0x1cca (by decide +kernel))
  have hcu := heu.agrees.codeIn (by simp [Component.Covers]) hc
  have hsp : stackPtr u = stackPtr s := heu.agrees.read (n := 64) (r := 4) (by simp)
  have hStore := mov_m8_r8_effect_step 0x101cca 3 (by decide) (.sib 4 none 0 (.d32 279))
    (by decide) (by decide) (by decide)
  change StepEffect (X86Proofs.StorePre 0x101cca 7 (fun v ↦ stackPtr v + 279) 1)
    (codeRange 0x101cca [0x88, 0x9c, 0x24, 0x17, 1, 0, 0])
    (storeEffect 0x101cca 7 (fun v ↦ stackPtr v + 279) ((Operand.reg 3 : Operand 8).read))
    at hStore
  have hStoreBytes : CodeIn (codeRange 0x101cca [0x88, 0x9c, 0x24, 0x17, 1, 0, 0]) u :=
    program_text_slice hcu 0x1cca 7 (by decide +kernel)
  have hPre : X86Proofs.StorePre 0x101cca 7 (fun v ↦ stackPtr v + 279) 1 u := by
    refine ⟨heu.rip, ?_, ?_⟩
    · rw [hsp]
      exact ⟨hw.readable.low, (hw.of_agrees heu.agrees).readable.mem,
        pageApart_of_avoids (by decide) hw.readable.low hw.tables⟩
    · rw [hsp]
      exact rangeApart_text hw.code (by decide +kernel : 0x1cca + 7 ≤ Extracted.textBytes.size)
  obtain ⟨t, hat, hrt, het⟩ := hStore.advances hru hStoreBytes hPre
    (text_address_ne_return hout 0x1cd1 (by decide +kernel))
  have hAvoids : ∀ i < 1, ¬ InProgram (stackPtr u + 279 + BitVec.ofNat 64 i) :=
    hsp.symm ▸ hw.code
  have hct := het.codeIn (DigestPrepare.store_avoids_program (len := 1)
    (storeEffect_components _ _ _ _ _) hAvoids) hcu
  have hBl : (Operand.reg 3 : Operand 8).read u =
      (Operand.reg 3 : Operand 8).read s + (Operand.reg 13 : Operand 8).read s := by
    have hReg := heu.writes
    change (Operand.reg 3 : Operand 64).read u = mergeGPR 8
      ((Operand.reg 3 : Operand 8).read s + (Operand.reg 13 : Operand 8).read s)
      ((Operand.reg 3 : Operand 64).read s) at hReg
    exact (congrArg (BitVec.setWidth 8) hReg).trans (setWidth_mergeGPR8 _ _)
  have hByte : (Operand.mem (stackPtr u + 279) : Operand 8).read t =
      (Operand.reg 3 : Operand 8).read u := het.writes
  have hag : AgreesExcept [.reg 3, .flags, .rip, .mem (stackPtr u + 279) 1] s t :=
    (heu.trans het).mono (by simp)
  rw [hsp] at hByte hag
  exact ⟨2, t, hau.trans hat, hrt, hct, het.rip, hByte.trans hBl, hag⟩

end Sha1.Proofs.Buffered.Update.Slices
