import P256.Proofs.Signing.Wrapper.Entry.Decode.Block

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Entry.Decode

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program Prelude
open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions

abbrev ZeroPre := BlockPre 0x102418 [] [(172,4),(24,8),(16,8),(8,8),(0,8)]

def zeroBytes : List UInt8 :=
  [199, 132, 36, 172, 0, 0, 0, 0, 1, 0, 0, 72, 199, 68, 36, 24, 0, 0, 0, 0, 72, 199, 68, 36, 16, 0, 0, 0, 0, 72, 199, 68, 36, 8, 0, 0, 0, 0, 72, 199, 4, 36, 0, 0, 0, 0]

def zeroEffect (s : RamState) : Effect :=
  { rip := 0x102446
    writes := [⟨(.mem (stackPtr s + 172) : Operand 32), 0x100⟩,
      ⟨(.mem (stackPtr s + 24) : Operand 64), 0x0⟩,
      ⟨(.mem (stackPtr s + 16) : Operand 64), 0x0⟩,
      ⟨(.mem (stackPtr s + 8) : Operand 64), 0x0⟩,
      ⟨(.mem (stackPtr s + 0) : Operand 64), 0x0⟩] }

theorem zero_correct [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary ZeroPre (codeRange 0x102418 zeroBytes)
      (Effect.post zeroEffect) := by
  advance_begin (CrossPageStore.mov_m32_imm32_legacy_effect_step_any 0x102418 (.sib 4 none 0 (.d32 172)) (by decide +kernel) rfl rfl 0x100)
  case pre =>
    intro s h
    refine ⟨h.rip,?_,?_⟩
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using h.writable (172,4) (by simp)
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using h.codeApart (172,4) (by simp) 0x2418 11 (by decide)
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm [stackPtr]
    simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using h.codeApart (172,4) (by simp) 0x2418 46 (by decide)
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0x2423 (by decide))
  advance_then (CrossPageStore.mov_m64_imm32_effect_step_any 0x102423 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl 0x0)
  case sub => exact codeRange_slice_subset 0x102418 zeroBytes 11 9
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_,?_,?_⟩
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.writable (24,8) (by simp)
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.codeApart (24,8) (by simp) 0x2423 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.codeApart (24,8) (by simp) 0x2418 46 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x242c (by decide))
  advance_then (CrossPageStore.mov_m64_imm32_effect_step_any 0x10242c 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl 0x0)
  case sub => exact codeRange_slice_subset 0x102418 zeroBytes 20 9
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_,?_,?_⟩
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.writable (16,8) (by simp)
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.codeApart (16,8) (by simp) 0x242c 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.codeApart (16,8) (by simp) 0x2418 46 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2435 (by decide))
  advance_then (CrossPageStore.mov_m64_imm32_effect_step_any 0x102435 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl 0x0)
  case sub => exact codeRange_slice_subset 0x102418 zeroBytes 29 9
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_,?_,?_⟩
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.writable (8,8) (by simp)
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.codeApart (8,8) (by simp) 0x2435 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.codeApart (8,8) (by simp) 0x2418 46 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x243e (by decide))
  advance_then (CrossPageStore.mov_m64_imm32_effect_step_any 0x10243e 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 .none) (by decide +kernel) rfl rfl 0x0)
  case sub => exact codeRange_slice_subset 0x102418 zeroBytes 38 8
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_,?_,?_⟩
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.writable (0,8) (by simp)
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.codeApart (0,8) (by simp) 0x243e 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.codeApart (0,8) (by simp) 0x2418 46 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2446 (by decide))
  advance_finish [zeroEffect,stackPtr,Operand.read_reg64,State.regValue,BitVec.add_zero]
  all_goals (repeat constructor <;> rfl)

end P256.Proofs.Signing.Wrapper.Entry.Decode
