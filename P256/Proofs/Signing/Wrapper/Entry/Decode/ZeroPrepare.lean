import P256.Proofs.Signing.Wrapper.Entry.Decode.Block

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Entry.Decode

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program Prelude
open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions

abbrev ZeroPreparePre := BlockPre 0x10256a [] [(280,8),(288,8),(296,8),(304,8),(200,8),(192,8),(184,8),(176,8)]

def zeroPrepareBytes : List UInt8 :=
  [72, 137, 172, 36, 24, 1, 0, 0, 76, 137, 180, 36, 32, 1, 0, 0, 72, 137, 156, 36, 40, 1, 0, 0, 76, 137, 188, 36, 48, 1, 0, 0, 72, 199, 132, 36, 200, 0, 0, 0, 0, 0, 0, 0, 72, 199, 132, 36, 192, 0, 0, 0, 0, 0, 0, 0, 72, 199, 132, 36, 184, 0, 0, 0, 0, 0, 0, 0, 72, 199, 132, 36, 176, 0, 0, 0, 0, 0, 0, 0]

def zeroPrepareEffect (s : RamState) : Effect :=
  { rip := 0x1025ba
    writes := [⟨(.mem (stackPtr s + 280) : Operand 64), (Operand.reg 5 : Operand 64).read s⟩,
      ⟨(.mem (stackPtr s + 288) : Operand 64), (Operand.reg 14 : Operand 64).read s⟩,
      ⟨(.mem (stackPtr s + 296) : Operand 64), (Operand.reg 3 : Operand 64).read s⟩,
      ⟨(.mem (stackPtr s + 304) : Operand 64), (Operand.reg 15 : Operand 64).read s⟩,
      ⟨(.mem (stackPtr s + 200) : Operand 64), 0x0⟩,
      ⟨(.mem (stackPtr s + 192) : Operand 64), 0x0⟩,
      ⟨(.mem (stackPtr s + 184) : Operand 64), 0x0⟩,
      ⟨(.mem (stackPtr s + 176) : Operand 64), 0x0⟩] }

theorem zeroPrepare_correct [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary ZeroPreparePre (codeRange 0x10256a zeroPrepareBytes)
      (Effect.post zeroPrepareEffect) := by
  advance_begin (CrossPageStore.mov_m64_r64_effect_step_any 0x10256a 0x48 (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d32 280)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    refine ⟨h.rip,?_,?_⟩
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using h.writable (280,8) (by simp)
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using h.codeApart (280,8) (by simp) 0x256a 8 (by decide)
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm [stackPtr]
    simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using h.codeApart (280,8) (by simp) 0x256a 80 (by decide)
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0x2572 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x102572 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 288)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10256a zeroPrepareBytes 8 8
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_,?_,?_⟩
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.writable (288,8) (by simp)
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.codeApart (288,8) (by simp) 0x2572 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.codeApart (288,8) (by simp) 0x256a 80 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x257a (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x10257a 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d32 296)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10256a zeroPrepareBytes 16 8
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_,?_,?_⟩
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.writable (296,8) (by simp)
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.codeApart (296,8) (by simp) 0x257a 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.codeApart (296,8) (by simp) 0x256a 80 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2582 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x102582 0x4c (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 304)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10256a zeroPrepareBytes 24 8
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_,?_,?_⟩
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.writable (304,8) (by simp)
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.codeApart (304,8) (by simp) 0x2582 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.codeApart (304,8) (by simp) 0x256a 80 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x258a (by decide))
  advance_then (CrossPageStore.mov_m64_imm32_effect_step_any 0x10258a 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 200)) (by decide +kernel) rfl rfl 0x0)
  case sub => exact codeRange_slice_subset 0x10256a zeroPrepareBytes 32 12
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_,?_,?_⟩
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.writable (200,8) (by simp)
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.codeApart (200,8) (by simp) 0x258a 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.codeApart (200,8) (by simp) 0x256a 80 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2596 (by decide))
  advance_then (CrossPageStore.mov_m64_imm32_effect_step_any 0x102596 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 192)) (by decide +kernel) rfl rfl 0x0)
  case sub => exact codeRange_slice_subset 0x10256a zeroPrepareBytes 44 12
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_,?_,?_⟩
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.writable (192,8) (by simp)
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.codeApart (192,8) (by simp) 0x2596 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.codeApart (192,8) (by simp) 0x256a 80 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x25a2 (by decide))
  advance_then (CrossPageStore.mov_m64_imm32_effect_step_any 0x1025a2 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 184)) (by decide +kernel) rfl rfl 0x0)
  case sub => exact codeRange_slice_subset 0x10256a zeroPrepareBytes 56 12
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_,?_,?_⟩
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.writable (184,8) (by simp)
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.codeApart (184,8) (by simp) 0x25a2 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.codeApart (184,8) (by simp) 0x256a 80 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x25ae (by decide))
  advance_then (CrossPageStore.mov_m64_imm32_effect_step_any 0x1025ae 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 176)) (by decide +kernel) rfl rfl 0x0)
  case sub => exact codeRange_slice_subset 0x10256a zeroPrepareBytes 68 12
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_,?_,?_⟩
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.writable (176,8) (by simp)
    · x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.codeApart (176,8) (by simp) 0x25ae 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      simpa only [Extracted.textAddress,BitVec.reduceAdd,BitVec.add_zero,BitVec.ofNat_eq_ofNat,stackPtr,Operand.read_reg64] using hP.codeApart (176,8) (by simp) 0x256a 80 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x25ba (by decide))
  have reg0 : gprNumber (0#1) (rexR (UInt8.toBitVec 76)) 7 = 15#5 := by decide +kernel
  have reg1 : gprNumber (0#1) (rexR (UInt8.toBitVec 76)) 6 = 14#5 := by decide +kernel
  have reg2 : gprNumber (0#1) (rexR (UInt8.toBitVec 72)) 3 = 3#5 := by decide +kernel
  have reg3 : gprNumber (0#1) (rexR (UInt8.toBitVec 72)) 5 = 5#5 := by decide +kernel
  apply AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · x86_norm [BitVec.ofNat_eq_ofNat,reg0,reg1,reg2,reg3,zeroPrepareEffect,stackPtr,BitVec.add_zero,Operand.read_reg64,State.regValue,Syntax.Reg.fin,gprIndex]
  · x86_norm [BitVec.ofNat_eq_ofNat,reg0,reg1,reg2,reg3,zeroPrepareEffect,stackPtr,BitVec.add_zero,Operand.read_reg64,State.regValue,Syntax.Reg.fin,gprIndex]
    exact ⟨rfl,rfl,rfl,rfl⟩
  · intro i
    cases i <;> x86_norm [BitVec.ofNat_eq_ofNat,reg0,reg1,reg2,reg3,zeroPrepareEffect,stackPtr,BitVec.add_zero,Operand.read_reg64,State.regValue,Syntax.Reg.fin,gprIndex]
  · x86_norm [BitVec.ofNat_eq_ofNat,reg0,reg1,reg2,reg3,zeroPrepareEffect,stackPtr,BitVec.add_zero,Operand.read_reg64,State.regValue,Syntax.Reg.fin,gprIndex]


end P256.Proofs.Signing.Wrapper.Entry.Decode
