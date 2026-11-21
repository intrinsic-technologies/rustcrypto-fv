import P256.Proofs.Signing.Wrapper.Entry.Decode.Copy.Support

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Entry.Decode.Copy

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions
open P256.Proofs.Common.Curve.LinearCombination.NafReverse

def bytes : List UInt8 :=
  [15, 182, 72, 2, 136, 140, 36, 82, 1, 0, 0, 15, 183, 8, 102, 137, 140, 36, 80, 1, 0, 0, 139, 72, 3, 72, 139, 80, 7, 72, 137, 148, 36, 87, 1, 0, 0, 72, 139, 80, 15, 72, 137, 148, 36, 95, 1, 0, 0, 72, 139, 80, 23, 72, 137, 148, 36, 103, 1, 0, 0, 15, 182, 64, 31, 136, 132, 36, 111, 1, 0, 0, 137, 140, 36, 83, 1, 0, 0]

def effect (s : RamState) : Effect :=
  { rip := 0x102418
    writes := [
      ⟨(.reg 1 : Operand 64), (memLoad s.external ((Operand.reg 0 : Operand 64).read s + 3)
        32).setWidth 64⟩,
      ⟨(.reg 0 : Operand 64), (memLoad s.external ((Operand.reg 0 : Operand 64).read s + 31)
        8).setWidth 64⟩,
      ⟨(.reg 2 : Operand 64), (memLoad s.external ((Operand.reg 0 : Operand 64).read s + 23)
        64).setWidth 64⟩,
      ⟨(.mem (((Operand.reg 4 : Operand 64).read s + 336) + 2) : Operand 8), memLoad s.external
        ((Operand.reg 0 : Operand 64).read s + 2) 8⟩,
      ⟨(.mem (((Operand.reg 4 : Operand 64).read s + 336) + 0) : Operand 16), memLoad s.external
        ((Operand.reg 0 : Operand 64).read s + 0) 16⟩,
      ⟨(.mem (((Operand.reg 4 : Operand 64).read s + 336) + 7) : Operand 64), memLoad s.external
        ((Operand.reg 0 : Operand 64).read s + 7) 64⟩,
      ⟨(.mem (((Operand.reg 4 : Operand 64).read s + 336) + 15) : Operand 64), memLoad s.external
        ((Operand.reg 0 : Operand 64).read s + 15) 64⟩,
      ⟨(.mem (((Operand.reg 4 : Operand 64).read s + 336) + 23) : Operand 64), memLoad s.external
        ((Operand.reg 0 : Operand 64).read s + 23) 64⟩,
      ⟨(.mem (((Operand.reg 4 : Operand 64).read s + 336) + 31) : Operand 8), memLoad s.external
        ((Operand.reg 0 : Operand 64).read s + 31) 8⟩,
      ⟨(.mem (((Operand.reg 4 : Operand 64).read s + 336) + 3) : Operand 32), memLoad s.external
        ((Operand.reg 0 : Operand 64).read s + 3) 32⟩] }

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip)
    (input : ByteArray) :
    AdvanceTriple boundary (CopyPre input) (codeRange 0x1023c9 bytes) (Effect.post effect) := by
  advance_begin (movzx_r32_m8_effect_step 0x1023c9 1 (.base 0 (.d8 2)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    refine ⟨hP.rip, ?_⟩
    x86_norm
    exact hP.readable 2 1 (by decide)
  case next =>
    intro s hP
    exact boundary_ne_program outside (inProgram_of_textOffset 0x23cd (by decide))
  advance_then (mov_m8_r8_legacy_effect_step 0x1023cd 1 (by decide +kernel) (.sib 4 none 0 (.d32 338))
    (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1023c9 bytes 4 7
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.byteWritable 2 (by decide)
    · x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.codeApart 2 1 (by decide) 0x23cd 7 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.codeApart 2 1 (by decide) 0x23c9 79 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x23d4 (by decide))
  advance_then (movzx_r32_m16_effect_step 0x1023d4 1 (.base 0 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1023c9 bytes 11 3
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [movzxR32M16Effect, Effect.components, Component.Covers]) _,
        ?_⟩
    · x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.readable 0 2 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x23d7 (by decide))
  advance_then (mov_m16_r16_effect_step 0x1023d7 1 (.sib 4 none 0 (.d32 336)) (by decide +kernel) rfl
    rfl)
  case sub => exact codeRange_slice_subset 0x1023c9 bytes 14 8
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.writable.add 0 (show 0 + 2 ≤ 32 by decide)
    · x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.codeApart 0 2 (by decide) 0x23d7 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.codeApart 0 2 (by decide) 0x23c9 79 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x23df (by decide))
  advance_then (LegacyLoad.mov_r32_m32_legacy_effect_step 0x1023df 1 (.base 0 (.d8 3))
    (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1023c9 bytes 22 3
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [LegacyLoad.movR32M32LegacyEffect, Effect.components,
        Component.Covers]) _, ?_⟩
    · x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.readable 3 4 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x23e2 (by decide))
  advance_then (mov_r64_m64_effect_step 0x1023e2 0x48 (by simp [RexWPrefix]) 2 (.base 0 (.d8 7)) (by
    decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1023c9 bytes 25 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [movR64M64Effect, Effect.components, Component.Covers]) _, ?_⟩
    · x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.readable 7 8 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x23e6 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x1023e6 0x48 (by simp [RexWPrefix]) 2
    (.sib 4 none 0 (.d32 343)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1023c9 bytes 29 8
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.writable.add 7 (show 7 + 8 ≤ 32 by decide)
    · x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.codeApart 7 8 (by decide) 0x23e6 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.codeApart 7 8 (by decide) 0x23c9 79 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x23ee (by decide))
  advance_then (mov_r64_m64_effect_step 0x1023ee 0x48 (by simp [RexWPrefix]) 2 (.base 0 (.d8 15))
    (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1023c9 bytes 37 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [movR64M64Effect, Effect.components, Component.Covers]) _, ?_⟩
    · x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.readable 15 8 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x23f2 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x1023f2 0x48 (by simp [RexWPrefix]) 2
    (.sib 4 none 0 (.d32 351)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1023c9 bytes 41 8
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.writable.add 15 (show 15 + 8 ≤ 32 by decide)
    · x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.codeApart 15 8 (by decide) 0x23f2 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.codeApart 15 8 (by decide) 0x23c9 79 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x23fa (by decide))
  advance_then (mov_r64_m64_effect_step 0x1023fa 0x48 (by simp [RexWPrefix]) 2 (.base 0 (.d8 23))
    (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1023c9 bytes 49 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [movR64M64Effect, Effect.components, Component.Covers]) _, ?_⟩
    · x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.readable 23 8 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x23fe (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x1023fe 0x48 (by simp [RexWPrefix]) 2
    (.sib 4 none 0 (.d32 359)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1023c9 bytes 53 8
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.writable.add 23 (show 23 + 8 ≤ 32 by decide)
    · x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.codeApart 23 8 (by decide) 0x23fe 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.codeApart 23 8 (by decide) 0x23c9 79 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2406 (by decide))
  advance_then (movzx_r32_m8_effect_step 0x102406 0 (.base 0 (.d8 31)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1023c9 bytes 61 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [movzxR32M8Effect, Effect.components, Component.Covers]) _,
        ?_⟩
    · x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.readable 31 1 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x240a (by decide))
  advance_then (mov_m8_r8_legacy_effect_step 0x10240a 0 (by decide +kernel) (.sib 4 none 0 (.d32 367))
    (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1023c9 bytes 65 7
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.byteWritable 31 (by decide)
    · x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.codeApart 31 1 (by decide) 0x240a 7 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.codeApart 31 1 (by decide) 0x23c9 79 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2411 (by decide))
  advance_then (CrossPageStore.mov_m32_r32_legacy_effect_step_any 0x102411 1 (.sib 4 none 0 (.d32 339))
    (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1023c9 bytes 72 7
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.writable.add 3 (show 3 + 4 ≤ 32 by decide)
    · x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.codeApart 3 4 (by decide) 0x2411 7 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.codeApart 3 4 (by decide) 0x23c9 79 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2418 (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  have hread (mem : Ram) (i j n k : Nat) (v : BitVec n)
      (hi : i+n/8 ≤ 32) (hj : j+k/8 ≤ 32) :
      memLoad (memStore mem (((Operand.reg 4 : Operand 64).read s + 336) + BitVec.ofNat 64 i) v)
        ((Operand.reg 0 : Operand 64).read s + BitVec.ofNat 64 j) k =
      memLoad mem ((Operand.reg 0 : Operand 64).read s + BitVec.ofNat 64 j) k := by
    apply memLoad_memStore_of_rangeApart
    intro a ha b hb he
    apply hP.apart (i+a) (by omega) (j+b) (by omega)
    simpa [BitVec.ofNat_add, BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue,
      Syntax.Reg.fin, gprIndex] using he
  have h2_0 := fun mem v => hread mem 2 0 8 16 v (by decide) (by decide)
  have h2_3 := fun mem v => hread mem 2 3 8 32 v (by decide) (by decide)
  have h0_3 := fun mem v => hread mem 0 3 16 32 v (by decide) (by decide)
  have h2_7 := fun mem v => hread mem 2 7 8 64 v (by decide) (by decide)
  have h0_7 := fun mem v => hread mem 0 7 16 64 v (by decide) (by decide)
  have h2_15 := fun mem v => hread mem 2 15 8 64 v (by decide) (by decide)
  have h0_15 := fun mem v => hread mem 0 15 16 64 v (by decide) (by decide)
  have h7_15 := fun mem v => hread mem 7 15 64 64 v (by decide) (by decide)
  have h2_23 := fun mem v => hread mem 2 23 8 64 v (by decide) (by decide)
  have h0_23 := fun mem v => hread mem 0 23 16 64 v (by decide) (by decide)
  have h7_23 := fun mem v => hread mem 7 23 64 64 v (by decide) (by decide)
  have h15_23 := fun mem v => hread mem 15 23 64 64 v (by decide) (by decide)
  have h2_31 := fun mem v => hread mem 2 31 8 8 v (by decide) (by decide)
  have h0_31 := fun mem v => hread mem 0 31 16 8 v (by decide) (by decide)
  have h7_31 := fun mem v => hread mem 7 31 64 8 v (by decide) (by decide)
  have h15_31 := fun mem v => hread mem 15 31 64 8 v (by decide) (by decide)
  have h23_31 := fun mem v => hread mem 23 31 64 8 v (by decide) (by decide)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, show (336 : BitVec 64) = 336#64 from rfl,
    show (4 : BitVec 5) = 4#5 from rfl,
    show (0 : BitVec 5) = 0#5 from rfl] at h2_0 h2_3 h0_3 h2_7 h0_7 h2_15 h0_15 h7_15
  simp only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, show (336 : BitVec 64) = 336#64 from rfl,
    show (4 : BitVec 5) = 4#5 from rfl,
    show (0 : BitVec 5) = 0#5 from rfl] at h2_23 h0_23 h7_23 h15_23 h2_31 h0_31 h7_31 h15_31 h23_31
  apply hH.weaken
  · x86_norm [effect, BitVec.add_zero, BitVec.setWidth_setWidth_of_le]
  · x86_norm [effect, BitVec.add_zero, BitVec.setWidth_setWidth_of_le, h2_0, h2_3, h0_3, h2_7, h0_7,
    h2_15, h0_15, h7_15, h2_23, h0_23, h7_23, h15_23, h2_31, h0_31, h7_31, h15_31, h23_31]
    all_goals (repeat constructor <;> rfl)
  · intro i
    cases i <;> x86_norm [effect]
  · x86_norm [effect, BitVec.add_zero, BitVec.setWidth_setWidth_of_le]

end P256.Proofs.Signing.Wrapper.Entry.Decode.Copy
