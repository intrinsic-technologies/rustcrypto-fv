import P256.Proofs.EcdhWrapper.Copy.Support

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Copy

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions
open P256.Proofs.EcdhWrapper.Copy
open P256.Proofs.Common.Curve.LinearCombination.NafReverse

def bytes : List UInt8 :=
  [0xf, 0xb6, 0x48, 0x2, 0x88, 0x4c, 0x24, 0x72, 0xf, 0xb7, 0x8, 0x66, 0x89, 0x4c, 0x24, 0x70, 0x8b, 0x48, 0x3, 0x48, 0x8b, 0x50, 0x7, 0x48, 0x89, 0x54, 0x24, 0x77, 0x48, 0x8b, 0x50, 0xf, 0x48, 0x89, 0x54, 0x24, 0x7f, 0x48, 0x8b, 0x50, 0x17, 0x48, 0x89, 0x94, 0x24, 0x87, 0x0, 0x0, 0x0, 0xf, 0xb6, 0x40, 0x1f, 0x88, 0x84, 0x24, 0x8f, 0x0, 0x0, 0x0, 0x89, 0x4c, 0x24, 0x73]

def effect (s : RamState) : Effect :=
  { rip := 0x10687d
    writes := [
      ⟨(.reg 1 : Operand 64), (memLoad s.external ((Operand.reg 0 : Operand 64).read s + 3)
        32).setWidth 64⟩,
      ⟨(.reg 0 : Operand 64), (memLoad s.external ((Operand.reg 0 : Operand 64).read s + 31)
        8).setWidth 64⟩,
      ⟨(.reg 2 : Operand 64), (memLoad s.external ((Operand.reg 0 : Operand 64).read s + 23)
        64).setWidth 64⟩,
      ⟨(.mem (((Operand.reg 4 : Operand 64).read s + 112) + 2) : Operand 8), memLoad s.external
        ((Operand.reg 0 : Operand 64).read s + 2) 8⟩,
      ⟨(.mem (((Operand.reg 4 : Operand 64).read s + 112) + 0) : Operand 16), memLoad s.external
        ((Operand.reg 0 : Operand 64).read s + 0) 16⟩,
      ⟨(.mem (((Operand.reg 4 : Operand 64).read s + 112) + 7) : Operand 64), memLoad s.external
        ((Operand.reg 0 : Operand 64).read s + 7) 64⟩,
      ⟨(.mem (((Operand.reg 4 : Operand 64).read s + 112) + 15) : Operand 64), memLoad s.external
        ((Operand.reg 0 : Operand 64).read s + 15) 64⟩,
      ⟨(.mem (((Operand.reg 4 : Operand 64).read s + 112) + 23) : Operand 64), memLoad s.external
        ((Operand.reg 0 : Operand 64).read s + 23) 64⟩,
      ⟨(.mem (((Operand.reg 4 : Operand 64).read s + 112) + 31) : Operand 8), memLoad s.external
        ((Operand.reg 0 : Operand 64).read s + 31) 8⟩,
      ⟨(.mem (((Operand.reg 4 : Operand 64).read s + 112) + 3) : Operand 32), memLoad s.external
        ((Operand.reg 0 : Operand 64).read s + 3) 32⟩] }

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip)
    (input : ByteArray) :
    AdvanceTriple boundary (fun s => CopyPre input s .rax 0x10683d) (codeRange 0x10683d bytes) (Effect.post effect) := by
  advance_begin (movzx_r32_m8_effect_step 0x10683d 1 (.base 0 (.d8 2)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    refine ⟨hP.rip, ?_⟩
    x86_norm
    exact hP.readable 2 1 (by decide)
  case next =>
    intro s hP
    exact boundary_ne_program outside (inProgram_of_textOffset 0x6841 (by decide))
  advance_then (mov_m8_r8_legacy_effect_step 0x106841 1 (by decide +kernel) (.sib 4 none 0 (.d8 114))
    (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10683d bytes 4 4
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.byteWritable 2 (by decide)
    · x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.codeApart 2 1 (by decide) 0x6841 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.codeApart 2 1 (by decide) 0x683d 64 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6845 (by decide))
  advance_then (movzx_r32_m16_effect_step 0x106845 1 (.base 0 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10683d bytes 8 3
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [movzxR32M16Effect, Effect.components, Component.Covers]) _,
        ?_⟩
    · x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.readable 0 2 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6848 (by decide))
  advance_then (mov_m16_r16_effect_step 0x106848 1 (.sib 4 none 0 (.d8 112)) (by decide +kernel) rfl
    rfl)
  case sub => exact codeRange_slice_subset 0x10683d bytes 11 5
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.writable.add 0 (show 0 + 2 ≤ 32 by decide)
    · x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.codeApart 0 2 (by decide) 0x6848 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.codeApart 0 2 (by decide) 0x683d 64 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x684d (by decide))
  advance_then (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10684d 1 (.base 0 (.d8 3))
    (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10683d bytes 16 3
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [LegacyLoad.movR32M32LegacyEffect, Effect.components,
        Component.Covers]) _, ?_⟩
    · x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.readable 3 4 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6850 (by decide))
  advance_then (mov_r64_m64_effect_step 0x106850 0x48 (by simp [RexWPrefix]) 2 (.base 0 (.d8 7)) (by
    decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10683d bytes 19 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [movR64M64Effect, Effect.components, Component.Covers]) _, ?_⟩
    · x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.readable 7 8 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6854 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x106854 0x48 (by simp [RexWPrefix]) 2
    (.sib 4 none 0 (.d8 119)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10683d bytes 23 5
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.writable.add 7 (show 7 + 8 ≤ 32 by decide)
    · x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.codeApart 7 8 (by decide) 0x6854 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.codeApart 7 8 (by decide) 0x683d 64 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6859 (by decide))
  advance_then (mov_r64_m64_effect_step 0x106859 0x48 (by simp [RexWPrefix]) 2 (.base 0 (.d8 15))
    (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10683d bytes 28 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [movR64M64Effect, Effect.components, Component.Covers]) _, ?_⟩
    · x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.readable 15 8 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x685d (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x10685d 0x48 (by simp [RexWPrefix]) 2
    (.sib 4 none 0 (.d8 127)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10683d bytes 32 5
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.writable.add 15 (show 15 + 8 ≤ 32 by decide)
    · x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.codeApart 15 8 (by decide) 0x685d 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.codeApart 15 8 (by decide) 0x683d 64 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6862 (by decide))
  advance_then (mov_r64_m64_effect_step 0x106862 0x48 (by simp [RexWPrefix]) 2 (.base 0 (.d8 23))
    (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10683d bytes 37 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [movR64M64Effect, Effect.components, Component.Covers]) _, ?_⟩
    · x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.readable 23 8 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6866 (by decide))
  advance_then (CrossPageStore.mov_m64_r64_effect_step_any 0x106866 0x48 (by simp [RexWPrefix]) 2
    (.sib 4 none 0 (.d32 135)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10683d bytes 41 8
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.writable.add 23 (show 23 + 8 ≤ 32 by decide)
    · x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.codeApart 23 8 (by decide) 0x6866 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.codeApart 23 8 (by decide) 0x683d 64 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x686e (by decide))
  advance_then (movzx_r32_m8_effect_step 0x10686e 0 (.base 0 (.d8 31)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10683d bytes 49 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [movzxR32M8Effect, Effect.components, Component.Covers]) _,
        ?_⟩
    · x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.readable 31 1 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6872 (by decide))
  advance_then (mov_m8_r8_legacy_effect_step 0x106872 0 (by decide +kernel) (.sib 4 none 0 (.d32 143))
    (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10683d bytes 53 7
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.byteWritable 31 (by decide)
    · x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.codeApart 31 1 (by decide) 0x6872 7 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.codeApart 31 1 (by decide) 0x683d 64 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6879 (by decide))
  advance_then (CrossPageStore.mov_m32_r32_legacy_effect_step_any 0x106879 1 (.sib 4 none 0 (.d8 115))
    (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10683d bytes 60 4
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.writable.add 3 (show 3 + 4 ≤ 32 by decide)
    · x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.codeApart 3 4 (by decide) 0x6879 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.codeApart 3 4 (by decide) 0x683d 64 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x687d (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  have hread (mem : Ram) (i j n k : Nat) (v : BitVec n)
      (hi : i+n/8 ≤ 32) (hj : j+k/8 ≤ 32) :
      memLoad (memStore mem (((Operand.reg 4 : Operand 64).read s + 112) + BitVec.ofNat 64 i) v)
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
  simp only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, show (112 : BitVec 64) = 112#64 from rfl,
    show (4 : BitVec 5) = 4#5 from rfl,
    show (0 : BitVec 5) = 0#5 from rfl] at h2_0 h2_3 h0_3 h2_7 h0_7 h2_15 h0_15 h7_15
  simp only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, show (112 : BitVec 64) = 112#64 from rfl,
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

end P256.Proofs.EcdhWrapper.Copy
