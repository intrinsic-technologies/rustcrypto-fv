import P256.Proofs.Verifying.Wrapper.KeyCopy.Interface

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper.KeyCopy.Head

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions
open P256.Proofs.Common.Curve.LinearCombination.NafReverse

def bytes : List UInt8 :=
  [15, 182, 66, 2, 136, 68, 36, 2, 15, 183, 2, 102, 137, 4, 36, 139, 66, 3]

def effect (s : RamState) : Effect :=
  { rip := 0x10309a
    writes := [⟨(.mem ((Operand.reg 4 : Operand 64).read s + 2) : Operand 8),
        memLoad s.external ((Operand.reg 2 : Operand 64).read s + 2) 8⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s) : Operand 16),
        memLoad s.external ((Operand.reg 2 : Operand 64).read s) 16⟩,
      ⟨(.reg 0 : Operand 64),
        (memLoad s.external ((Operand.reg 2 : Operand 64).read s + 3) 32).setWidth 64⟩] }

theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (Pre 0x103088) (codeRange 0x103088 bytes) (Effect.post effect) := by
  advance_begin (movzx_r32_m8_effect_step 0x103088 0 (.base 2 (.d8 2)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    refine ⟨hP.rip, ?_⟩
    x86_norm
    exact hP.readable 2 1 (by decide)
  case next =>
    intro s hP
    exact boundary_ne_program outside (inProgram_of_textOffset 0x308c (by decide))
  advance_then (mov_m8_r8_legacy_effect_step 0x10308c 0 (by decide +kernel) (.sib 4 none 0 (.d8 2))
    (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x103088 bytes 4 4
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.byteWritable 2 (by decide)
    · x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.codeApart 2 1 (by decide) 0x308c 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.codeApart 2 1 (by decide) 0x3088 18 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x3090 (by decide))
  advance_then (movzx_r32_m16_effect_step 0x103090 0 (.base 2 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x103088 bytes 8 3
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [movzxR32M16Effect, Effect.components, Component.Covers]) _,
        ?_⟩
    · x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.readable 0 2 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x3093 (by decide))
  advance_then (mov_m16_r16_effect_step 0x103093 0 (.sib 4 none 0 .none) (by decide +kernel) rfl
    rfl)
  case sub => exact codeRange_slice_subset 0x103088 bytes 11 4
  case mid =>
    intro s t hP hH hO
    refine ⟨CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.writable.add 0 (show 0 + 2 ≤ 65 by decide)
    · x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.codeApart 0 2 (by decide) 0x3093 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.codeApart 0 2 (by decide) 0x3088 18 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x3097 (by decide))
  advance_then (LegacyLoad.mov_r32_m32_legacy_effect_step 0x103097 0 (.base 2 (.d8 3))
    (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x103088 bytes 15 3
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [LegacyLoad.movR32M32LegacyEffect, Effect.components,
        Component.Covers]) _, ?_⟩
    · x86_norm [stackPtr]
      simpa [BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using hP.readable 3 4 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x309a (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  have hread (mem : Ram) (i j n k : Nat) (v : BitVec n)
      (hi : i+n/8 ≤ 65) (hj : j+k/8 ≤ 65) :
      memLoad (memStore mem ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 i) v)
        ((Operand.reg 2 : Operand 64).read s + BitVec.ofNat 64 j) k =
      memLoad mem ((Operand.reg 2 : Operand 64).read s + BitVec.ofNat 64 j) k := by
    apply memLoad_memStore_of_rangeApart
    intro a ha b hb he
    apply hP.apart (i+a) (by omega) (j+b) (by omega)
    simpa [BitVec.ofNat_add, BitVec.add_assoc, stackPtr, Operand.read_reg64, State.regValue,
      Syntax.Reg.fin, gprIndex] using he
  have h2_0 := fun mem v => hread mem 2 0 8 16 v (by decide) (by decide)
  have h2_3 := fun mem v => hread mem 2 3 8 32 v (by decide) (by decide)
  have h0_3 := fun mem v => hread mem 0 3 16 32 v (by decide) (by decide)
  simp only [BitVec.add_zero, show (2 : BitVec 5) = 2#5 from rfl,
    show (4 : BitVec 5) = 4#5 from rfl] at h2_0 h2_3 h0_3
  apply hH.weaken
  · x86_norm [effect, BitVec.add_zero, BitVec.setWidth_setWidth_of_le]
  · x86_norm [effect, BitVec.add_zero, BitVec.setWidth_setWidth_of_le, h2_0, h2_3, h0_3]
    all_goals (repeat constructor <;> rfl)
  · intro i
    cases i <;> x86_norm [effect]
  · x86_norm [effect, BitVec.add_zero, BitVec.setWidth_setWidth_of_le]

end P256.Proofs.Verifying.Wrapper.KeyCopy.Head
