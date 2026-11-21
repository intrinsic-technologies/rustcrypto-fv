import P256.Proofs.Verifying.Wrapper.KeyCopy.Interface

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper.KeyCopy.Tail

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions
open P256.Proofs.Common.Curve.LinearCombination.NafReverse

def bytes : List UInt8 :=
  [15, 183, 74, 63, 102, 137, 76, 36, 63, 137, 68, 36, 3]

def effect (s : RamState) : Effect :=
  { rip := 0x1030e6
    writes := [⟨(.reg 1 : Operand 64),
      (memLoad s.external ((Operand.reg 2 : Operand 64).read s + 63) 16).setWidth 64⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 63) : Operand 16),
        memLoad s.external ((Operand.reg 2 : Operand 64).read s + 63) 16⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 3) : Operand 32),
        (Operand.reg 0 : Operand 32).read s⟩] }

theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (Pre 0x1030d9) (codeRange 0x1030d9 bytes) (Effect.post effect) := by
  advance_begin (movzx_r32_m16_effect_step 0x1030d9 1 (.base 2 (.d8 63)) (by decide) rfl rfl)
  case pre =>
    intro s h
    refine ⟨h.rip, ?_⟩
    x86_norm
    exact h.readable 63 2 (by decide)
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0x30dd (by decide))
  advance_then (mov_m16_r16_effect_step 0x1030dd 1 (.sib 4 none 0 (.d8 63)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1030d9 bytes 4 5
  case mid =>
    intro s t h hh ho
    refine ⟨CrossPageStore.Pre.of_holds hh (ho true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      simpa [stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex] using
        h.writable.add 63 (show 63+2≤65 by decide)
    · x86_norm [stackPtr]
      simpa [stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using h.codeApart 63 2 (by decide) 0x30dd 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      simpa [stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using h.codeApart 63 2 (by decide) 0x30d9 13 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x30e2 (by decide))
  advance_then (CrossPageStore.mov_m32_r32_legacy_effect_step_any 0x1030e2 0
    (.sib 4 none 0 (.d8 3)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1030d9 bytes 9 4
  case mid =>
    intro s t h hh ho
    refine ⟨CrossPageStore.Pre.of_holds hh (ho true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      simpa [stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex] using
        h.writable.add 3 (show 3+4≤65 by decide)
    · x86_norm [stackPtr]
      simpa [stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using h.codeApart 3 4 (by decide) 0x30e2 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      simpa [stackPtr, Operand.read_reg64, State.regValue, Syntax.Reg.fin, gprIndex,
        Extracted.textAddress] using h.codeApart 3 4 (by decide) 0x30d9 13 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x30e6 (by decide))
  apply AdvanceTriple.block_end
  intro s t h hh
  apply hh.weaken
  · x86_norm [effect, BitVec.setWidth_setWidth_of_le]
  · x86_norm [effect, BitVec.setWidth_setWidth_of_le]
    exact Or.inr (Or.inr rfl)
  · intro i
    cases i <;> x86_norm [effect]
  · x86_norm [effect, BitVec.setWidth_setWidth_of_le]

end P256.Proofs.Verifying.Wrapper.KeyCopy.Tail
