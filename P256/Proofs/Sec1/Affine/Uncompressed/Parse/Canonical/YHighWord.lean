import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.Field.Operations.Neg.Borrow.Or
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Movs.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Field.FieldNeg.Instructions (or_r64_r64_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice)

namespace P256.Proofs.Sec1.Affine.Uncompressed.Parse.Canonical

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def yHighWordBytes : List UInt8 :=
  [65, 188, 255, 255, 255, 255, 72, 1, 193, 76, 1, 225, 72, 247, 208, 72, 9, 200, 72, 193, 232, 63]

def yHighWordEffect (s : RamState) : Effect :=
  { rip := 0x1106f5
    writes := [⟨(.reg 12 : Operand 64), 0xffffffff⟩,
      ⟨(.reg 1 : Operand 64), ((Operand.reg 1 : Operand 64).read s)+((Operand.reg 0 : Operand 64).read s)+0xffffffff⟩,
      ⟨(.reg 0 : Operand 64), (~~~((Operand.reg 0 : Operand 64).read s) ||| (((Operand.reg 1 : Operand 64).read s)+((Operand.reg 0 : Operand 64).read s)+0xffffffff)) >>> 63⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

def yHighRestEffect (s : RamState) : Effect :=
  let r := (Operand.reg 1 : Operand 64).read s + (Operand.reg 0 : Operand 64).read s +
    (Operand.reg 12 : Operand 64).read s
  { rip := 0x1106f5
    writes := [⟨(.reg 1 : Operand 64), r⟩,
      ⟨(.reg 0 : Operand 64), (~~~((Operand.reg 0 : Operand 64).read s) ||| r) >>> 63⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem y_high_rest_correct [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1106e5)
      (codeRange 0x1106df yHighWordBytes) (Effect.post yHighRestEffect) := by
  advance_begin (add_r64_r64_effect_step 0x1106e5 0x48 0xc1 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1106df yHighWordBytes 6 3
  case next =>
    intro _ _
    exact boundary_ne_program outside (inProgram_of_textOffset 0x106e8 (by decide))
  advance_then (add_r64_r64_effect_step 0x1106e8 0x4c 0xe1 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1106df yHighWordBytes 9 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x106eb (by decide))⟩
  advance_then (not_r64_effect_step 0x1106eb 0x48 0xd0 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1106df yHighWordBytes 12 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x106ee (by decide))⟩
  advance_then (or_r64_r64_effect_step 0x1106ee 0x48 0xc8 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1106df yHighWordBytes 15 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x106f1 (by decide))⟩
  advance_then (shr_r64_imm8_effect_step 0x1106f1 0x48 0xe8 63 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1106df yHighWordBytes 18 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x106f5 (by decide))⟩
  advance_finish [yHighRestEffect]

theorem y_high_word_correct [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1106df)
      (codeRange 0x1106df yHighWordBytes) (Effect.post yHighWordEffect) := by
  intro s ready code rip
  obtain ⟨u, runU, readyU, effectU⟩ :=
    (mov_r32_imm32_rex_effect_step 0x1106df 0x41 0xbc
      (by simp [RexNoWPrefix]) (by decide) 0xffffffff).advances ready
      (code.mono (codeRange_slice_subset 0x1106df yHighWordBytes 0 6)) rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x106e5 (by decide)))
  change (movR32Imm32Effect 0x1106df 6 12 0xffffffff s).Holds s u at effectU
  have memory := effectU.agrees.external (by simp [movR32Imm32Effect, Effect.components, Component.Covers])
  have codeU : CodeIn (codeRange 0x1106df yHighWordBytes) u := by
    intro x hx
    exact ⟨(code x hx).1, memory ▸ (code x hx).2⟩
  obtain ⟨n, t, runT, readyT, codeT, effectT⟩ :=
    y_high_rest_correct boundary outside u readyU codeU effectU.rip
  have c : (Operand.reg 12 : Operand 64).read u = 0xffffffff := effectU.writes
  have a : (Operand.reg 0 : Operand 64).read u = (Operand.reg 0 : Operand 64).read s :=
    effectU.agrees.read (by simp [movR32Imm32Effect, Effect.components])
  have b : (Operand.reg 1 : Operand 64).read u = (Operand.reg 1 : Operand 64).read s :=
    effectU.agrees.read (by simp [movR32Imm32Effect, Effect.components])
  refine ⟨1+n, t, runU.trans runT, readyT, codeT, effectT.rip, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · exact (effectT.agrees.read (n := 64) (r := 12)
        (by simp [yHighRestEffect, Effect.components])).trans c
    · simpa only [yHighRestEffect, Write.AllHold, a, b, c] using effectT.writes.1
    · simpa only [yHighRestEffect, Write.AllHold, a, b, c] using effectT.writes.2
  · exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  · apply (effectU.agrees.trans effectT.agrees).mono
    simp [movR32Imm32Effect, yHighRestEffect, yHighWordEffect, Effect.components]

end P256.Proofs.Sec1.Affine.Uncompressed.Parse.Canonical
