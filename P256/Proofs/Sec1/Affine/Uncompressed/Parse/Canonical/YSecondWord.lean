import P256.Proofs.Common.Field.Operations.Run.Compose
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
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Sec1.Affine.Uncompressed.Parse.Canonical

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def ySecondWordBytes : List UInt8 :=
  [73, 191, 1, 0, 0, 0, 255, 255, 255, 255, 73, 1, 248, 77, 1, 248, 72, 247, 215, 76, 33, 199, 72, 193, 239, 63]

def ySecondWordEffect (s : RamState) : Effect :=
  let x := (Operand.reg 7 : Operand 64).read s
  let b := (Operand.reg 8 : Operand 64).read s
  let r := b + x + 0xffffffff00000001
  { rip := 0x1106af
    writes := [⟨(Operand.reg 15 : Operand 64), 0xffffffff00000001⟩,
      ⟨(Operand.reg 8 : Operand 64), r⟩,
      ⟨(Operand.reg 7 : Operand 64), (~~~x &&& r) >>> 63⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

def ySecondSumEffect (s : RamState) : Effect :=
  { rip := 0x1106a5
    writes := [⟨(Operand.reg 15 : Operand 64), 0xffffffff00000001⟩,
      ⟨(Operand.reg 8 : Operand 64),
        (Operand.reg 8 : Operand 64).read s + (Operand.reg 7 : Operand 64).read s +
          0xffffffff00000001⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

def ySecondBorrowEffect (s : RamState) : Effect :=
  { rip := 0x1106af
    writes := [⟨(Operand.reg 7 : Operand 64),
      (~~~((Operand.reg 7 : Operand 64).read s) &&& (Operand.reg 8 : Operand 64).read s) >>> 63⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem y_second_sum_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x110695)
      (codeRange 0x110695 ySecondWordBytes) (Effect.post ySecondSumEffect) := by
  advance_begin (mov_r64_imm64_effect_step 0x110695 0x49 0xbf
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) 0xffffffff00000001)
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0x1069f (by decide +kernel))
  advance_then (add_r64_r64_effect_step 0x11069f 0x49 0xf8
    (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x110695 ySecondWordBytes 10 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x106a2 (by decide +kernel))
  advance_then (add_r64_r64_effect_step 0x1106a2 0x4d 0xf8
    (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x110695 ySecondWordBytes 13 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x106a5 (by decide +kernel))
  advance_finish [ySecondSumEffect]

theorem y_second_borrow_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1106a5)
      (codeRange 0x110695 ySecondWordBytes) (Effect.post ySecondBorrowEffect) := by
  advance_begin (not_r64_effect_step 0x1106a5 0x48 0xd7
    (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110695 ySecondWordBytes 16 3
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0x106a8 (by decide +kernel))
  advance_then (and_r64_r64_effect_step 0x1106a8 0x4c 0xc7
    (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x110695 ySecondWordBytes 19 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x106ab (by decide +kernel))
  advance_then (shr_r64_imm8_effect_step 0x1106ab 0x48 0xef 63
    (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110695 ySecondWordBytes 22 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x106af (by decide +kernel))
  advance_finish [ySecondBorrowEffect]

theorem y_second_word_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x110695)
      (codeRange 0x110695 ySecondWordBytes) (Effect.post ySecondWordEffect) := by
  intro s hr hc hp
  obtain ⟨n, u, ha, hru, hcu, hu⟩ := y_second_sum_correct boundary hout s hr hc hp
  obtain ⟨m, t, hb, hrt, hct, ht⟩ := y_second_borrow_correct boundary hout u hru hcu hu.rip
  have hr8 : (Operand.reg 7 : Operand 64).read u = (Operand.reg 7 : Operand 64).read s :=
    hu.agrees.read (by simp [ySecondSumEffect, Effect.components])
  refine ⟨n+m, t, ha.trans hb, hrt, hct, ht.rip, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · exact (ht.agrees.read (n := 64) (r := 15)
        (by simp [ySecondBorrowEffect, Effect.components])).trans hu.writes.1
    · exact (ht.agrees.read (n := 64) (r := 8)
        (by simp [ySecondBorrowEffect, Effect.components])).trans hu.writes.2
    · have hh := ht.writes
      change (Operand.reg 7 : Operand 64).read t =
        (~~~((Operand.reg 7 : Operand 64).read u) &&& (Operand.reg 8 : Operand 64).read u) >>> 63 at hh
      rw [hr8, hu.writes.2] at hh
      exact hh
  · exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  · apply (hu.agrees.trans ht.agrees).mono
    simp [ySecondSumEffect, ySecondBorrowEffect, ySecondWordEffect, Effect.components]

end P256.Proofs.Sec1.Affine.Uncompressed.Parse.Canonical
