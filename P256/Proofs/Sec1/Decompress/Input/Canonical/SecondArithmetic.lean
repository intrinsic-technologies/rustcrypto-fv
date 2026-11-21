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

namespace P256.Proofs.Sec1.Decompress.Input

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def canonicalSecondWordBytes : List UInt8 :=
  [0x49,0xbe,0x01,0,0,0,0xff,0xff,0xff,0xff,0x4d,0x01,0xc1,0x4d,0x01,0xf1,
    0x49,0xf7,0xd0,0x4d,0x21,0xc8,0x49,0xc1,0xe8,0x3f]

def canonicalSecondWordEffect (s : RamState) : Effect :=
  let x := (Operand.reg 8 : Operand 64).read s
  let b := (Operand.reg 9 : Operand 64).read s
  let r := b + x + 0xffffffff00000001
  { rip := 0x10fc80
    writes := [⟨(Operand.reg 14 : Operand 64), 0xffffffff00000001⟩,
      ⟨(Operand.reg 9 : Operand 64), r⟩,
      ⟨(Operand.reg 8 : Operand 64), (~~~x &&& r) >>> 63⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

def canonicalSecondSumEffect (s : RamState) : Effect :=
  { rip := 0x10fc76
    writes := [⟨(Operand.reg 14 : Operand 64), 0xffffffff00000001⟩,
      ⟨(Operand.reg 9 : Operand 64),
        (Operand.reg 9 : Operand 64).read s + (Operand.reg 8 : Operand 64).read s +
          0xffffffff00000001⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

def canonicalSecondBorrowEffect (s : RamState) : Effect :=
  { rip := 0x10fc80
    writes := [⟨(Operand.reg 8 : Operand 64),
      (~~~((Operand.reg 8 : Operand 64).read s) &&& (Operand.reg 9 : Operand 64).read s) >>> 63⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem canonical_second_sum_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10fc66)
      (codeRange 0x10fc66 canonicalSecondWordBytes) (Effect.post canonicalSecondSumEffect) := by
  advance_begin (mov_r64_imm64_effect_step 0x10fc66 0x49 0xbe
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) 0xffffffff00000001)
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0xfc70 (by decide +kernel))
  advance_then (add_r64_r64_effect_step 0x10fc70 0x4d 0xc1
    (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x10fc66 canonicalSecondWordBytes 10 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfc73 (by decide +kernel))
  advance_then (add_r64_r64_effect_step 0x10fc73 0x4d 0xf1
    (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x10fc66 canonicalSecondWordBytes 13 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfc76 (by decide +kernel))
  advance_finish [canonicalSecondSumEffect]

theorem canonical_second_borrow_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10fc76)
      (codeRange 0x10fc66 canonicalSecondWordBytes) (Effect.post canonicalSecondBorrowEffect) := by
  advance_begin (not_r64_effect_step 0x10fc76 0x49 0xd0
    (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fc66 canonicalSecondWordBytes 16 3
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0xfc79 (by decide +kernel))
  advance_then (and_r64_r64_effect_step 0x10fc79 0x4d 0xc8
    (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x10fc66 canonicalSecondWordBytes 19 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfc7c (by decide +kernel))
  advance_then (shr_r64_imm8_effect_step 0x10fc7c 0x49 0xe8 63
    (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fc66 canonicalSecondWordBytes 22 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfc80 (by decide +kernel))
  advance_finish [canonicalSecondBorrowEffect]

theorem canonical_second_word_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10fc66)
      (codeRange 0x10fc66 canonicalSecondWordBytes) (Effect.post canonicalSecondWordEffect) := by
  intro s hr hc hp
  obtain ⟨n, u, ha, hru, hcu, hu⟩ := canonical_second_sum_correct boundary hout s hr hc hp
  obtain ⟨m, t, hb, hrt, hct, ht⟩ := canonical_second_borrow_correct boundary hout u hru hcu hu.rip
  have hr8 : (Operand.reg 8 : Operand 64).read u = (Operand.reg 8 : Operand 64).read s :=
    hu.agrees.read (by simp [canonicalSecondSumEffect, Effect.components])
  refine ⟨n+m, t, ha.trans hb, hrt, hct, ht.rip, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · exact (ht.agrees.read (n := 64) (r := 14)
        (by simp [canonicalSecondBorrowEffect, Effect.components])).trans hu.writes.1
    · exact (ht.agrees.read (n := 64) (r := 9)
        (by simp [canonicalSecondBorrowEffect, Effect.components])).trans hu.writes.2
    · have hh := ht.writes
      change (Operand.reg 8 : Operand 64).read t =
        (~~~((Operand.reg 8 : Operand 64).read u) &&& (Operand.reg 9 : Operand 64).read u) >>> 63 at hh
      rw [hr8, hu.writes.2] at hh
      exact hh
  · exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  · apply (hu.agrees.trans ht.agrees).mono
    simp [canonicalSecondSumEffect, canonicalSecondBorrowEffect, canonicalSecondWordEffect, Effect.components]

end P256.Proofs.Sec1.Decompress.Input
