import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.Code
import P256.Proofs.Common.Field.Operations.Neg.Borrow.Or
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
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Sec1.Decompress.Input

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def canonicalHighWordBytes : List UInt8 :=
  [0xb9,0xff,0xff,0xff,0xff,0x48,0x01,0xc1,0x48,0x01,0xce,
    0x48,0xf7,0xd0,0x48,0x09,0xf0,0x48,0xc1,0xe8,0x3f]

def canonicalHighWordEffect (s : RamState) : Effect :=
  let x := (Operand.reg 0 : Operand 64).read s
  let r := (Operand.reg 6 : Operand 64).read s + (0xffffffff + x)
  { rip := 0x10fcc5
    writes := [⟨(Operand.reg 1 : Operand 64), 0xffffffff + x⟩,
      ⟨(Operand.reg 6 : Operand 64), r⟩,
      ⟨(Operand.reg 0 : Operand 64), (~~~x ||| r) >>> 63⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

def canonicalHighSumEffect (s : RamState) : Effect :=
  { rip := 0x10fcbb
    writes := [⟨(Operand.reg 1 : Operand 64), 0xffffffff + (Operand.reg 0 : Operand 64).read s⟩,
      ⟨(Operand.reg 6 : Operand 64),
        (Operand.reg 6 : Operand 64).read s + (0xffffffff + (Operand.reg 0 : Operand 64).read s)⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

def canonicalHighBorrowEffect (s : RamState) : Effect :=
  { rip := 0x10fcc5
    writes := [⟨(Operand.reg 0 : Operand 64),
      (~~~((Operand.reg 0 : Operand 64).read s) ||| (Operand.reg 6 : Operand 64).read s) >>> 63⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem canonical_high_sum_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10fcb0)
      (codeRange 0x10fcb0 canonicalHighWordBytes) (Effect.post canonicalHighSumEffect) := by
  advance_begin (mov_r32_imm32_effect_step 0x10fcb0 0xb9 (by decide +kernel) 0xffffffff)
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0xfcb5 (by decide +kernel))
  advance_then (add_r64_r64_effect_step 0x10fcb5 0x48 0xc1
    (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x10fcb0 canonicalHighWordBytes 5 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfcb8 (by decide +kernel))
  advance_then (add_r64_r64_effect_step 0x10fcb8 0x48 0xce
    (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x10fcb0 canonicalHighWordBytes 8 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfcbb (by decide +kernel))
  advance_finish [canonicalHighSumEffect]

theorem canonical_high_borrow_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10fcbb)
      (codeRange 0x10fcb0 canonicalHighWordBytes) (Effect.post canonicalHighBorrowEffect) := by
  advance_begin (not_r64_effect_step 0x10fcbb 0x48 0xd0
    (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fcb0 canonicalHighWordBytes 11 3
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0xfcbe (by decide +kernel))
  advance_then (or_r64_r64_effect_step 0x10fcbe 0x48 0xf0
    (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x10fcb0 canonicalHighWordBytes 14 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfcc1 (by decide +kernel))
  advance_then (shr_r64_imm8_effect_step 0x10fcc1 0x48 0xe8 63
    (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fcb0 canonicalHighWordBytes 17 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfcc5 (by decide +kernel))
  advance_finish [canonicalHighBorrowEffect]

theorem canonical_high_word_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10fcb0)
      (codeRange 0x10fcb0 canonicalHighWordBytes) (Effect.post canonicalHighWordEffect) := by
  intro s hr hc hp
  obtain ⟨n, u, ha, hru, hcu, hu⟩ := canonical_high_sum_correct boundary hout s hr hc hp
  obtain ⟨m, t, hb, hrt, hct, ht⟩ := canonical_high_borrow_correct boundary hout u hru hcu hu.rip
  have hr0 : (Operand.reg 0 : Operand 64).read u = (Operand.reg 0 : Operand 64).read s :=
    hu.agrees.read (by simp [canonicalHighSumEffect, Effect.components])
  refine ⟨n+m, t, ha.trans hb, hrt, hct, ht.rip, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · exact (ht.agrees.read (n := 64) (r := 1)
        (by simp [canonicalHighBorrowEffect, Effect.components])).trans hu.writes.1
    · exact (ht.agrees.read (n := 64) (r := 6)
        (by simp [canonicalHighBorrowEffect, Effect.components])).trans hu.writes.2
    · have hh := ht.writes
      change (Operand.reg 0 : Operand 64).read t =
        (~~~((Operand.reg 0 : Operand 64).read u) ||| (Operand.reg 6 : Operand 64).read u) >>> 63 at hh
      rw [hr0, hu.writes.2] at hh
      exact hh
  · exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  · apply (hu.agrees.trans ht.agrees).mono
    simp [canonicalHighSumEffect, canonicalHighBorrowEffect, canonicalHighWordEffect, Effect.components]

end P256.Proofs.Sec1.Decompress.Input
