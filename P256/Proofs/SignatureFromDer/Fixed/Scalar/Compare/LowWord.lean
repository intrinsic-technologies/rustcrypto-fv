import X86Proofs.Instructions.Lea.Triple
import P256.Proofs.SignatureFromDer.Fixed.Scalar.Compare.Slot
import P256.Proofs.SignatureFromDer.Fixed.Scalar.Compare.Common

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.SignatureFromDer.Fixed.Scalar.Compare (BorrowSlotPre)
open P256.Proofs.Common.Field.FieldNeg.Instructions (or_r64_r64_effect_step)
open P256.Proofs.Common.Field.Instructions (subR64M64Effect_components sub_r64_m64_effect_step)
open P256.Proofs.Common.Instructions (sarR64Effect_components sar_r64_imm8_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.SignatureFromDer.Fixed.Scalar.Compare

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def lowWordBytes : List UInt8 :=
  [0x48,0xb8,0xaf,0xda,0x9c,0x3,0x3d,0x35,0x46,0xc,0x4c,0x1,0xf8,0x4c,0x89,0xf9,0x48,0xf7,0xd1,0x48,0x9,0xc1,0x48,0xc1,0xe9,0x3f]

def lowWordEffect (s : RamState) : Effect :=
  let x := (Operand.reg 15 : Operand 64).read s
  { rip := 0x10fae5
    writes := [⟨(Operand.reg 0 : Operand 64), 0xc46353d039cdaaf + x⟩,
      ⟨(Operand.reg 1 : Operand 64), (~~~x ||| (0xc46353d039cdaaf + x)) >>> 63⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem low_word_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10facb)
      (codeRange 0x10facb lowWordBytes) (Effect.post lowWordEffect) := by
  advance_begin (mov_r64_imm64_effect_step 0x10facb 0x48 0xb8
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) 0xc46353d039cdaaf)
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0xfad5 (by decide +kernel))
  advance_then (add_r64_r64_effect_step 0x10fad5 0x4c 0xf8
    (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x10facb lowWordBytes 10 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfad8 (by decide +kernel))
  advance_then (mov_r64_r64_effect_step 0x10fad8 0x4c 0xf9
    (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x10facb lowWordBytes 13 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfadb (by decide +kernel))
  advance_then (not_r64_effect_step 0x10fadb 0x48 0xd1
    (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10facb lowWordBytes 16 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfade (by decide +kernel))
  advance_then (or_r64_r64_effect_step 0x10fade 0x48 0xc1
    (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x10facb lowWordBytes 19 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfae1 (by decide +kernel))
  advance_then (shr_r64_imm8_effect_step 0x10fae1 0x48 0xe9 63
    (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10facb lowWordBytes 22 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfae5 (by decide +kernel))
  advance_finish [lowWordEffect]

def borrowSetupBytes : List UInt8 :=
  [0x48,0x89,0x4c,0x24,0x8,0x48,0x8d,0x44,0x24,0x8,0x31,0xc9,0x31,0xd2,0x48,0x2b,0x54,0x24,0x8,0x48,0xc1,0xfa,0x3f]

def borrowSetupEffect (s : RamState) : Effect :=
  { rip := 0x10fafc
    writes := [⟨(Operand.mem (stackPtr s + 8) : Operand 64), (Operand.reg 1 : Operand 64).read s⟩,
      ⟨(Operand.reg 0 : Operand 64), stackPtr s + 8⟩,
      ⟨(Operand.reg 1 : Operand 64), 0⟩,
      ⟨(Operand.reg 2 : Operand 64), (-((Operand.reg 1 : Operand 64).read s)).sshiftRight 63⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem borrow_setup_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (BorrowSlotPre 0x10fae5)
      (codeRange 0x10fae5 borrowSetupBytes) (Effect.post borrowSetupEffect) := by
  advance_begin (mov_m64_r64_effect_step 0x10fae5 0x48
    (by unfold RexWPrefix; decide +kernel) 1 (.sib 4 none 0 (.d8 8))
    (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    refine ⟨h.rip, ?_, ?_⟩
    · change MemWritable s (stackPtr s + 8#64) 8
      exact h.writable
    · change RangeApart (stackPtr s + 8#64) 8 0x10fae5 5
      have ha := h.apart 0xfae5 5 (by decide +kernel)
      change RangeApart (stackPtr s + 8) 8 (0x10fae5 : BitVec 64) 5 at ha
      exact ha
  case av =>
    intro s h
    apply h.avoids_code 0xfae5 borrowSetupBytes (by decide +kernel)
    intro c hc a len he
    simp only [movM64R64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · cases he
      exact ⟨rfl, rfl⟩
    · cases he
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0xfaea (by decide +kernel))
  advance_then (lea_r64_effect_step 0x10faea 0x48 (by unfold RexWPrefix; decide +kernel) 0 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fae5 borrowSetupBytes 5 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfaef (by decide +kernel))
  advance_then (xor_r32_r32_effect_step 0x10faef 0xc9 rfl)
  case sub => exact codeRange_slice_subset 0x10fae5 borrowSetupBytes 10 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfaf1 (by decide +kernel))
  advance_then (xor_r32_r32_effect_step 0x10faf1 0xd2 rfl)
  case sub => exact codeRange_slice_subset 0x10fae5 borrowSetupBytes 12 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfaf3 (by decide +kernel))
  advance_then (sub_r64_m64_effect_step 0x10faf3 0x48
    (by unfold RexWPrefix; decide +kernel) 2 (.sib 4 none 0 (.d8 8))
    (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fae5 borrowSetupBytes 14 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [BitVec.add_zero]
      exact hP.writable.readable
    · apply Effect.Avoids.of_noMem
      simp [subR64M64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfaf8 (by decide +kernel))
  advance_then (sar_r64_imm8_effect_step 0x10faf8 0x48 0xfa 63
    (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fae5 borrowSetupBytes 19 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [sarR64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfafc (by decide +kernel))
  apply AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · rfl
  · x86_norm [borrowSetupEffect, stackPtr, BitVec.add_zero]
    change (stackPtr s + 8 = (Operand.reg 4 : Operand 64).read s + 8 ∧
        (Operand.reg 1 : Operand 64).read s = (Operand.reg 1 : Operand 64).read s) ∧
      stackPtr s + 8 = (Operand.reg 4 : Operand 64).read s + 8 ∧
      (0 : BitVec 64) = (((Operand.reg 1 : Operand 32).read s) ^^^
        ((Operand.reg 1 : Operand 32).read s)).setWidth 64 ∧
      (-((Operand.reg 1 : Operand 64).read s)).sshiftRight 63 =
        ((((Operand.reg 2 : Operand 32).read s ^^^ (Operand.reg 2 : Operand 32).read s).setWidth 64) -
          ((Operand.reg 1 : Operand 64).read s)).sshiftRight 63
    simp [BitVec.xor_self, BitVec.zero_sub, stackPtr, Operand.read_reg64]
  · intro i
    cases i <;> x86_norm [borrowSetupEffect]
  · x86_norm [borrowSetupEffect, stackPtr, BitVec.add_zero]
    rfl

end P256.Proofs.SignatureFromDer.Fixed.Scalar.Compare
