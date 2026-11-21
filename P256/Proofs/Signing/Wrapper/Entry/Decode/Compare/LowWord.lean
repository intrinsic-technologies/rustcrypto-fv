import P256.Proofs.Signing.Wrapper.Entry.Decode.Compare.Common

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Signing.Wrapper.Entry.Decode.Compare (BorrowSlotPre)
open P256.Proofs.Common.Field.FieldNeg.Instructions (or_r64_r64_effect_step)
open P256.Proofs.Common.Field.Instructions (subR64M64Effect_components sub_r64_m64_effect_step)
open P256.Proofs.Common.Instructions (sarR64Effect_components sar_r64_imm8_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Signing.Wrapper.Entry.Decode.Compare

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def lowWordBytes : List UInt8 :=
  [72, 184, 175, 218, 156, 3, 61, 53, 70, 12, 72, 1, 232, 72, 137, 233, 72, 247, 209, 72, 9, 193, 72, 193, 233, 63]

def lowWordEffect (s : RamState) : Effect :=
  let x := (Operand.reg 5 : Operand 64).read s
  { rip := 0x1024b3
    writes := [⟨(Operand.reg 0 : Operand 64), 0xc46353d039cdaaf + x⟩,
      ⟨(Operand.reg 1 : Operand 64), (~~~x ||| (0xc46353d039cdaaf + x)) >>> 63⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem low_word_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x102499)
      (codeRange 0x102499 lowWordBytes) (Effect.post lowWordEffect) := by
  advance_begin (mov_r64_imm64_effect_step 0x102499 0x48 0xb8
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) 0xc46353d039cdaaf)
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0x24a3 (by decide +kernel))
  advance_then (add_r64_r64_effect_step 0x1024a3 0x48 0xe8
    (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x102499 lowWordBytes 10 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x24a6 (by decide +kernel))
  advance_then (mov_r64_r64_effect_step 0x1024a6 0x48 0xe9
    (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x102499 lowWordBytes 13 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x24a9 (by decide +kernel))
  advance_then (not_r64_effect_step 0x1024a9 0x48 0xd1
    (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x102499 lowWordBytes 16 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x24ac (by decide +kernel))
  advance_then (or_r64_r64_effect_step 0x1024ac 0x48 0xc1
    (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x102499 lowWordBytes 19 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x24af (by decide +kernel))
  advance_then (shr_r64_imm8_effect_step 0x1024af 0x48 0xe9 63
    (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x102499 lowWordBytes 22 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x24b3 (by decide +kernel))
  advance_finish [lowWordEffect]

def borrowSetupBytes : List UInt8 :=
  [72, 137, 140, 36, 176, 0, 0, 0, 72, 141, 132, 36, 176, 0, 0, 0, 49, 201, 49, 210, 72, 43, 148, 36, 176, 0, 0, 0, 72, 193, 250, 63]

def borrowSetupEffect (s : RamState) : Effect :=
  { rip := 0x1024d3
    writes := [⟨(Operand.mem (stackPtr s + 176) : Operand 64), (Operand.reg 1 : Operand 64).read s⟩,
      ⟨(Operand.reg 0 : Operand 64), stackPtr s + 176⟩,
      ⟨(Operand.reg 1 : Operand 64), 0⟩,
      ⟨(Operand.reg 2 : Operand 64), (-((Operand.reg 1 : Operand 64).read s)).sshiftRight 63⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem borrow_setup_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (BorrowSlotPre 0x1024b3)
      (codeRange 0x1024b3 borrowSetupBytes) (Effect.post borrowSetupEffect) := by
  advance_begin (mov_m64_r64_effect_step 0x1024b3 0x48
    (by unfold RexWPrefix; decide +kernel) 1 (.sib 4 none 0 (.d32 176))
    (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    refine ⟨h.rip, ?_, ?_⟩
    · change MemWritable s (stackPtr s + 176#64) 8
      simpa only [BitVec.ofNat_eq_ofNat] using h.writable
    · change RangeApart (stackPtr s + 176#64) 8 0x1024b3 8
      have ha := h.apart 0x24b3 8 (by decide +kernel)
      change RangeApart (stackPtr s + 176) 8 (0x1024b3 : BitVec 64) 8 at ha
      simpa only [BitVec.ofNat_eq_ofNat] using ha
  case av =>
    intro s h
    apply h.avoids_code 0x24b3 borrowSetupBytes (by decide +kernel)
    intro c hc a len he
    simp only [movM64R64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · cases he
      exact ⟨rfl, rfl⟩
    · cases he
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0x24bb (by decide +kernel))
  advance_then (lea_r64_effect_step 0x1024bb 0x48
    (by unfold RexWPrefix; decide +kernel) 0 (.sib 4 none 0 (.d32 176))
    (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1024b3 borrowSetupBytes 8 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x24c3 (by decide +kernel))
  advance_then (xor_r32_r32_effect_step 0x1024c3 0xc9 rfl)
  case sub => exact codeRange_slice_subset 0x1024b3 borrowSetupBytes 16 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x24c5 (by decide +kernel))
  advance_then (xor_r32_r32_effect_step 0x1024c5 0xd2 rfl)
  case sub => exact codeRange_slice_subset 0x1024b3 borrowSetupBytes 18 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x24c7 (by decide +kernel))
  advance_then (sub_r64_m64_effect_step 0x1024c7 0x48
    (by unfold RexWPrefix; decide +kernel) 2 (.sib 4 none 0 (.d32 176))
    (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1024b3 borrowSetupBytes 20 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [BitVec.add_zero]
      exact hP.writable.readable
    · apply Effect.Avoids.of_noMem
      simp [subR64M64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x24cf (by decide +kernel))
  advance_then (sar_r64_imm8_effect_step 0x1024cf 0x48 0xfa 63
    (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1024b3 borrowSetupBytes 28 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [sarR64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x24d3 (by decide +kernel))
  apply AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · rfl
  · x86_norm [borrowSetupEffect, stackPtr, Operand.read_reg64]
    change (Operand.reg 1 : Operand 64).read s = (Operand.reg 1 : Operand 64).read s ∧
      (0 : BitVec 64) = (((Operand.reg 1 : Operand 32).read s) ^^^
        ((Operand.reg 1 : Operand 32).read s)).setWidth 64 ∧
      (-((Operand.reg 1 : Operand 64).read s)).sshiftRight 63 =
        ((((Operand.reg 2 : Operand 32).read s ^^^ (Operand.reg 2 : Operand 32).read s).setWidth 64) -
          ((Operand.reg 1 : Operand 64).read s)).sshiftRight 63
    simp [BitVec.xor_self, BitVec.zero_sub]
  · intro i
    cases i <;> x86_norm [borrowSetupEffect]
  · x86_norm [borrowSetupEffect, stackPtr, Operand.read_reg64]

end P256.Proofs.Signing.Wrapper.Entry.Decode.Compare
