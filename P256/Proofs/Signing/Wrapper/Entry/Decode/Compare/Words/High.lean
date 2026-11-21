import P256.Proofs.Signing.Wrapper.Entry.Decode.Compare.Borrow
import P256.Proofs.Common.Field.Operations.Neg.Borrow.Or
import P256.Proofs.Common.EffectCompose.Memory

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Signing.Wrapper.Entry.Decode.Compare (BorrowSlotPre)
open P256.Proofs.Common.Field.FieldNeg.Instructions (or_r64_r64_effect_step)
open P256.Proofs.Common.Field.Instructions (subR64M64Effect_components sub_r64_m64_effect_step)
open P256.Proofs.Common.Instructions (sarR64Effect_components sar_r64_imm8_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Signing.Wrapper.Entry.Decode.Compare

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def highWordBytes : List UInt8 :=
  [72, 137, 180, 36, 176, 0, 0, 0, 72, 43, 140, 36, 176, 0, 0, 0, 72, 193, 249, 63, 76, 137, 250, 72, 247, 210, 72, 190, 0, 0, 0, 0, 1, 0, 0, 0, 76, 1, 254, 72, 1, 206, 72, 9, 214, 72, 193, 238, 63]

def highWordEffect (s : RamState) : Effect :=
  let x := (Operand.reg 15 : Operand 64).read s
  let c := ((Operand.reg 1 : Operand 64).read s - (Operand.reg 6 : Operand 64).read s).sshiftRight 63
  { rip := 0x102548
    writes := [⟨(Operand.mem (stackPtr s + 176) : Operand 64), (Operand.reg 6 : Operand 64).read s⟩,
      ⟨(Operand.reg 1 : Operand 64), c⟩,
      ⟨(Operand.reg 2 : Operand 64), ~~~x⟩,
      ⟨(Operand.reg 6 : Operand 64), (0x100000000 + x + c ||| ~~~x) >>> 63⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem high_word_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (BorrowSlotPre 0x102517)
      (codeRange 0x102517 highWordBytes) (Effect.post highWordEffect) := by
  advance_begin (mov_m64_r64_effect_step 0x102517 0x48 (by unfold RexWPrefix; decide +kernel) 6 (.sib 4 none 0 (.d32 176)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    refine ⟨h.rip, ?_, ?_⟩
    · change MemWritable s (stackPtr s + 176#64) 8
      simpa only [BitVec.ofNat_eq_ofNat] using h.writable
    · change RangeApart (stackPtr s + 176#64) 8 0x102517 8
      have ha := h.apart 0x2517 8 (by decide +kernel)
      change RangeApart (stackPtr s + 176) 8 (0x102517 : BitVec 64) 8 at ha
      simpa only [BitVec.ofNat_eq_ofNat] using ha
  case av =>
    intro s h
    apply h.avoids_code 0x2517 highWordBytes (by decide +kernel)
    intro c hc a len he
    simp only [movM64R64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · cases he
      exact ⟨rfl, rfl⟩
    · cases he
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0x251f (by decide +kernel))
  advance_then (sub_r64_m64_effect_step 0x10251f 0x48 (by unfold RexWPrefix; decide +kernel) 1 (.sib 4 none 0 (.d32 176)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x102517 highWordBytes 8 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [BitVec.add_zero]
      exact hP.writable.readable
    · apply Effect.Avoids.of_noMem
      simp [subR64M64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x2527 (by decide +kernel))
  advance_then (sar_r64_imm8_effect_step 0x102527 0x48 0xf9 63 (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x102517 highWordBytes 16 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [sarR64Effect_components , Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x252b (by decide +kernel))
  advance_then (mov_r64_r64_effect_step 0x10252b 0x4c 0xfa (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x102517 highWordBytes 20 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x252e (by decide +kernel))
  advance_then (not_r64_effect_step 0x10252e 0x48 0xd2 (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x102517 highWordBytes 23 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x2531 (by decide +kernel))
  advance_then (mov_r64_imm64_effect_step 0x102531 0x48 0xbe (by unfold RexWPrefix; decide +kernel) (by decide +kernel) 0x100000000)
  case sub => exact codeRange_slice_subset 0x102517 highWordBytes 26 10
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x253b (by decide +kernel))
  advance_then (add_r64_r64_effect_step 0x10253b 0x4c 0xfe (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x102517 highWordBytes 36 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x253e (by decide +kernel))
  advance_then (add_r64_r64_effect_step 0x10253e 0x48 0xce (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x102517 highWordBytes 39 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x2541 (by decide +kernel))
  advance_then (or_r64_r64_effect_step 0x102541 0x48 0xd6 (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x102517 highWordBytes 42 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x2544 (by decide +kernel))
  advance_then (shr_r64_imm8_effect_step 0x102544 0x48 0xee 63 (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x102517 highWordBytes 45 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x2548 (by decide +kernel))
  apply AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · rfl
  · x86_norm [highWordEffect, stackPtr, BitVec.add_zero]
    repeat' constructor
  · intro i
    cases i <;> x86_norm [highWordEffect]
  · x86_norm [highWordEffect, stackPtr, BitVec.add_zero]
    rfl

end P256.Proofs.Signing.Wrapper.Entry.Decode.Compare
