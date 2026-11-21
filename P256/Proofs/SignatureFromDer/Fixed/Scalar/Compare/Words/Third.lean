import P256.Proofs.SignatureFromDer.Fixed.Scalar.Compare.Slot
import X86Proofs.Instructions.Dec.Generated.R.Triple
import P256.Proofs.SecretKeyFromBytes.Scalar.Borrow
import P256.Proofs.Common.EffectCompose.Memory

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.SignatureFromDer.Fixed.Scalar.Compare (BorrowSlotPre)
open P256.Proofs.Common.Field.FieldNeg.Instructions (or_r64_r64_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.SignatureFromDer.Fixed.Scalar.Compare

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

attribute [local x86_compose] decR64Effect decSpec

private theorem compareDecLocal (p : BitVec 64) (dst : BitVec 5) :
    Effect.Local (decR64Effect p dst) := by
  refine ⟨fun t t' h => ?_, fun t t' h => ?_, fun t t' h => ?_, fun t t' h i hi => ?_,
    fun t => ?_⟩
  · simp [decR64Effect]
  · simp [decR64Effect, h.read_reg]
  · simp [decR64Effect]
  · cases i <;> simp_all [decR64Effect, decSpec, Effect.flag, StatusFlagsOutcome.get,
      StatusFlags.get, StatusFlagsOutcome.ofStatusFlags, h.read_reg]
  · simp [decR64Effect, Write.Full, Operand.Full]

attribute [local x86_local] compareDecLocal

def thirdWordBytes : List UInt8 :=
  [0x48,0x89,0x54,0x24,0x8,0x48,0x8b,0x54,0x24,0x8,0x48,0xff,0xca,0x48,0xc1,0xea,0x3f,0x4c,0x1,0xea,0x4c,0x89,0xee,0x48,0xf7,0xd6,0x48,0x9,0xd6,0x48,0xc1,0xee,0x3f]

def thirdWordEffect (s : RamState) : Effect :=
  let x := (Operand.reg 13 : Operand 64).read s
  let b := (Operand.reg 2 : Operand 64).read s
  let r := ((b - 1) >>> 63) + x
  { rip := 0x10fb3a
    writes := [⟨(Operand.mem (stackPtr s + 8) : Operand 64), b⟩,
      ⟨(Operand.reg 2 : Operand 64), r⟩,
      ⟨(Operand.reg 6 : Operand 64), (~~~x ||| r) >>> 63⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem third_word_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (BorrowSlotPre 0x10fb19)
      (codeRange 0x10fb19 thirdWordBytes) (Effect.post thirdWordEffect) := by
  advance_begin (mov_m64_r64_effect_step 0x10fb19 0x48 (by unfold RexWPrefix; decide +kernel) 2 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    refine ⟨h.rip, ?_, ?_⟩
    · change MemWritable s (stackPtr s + 8#64) 8
      exact h.writable
    · change RangeApart (stackPtr s + 8#64) 8 0x10fb19 5
      have ha := h.apart 0xfb19 5 (by decide +kernel)
      change RangeApart (stackPtr s + 8) 8 (0x10fb19 : BitVec 64) 5 at ha
      exact ha
  case av =>
    intro s h
    apply h.avoids_code 0xfb19 thirdWordBytes (by decide +kernel)
    intro c hc a len he
    simp only [movM64R64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · cases he
      exact ⟨rfl, rfl⟩
    · cases he
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0xfb1e (by decide +kernel))
  advance_then (mov_r64_m64_effect_step 0x10fb1e 0x48 (by unfold RexWPrefix; decide +kernel) 2 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fb19 thirdWordBytes 5 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [BitVec.add_zero]
      exact hP.writable.readable
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfb23 (by decide +kernel))
  advance_then (dec_r64_effect_step 0x10fb23 0x48 0xca (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fb19 thirdWordBytes 10 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfb26 (by decide +kernel))
  advance_then (shr_r64_imm8_effect_step 0x10fb26 0x48 0xea 63 (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fb19 thirdWordBytes 13 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfb2a (by decide +kernel))
  advance_then (add_r64_r64_effect_step 0x10fb2a 0x4c 0xea (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x10fb19 thirdWordBytes 17 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfb2d (by decide +kernel))
  advance_then (mov_r64_r64_effect_step 0x10fb2d 0x4c 0xee (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x10fb19 thirdWordBytes 20 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfb30 (by decide +kernel))
  advance_then (not_r64_effect_step 0x10fb30 0x48 0xd6 (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fb19 thirdWordBytes 23 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfb33 (by decide +kernel))
  advance_then (or_r64_r64_effect_step 0x10fb33 0x48 0xd6 (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x10fb19 thirdWordBytes 26 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfb36 (by decide +kernel))
  advance_then (shr_r64_imm8_effect_step 0x10fb36 0x48 0xee 63 (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fb19 thirdWordBytes 29 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfb3a (by decide +kernel))
  apply AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · rfl
  · x86_norm [thirdWordEffect, stackPtr, BitVec.add_zero]
    repeat' constructor
  · intro i
    cases i <;> x86_norm [thirdWordEffect]
  · x86_norm [thirdWordEffect, stackPtr, BitVec.add_zero]
    rfl

end P256.Proofs.SignatureFromDer.Fixed.Scalar.Compare
