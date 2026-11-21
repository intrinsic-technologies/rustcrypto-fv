import X86Proofs.Instructions.Dec.Generated.R.Triple
import P256.Proofs.Signing.Wrapper.Entry.Decode.Compare.Borrow
import P256.Proofs.Common.Field.Operations.Neg.Borrow.Or
import P256.Proofs.Common.EffectCompose.Memory

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Signing.Wrapper.Entry.Decode.Compare (BorrowSlotPre)
open P256.Proofs.Common.Field.FieldNeg.Instructions (or_r64_r64_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Signing.Wrapper.Entry.Decode.Compare

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
  [72, 137, 148, 36, 176, 0, 0, 0, 72, 139, 148, 36, 176, 0, 0, 0, 72, 255, 202, 72, 193, 234, 63, 72, 1, 218, 72, 137, 222, 72, 247, 214, 72, 9, 214, 72, 193, 238, 63]

def thirdWordEffect (s : RamState) : Effect :=
  let x := (Operand.reg 3 : Operand 64).read s
  let b := (Operand.reg 2 : Operand 64).read s
  let r := ((b - 1) >>> 63) + x
  { rip := 0x102517
    writes := [⟨(Operand.mem (stackPtr s + 176) : Operand 64), b⟩,
      ⟨(Operand.reg 2 : Operand 64), r⟩,
      ⟨(Operand.reg 6 : Operand 64), (~~~x ||| r) >>> 63⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem third_word_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (BorrowSlotPre 0x1024f0)
      (codeRange 0x1024f0 thirdWordBytes) (Effect.post thirdWordEffect) := by
  advance_begin (mov_m64_r64_effect_step 0x1024f0 0x48 (by unfold RexWPrefix; decide +kernel) 2 (.sib 4 none 0 (.d32 176)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    refine ⟨h.rip, ?_, ?_⟩
    · change MemWritable s (stackPtr s + 176#64) 8
      simpa only [BitVec.ofNat_eq_ofNat] using h.writable
    · change RangeApart (stackPtr s + 176#64) 8 0x1024f0 8
      have ha := h.apart 0x24f0 8 (by decide +kernel)
      change RangeApart (stackPtr s + 176) 8 (0x1024f0 : BitVec 64) 8 at ha
      simpa only [BitVec.ofNat_eq_ofNat] using ha
  case av =>
    intro s h
    apply h.avoids_code 0x24f0 thirdWordBytes (by decide +kernel)
    intro c hc a len he
    simp only [movM64R64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · cases he
      exact ⟨rfl, rfl⟩
    · cases he
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0x24f8 (by decide +kernel))
  advance_then (mov_r64_m64_effect_step 0x1024f8 0x48 (by unfold RexWPrefix; decide +kernel) 2 (.sib 4 none 0 (.d32 176)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1024f0 thirdWordBytes 8 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [BitVec.add_zero]
      exact hP.writable.readable
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x2500 (by decide +kernel))
  advance_then (dec_r64_effect_step 0x102500 0x48 0xca (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1024f0 thirdWordBytes 16 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x2503 (by decide +kernel))
  advance_then (shr_r64_imm8_effect_step 0x102503 0x48 0xea 63 (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1024f0 thirdWordBytes 19 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x2507 (by decide +kernel))
  advance_then (add_r64_r64_effect_step 0x102507 0x48 0xda (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x1024f0 thirdWordBytes 23 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x250a (by decide +kernel))
  advance_then (mov_r64_r64_effect_step 0x10250a 0x48 0xde (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x1024f0 thirdWordBytes 26 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x250d (by decide +kernel))
  advance_then (not_r64_effect_step 0x10250d 0x48 0xd6 (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1024f0 thirdWordBytes 29 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x2510 (by decide +kernel))
  advance_then (or_r64_r64_effect_step 0x102510 0x48 0xd6 (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x1024f0 thirdWordBytes 32 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x2513 (by decide +kernel))
  advance_then (shr_r64_imm8_effect_step 0x102513 0x48 0xee 63 (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1024f0 thirdWordBytes 35 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x2517 (by decide +kernel))
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

end P256.Proofs.Signing.Wrapper.Entry.Decode.Compare
