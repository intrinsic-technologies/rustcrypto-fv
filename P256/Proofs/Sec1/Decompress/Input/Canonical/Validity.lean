import P256.Proofs.Field.Montgomery.Reduction.Slot
import P256.Proofs.Common.EffectCompose.ByteLogic
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Field.Montgomery.Reduction (BorrowSlotPre)
open P256.Proofs.Common.Instructions.ByteLogic (andR8Imm8Effect and_bl_one_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Sec1.Decompress.Input

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def canonicalValidityBytes : List UInt8 :=
  [0x48,0x89,0x04,0x24,0x0f,0xb6,0x1c,0x24,0x80,0xe3,0x01]

def canonicalValidityEffect (s : RamState) : Effect :=
  let x := (Operand.reg 0 : Operand 64).read s
  { rip := 0x10fcd0
    writes := [⟨(Operand.mem (stackPtr s) : Operand 64), x⟩,
      ⟨(Operand.reg 3 : Operand 64), (x.setWidth 8 &&& 1).setWidth 64⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem canonical_validity_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (BorrowSlotPre 0x10fcc5)
      (codeRange 0x10fcc5 canonicalValidityBytes) (Effect.post canonicalValidityEffect) := by
  advance_begin (mov_m64_r64_effect_step 0x10fcc5 0x48
    (by unfold RexWPrefix; decide +kernel) 0 (.sib 4 none 0 .none)
    (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    refine ⟨h.rip, ?_, ?_⟩
    · change MemWritable s (stackPtr s + 0#64) 8
      simpa only [BitVec.add_zero] using h.writable
    · change RangeApart (stackPtr s + 0#64) 8 0x10fcc5 4
      have ha := h.apart 0xfcc5 4 (by decide +kernel)
      change RangeApart (stackPtr s) 8 (0x10fcc5 : BitVec 64) 4 at ha
      simpa only [BitVec.add_zero] using ha
  case av =>
    intro s h
    apply h.avoids_code 0xfcc5 canonicalValidityBytes (by decide +kernel)
    intro c hc a len he
    simp only [movM64R64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · cases he
      exact ⟨BitVec.add_zero _, rfl⟩
    · cases he
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0xfcc9 (by decide +kernel))
  advance_then (movzx_r32_m8_effect_step 0x10fcc9 3 (.sib 4 none 0 .none)
    (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fcc5 canonicalValidityBytes 4 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [BitVec.add_zero]
      change MemReadable s (stackPtr s) 1
      exact ⟨by have h := hP.writable.readable.low; omega,
        fun i hi => hP.writable.readable.mem i (by omega)⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfccd (by decide +kernel))
  advance_then (and_bl_one_effect_step 0x10fccd)
  case sub => exact codeRange_slice_subset 0x10fcc5 canonicalValidityBytes 8 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [andR8Imm8Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfcd0 (by decide +kernel))
  apply AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · rfl
  · x86_norm [canonicalValidityEffect, BitVec.add_zero, stackPtr, Operand.read_reg64]
    change (s.regValue .rsp = s.regValue .rsp + 0 ∧ s.regValue .rax = s.regValue .rax) ∧
      ((s.regValue .rax).setWidth 8 &&& 1).setWidth 64 =
        mergeGPR 8 ((((s.regValue .rax).setWidth 8).setWidth 64).setWidth 8 &&& 1)
          (((s.regValue .rax).setWidth 8).setWidth 64)
    refine ⟨⟨(BitVec.add_zero _).symm, rfl⟩, ?_⟩
    simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64)]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [mergeGPR, show (8 : Nat) ≠ 32 by decide, ↓reduceIte]
    rw [getLsbD_setSlice _ _ _ _ i hi]
    by_cases h : i < 8 <;> simp [BitVec.getLsbD_setWidth, h, hi]
  · intro i
    cases i <;> x86_norm [canonicalValidityEffect]
  · x86_norm [canonicalValidityEffect, BitVec.add_zero, stackPtr, Operand.read_reg64]
    exact BitVec.add_zero _

end P256.Proofs.Sec1.Decompress.Input
