import P256.Proofs.Projective.Multiply.Machine.Loop.Initial.Setup
import X86Proofs.Instructions.Dec.Generated.R.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Projective.Multiply.Machine.Loop.Round

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs

attribute [local x86_compose] decR64Effect decSpec

theorem dec_local (p : BitVec 64) (dst : BitVec 5) : Effect.Local (decR64Effect p dst) := by
  refine ⟨fun t t' h => ?_, fun t t' h => ?_, fun t t' h => ?_, fun t t' h i hi => ?_, fun t => ?_⟩
  · simp [decR64Effect]
  · simp [decR64Effect, h.read_reg]
  · simp [decR64Effect]
  · cases i <;> simp_all [decR64Effect, decSpec, Effect.flag, StatusFlagsOutcome.get,
      StatusFlags.get, StatusFlagsOutcome.ofStatusFlags, h.read_reg]
  · simp [decR64Effect, Write.Full, Operand.Full]

attribute [local x86_local] dec_local

structure AfterDoublePre (s : RamState) : Prop where
  rip : s.RIP = 0x103368
  writable : P256.Proofs.Common.Instructions.CrossPageStore.Writable s (stackPtr s + 32) 8
  apart : RangeApart (stackPtr s + 32) 8 0x103368 24
def afterDoubleBytes : List UInt8 :=
  [72, 137, 232, 73, 255, 207, 76, 137, 124, 36, 32, 73, 137, 223, 49, 219, 76, 141, 164, 36, 136, 0, 0, 0]

def afterDoubleEffect (s : RamState) : Effect :=
  { rip := 0x103380
    writes := [⟨(Operand.reg 0 : Operand 64), s.regValue .rbp⟩,
      ⟨(Operand.mem (stackPtr s + 32) : Operand 64), s.regValue .r15 - 1⟩,
      ⟨(Operand.reg 15 : Operand 64), s.regValue .rbx⟩,
      ⟨(Operand.reg 3 : Operand 64), 0⟩,
      ⟨(Operand.reg 12 : Operand 64), stackPtr s + 136⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem afterDouble_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary AfterDoublePre (codeRange 0x103368 afterDoubleBytes)
      (Effect.post afterDoubleEffect) := by
  advance_begin (mov_r64_r64_effect_step 0x103368 0x48 0xe8 (by simp [RexWPrefix]) rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x336b (by decide))
  advance_then (dec_r64_effect_step 0x10336b 0x49 0xcf (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x103368 afterDoubleBytes 3 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x336e (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10336e 0x4c (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x103368 afterDoubleBytes 6 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable
    · x86_norm
      intro i hi j hj he
      apply hP.apart i hi (6+j) (by omega)
      change stackPtr s + (32 : BitVec 64) + BitVec.ofNat 64 i = _ at he
      simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.reduceAdd] using he
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x3373 (by decide))
  advance_then (mov_r64_r64_effect_step 0x103373 0x49 0xdf (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x103368 afterDoubleBytes 11 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x3376 (by decide))⟩
  advance_then (xor_r32_r32_effect_step 0x103376 0xdb rfl)
  case sub => exact codeRange_slice_subset 0x103368 afterDoubleBytes 14 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x3378 (by decide))⟩
  advance_then (lea_r64_effect_step 0x103378 0x4c (by simp [RexWPrefix]) 4 (.sib 4 none 0 (.d32 136)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x103368 afterDoubleBytes 16 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x3380 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [afterDoubleEffect, BitVec.shiftLeft_zero, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
    all_goals simp [gprNumber, modrmRm, modrmReg]
  · x86_norm [afterDoubleEffect, BitVec.shiftLeft_zero, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
    all_goals simp [gprNumber, modrmRm, modrmReg]
  · intro i; cases i <;> x86_norm [afterDoubleEffect, BitVec.shiftLeft_zero, BitVec.add_zero]
  · x86_norm [afterDoubleEffect, BitVec.shiftLeft_zero, BitVec.add_zero]
    all_goals (repeat first | constructor | rfl)
    all_goals simp [gprNumber, modrmRm, modrmReg]

end P256.Proofs.Projective.Multiply.Machine.Loop.Round
