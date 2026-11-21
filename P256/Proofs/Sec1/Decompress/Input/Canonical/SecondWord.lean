import P256.Proofs.SecretKeyFromBytes.Scalar.Borrow
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
import P256.Proofs.Field.Montgomery.Reduction.Slot

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Field.Montgomery.Reduction (BorrowSlotPre)
open P256.Proofs.Common.Field.Instructions (subR64M64Effect_components sub_r64_m64_effect_step)
open P256.Proofs.Common.Instructions (sarR64Effect_components sar_r64_imm8_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Sec1.Decompress.Input

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def canonicalBorrowSetupBytes : List UInt8 :=
  [0x48,0x89,0x14,0x24,0x48,0x89,0xe2,0x31,0xf6,0x45,0x31,0xc9,
    0x4c,0x2b,0x0c,0x24,0x49,0xc1,0xf9,0x3f]

def canonicalBorrowSetupEffect (s : RamState) : Effect :=
  { rip := 0x10fc66
    writes := [⟨(Operand.mem (stackPtr s) : Operand 64), (Operand.reg 2 : Operand 64).read s⟩,
      ⟨(Operand.reg 2 : Operand 64), stackPtr s⟩,
      ⟨(Operand.reg 6 : Operand 64), 0⟩,
      ⟨(Operand.reg 9 : Operand 64), (-((Operand.reg 2 : Operand 64).read s)).sshiftRight 63⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem canonical_borrow_setup_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (BorrowSlotPre 0x10fc52)
      (codeRange 0x10fc52 canonicalBorrowSetupBytes) (Effect.post canonicalBorrowSetupEffect) := by
  advance_begin (mov_m64_r64_effect_step 0x10fc52 0x48
    (by unfold RexWPrefix; decide +kernel) 2 (.sib 4 none 0 .none)
    (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    refine ⟨h.rip, ?_, ?_⟩
    · change MemWritable s (stackPtr s + 0#64) 8
      simpa only [BitVec.add_zero] using h.writable
    · change RangeApart (stackPtr s + 0#64) 8 0x10fc52 4
      have ha := h.apart 0xfc52 4 (by decide +kernel)
      change RangeApart (stackPtr s) 8 (0x10fc52 : BitVec 64) 4 at ha
      simpa only [BitVec.add_zero] using ha
  case av =>
    intro s h
    apply h.avoids_code 0xfc52 canonicalBorrowSetupBytes (by decide +kernel)
    intro c hc a len he
    simp only [movM64R64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · cases he
      exact ⟨BitVec.add_zero _, rfl⟩
    · cases he
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0xfc56 (by decide +kernel))
  advance_then (mov_r64_r64_effect_step 0x10fc56 0x48 0xe2
    (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x10fc52 canonicalBorrowSetupBytes 4 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfc59 (by decide +kernel))
  advance_then (xor_r32_r32_effect_step 0x10fc59 0xf6 rfl)
  case sub => exact codeRange_slice_subset 0x10fc52 canonicalBorrowSetupBytes 7 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfc5b (by decide +kernel))
  advance_then (xor_r32_r32_rex_effect_step 0x10fc5b 0x45 0xc9
    (by unfold RexNoWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x10fc52 canonicalBorrowSetupBytes 9 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfc5e (by decide +kernel))
  advance_then (sub_r64_m64_effect_step 0x10fc5e 0x4c
    (by unfold RexWPrefix; decide +kernel) 1 (.sib 4 none 0 .none)
    (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fc52 canonicalBorrowSetupBytes 12 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [BitVec.add_zero]
      exact hP.writable.readable
    · apply Effect.Avoids.of_noMem
      simp [subR64M64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfc62 (by decide +kernel))
  advance_then (sar_r64_imm8_effect_step 0x10fc62 0x49 0xf9 63
    (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fc52 canonicalBorrowSetupBytes 16 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [sarR64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfc66 (by decide +kernel))
  apply AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · rfl
  · x86_norm [canonicalBorrowSetupEffect, stackPtr, BitVec.add_zero]
    change (stackPtr s = (Operand.reg 4 : Operand 64).read s ∧
        (Operand.reg 2 : Operand 64).read s = (Operand.reg 2 : Operand 64).read s) ∧
      stackPtr s = (Operand.reg 4 : Operand 64).read s ∧
      (0 : BitVec 64) = (((Operand.reg 6 : Operand 32).read s) ^^^
        ((Operand.reg 6 : Operand 32).read s)).setWidth 64 ∧
      (-((Operand.reg 2 : Operand 64).read s)).sshiftRight 63 =
        ((((Operand.reg 9 : Operand 32).read s ^^^ (Operand.reg 9 : Operand 32).read s).setWidth 64) -
          ((Operand.reg 2 : Operand 64).read s)).sshiftRight 63
    simp [BitVec.xor_self, BitVec.zero_sub, stackPtr, Operand.read_reg64]
  · intro i
    cases i <;> x86_norm [canonicalBorrowSetupEffect]
  · x86_norm [canonicalBorrowSetupEffect, stackPtr, BitVec.add_zero]
    rfl

end P256.Proofs.Sec1.Decompress.Input
