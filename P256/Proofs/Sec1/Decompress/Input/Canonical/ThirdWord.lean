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

def canonicalThirdSetupBytes : List UInt8 :=
  [0x4c,0x89,0x04,0x24,0x45,0x31,0xc0,0x4c,0x2b,0x04,0x24,0x49,0xc1,0xf8,0x3f]

def canonicalThirdSetupEffect (s : RamState) : Effect :=
  { rip := 0x10fc8f
    writes := [⟨(Operand.mem (stackPtr s) : Operand 64), (Operand.reg 8 : Operand 64).read s⟩,
      ⟨(Operand.reg 8 : Operand 64), (-((Operand.reg 8 : Operand 64).read s)).sshiftRight 63⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem canonical_third_setup_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (BorrowSlotPre 0x10fc80)
      (codeRange 0x10fc80 canonicalThirdSetupBytes) (Effect.post canonicalThirdSetupEffect) := by
  advance_begin (mov_m64_r64_effect_step 0x10fc80 0x4c
    (by unfold RexWPrefix; decide +kernel) 0 (.sib 4 none 0 .none)
    (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    refine ⟨h.rip, ?_, ?_⟩
    · change MemWritable s (stackPtr s + 0#64) 8
      simpa only [BitVec.add_zero] using h.writable
    · change RangeApart (stackPtr s + 0#64) 8 0x10fc80 4
      have ha := h.apart 0xfc80 4 (by decide +kernel)
      change RangeApart (stackPtr s) 8 (0x10fc80 : BitVec 64) 4 at ha
      simpa only [BitVec.add_zero] using ha
  case av =>
    intro s h
    apply h.avoids_code 0xfc80 canonicalThirdSetupBytes (by decide +kernel)
    intro c hc a len he
    simp only [movM64R64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · cases he
      exact ⟨BitVec.add_zero _, rfl⟩
    · cases he
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0xfc84 (by decide +kernel))
  advance_then (xor_r32_r32_rex_effect_step 0x10fc84 0x45 0xc0
    (by unfold RexNoWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x10fc80 canonicalThirdSetupBytes 4 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfc87 (by decide +kernel))
  advance_then (sub_r64_m64_effect_step 0x10fc87 0x4c
    (by unfold RexWPrefix; decide +kernel) 0 (.sib 4 none 0 .none)
    (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fc80 canonicalThirdSetupBytes 7 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [BitVec.add_zero]
      exact hP.writable.readable
    · apply Effect.Avoids.of_noMem
      simp [subR64M64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfc8b (by decide +kernel))
  advance_then (sar_r64_imm8_effect_step 0x10fc8b 0x49 0xf8 63
    (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fc80 canonicalThirdSetupBytes 11 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [sarR64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfc8f (by decide +kernel))
  apply AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · rfl
  · x86_norm [canonicalThirdSetupEffect, stackPtr, BitVec.add_zero]
    change (stackPtr s = (Operand.reg 4 : Operand 64).read s ∧
        (Operand.reg 8 : Operand 64).read s = (Operand.reg 8 : Operand 64).read s) ∧
      (-((Operand.reg 8 : Operand 64).read s)).sshiftRight 63 =
        ((((Operand.reg 8 : Operand 32).read s ^^^ (Operand.reg 8 : Operand 32).read s).setWidth 64) -
          ((Operand.reg 8 : Operand 64).read s)).sshiftRight 63
    simp [BitVec.xor_self, BitVec.zero_sub, stackPtr, Operand.read_reg64]
  · intro i
    cases i <;> x86_norm [canonicalThirdSetupEffect]
  · x86_norm [canonicalThirdSetupEffect, stackPtr, BitVec.add_zero]
    rfl

def canonicalThirdWordBytes : List UInt8 :=
  [0x49,0x01,0xc8,0x48,0xf7,0xd1,0x4c,0x21,0xc1,0x48,0xc1,0xe9,0x3f]

def canonicalThirdWordEffect (s : RamState) : Effect :=
  let x := (Operand.reg 1 : Operand 64).read s
  let r := (Operand.reg 8 : Operand 64).read s + x
  { rip := 0x10fc9c
    writes := [⟨(Operand.reg 8 : Operand 64), r⟩,
      ⟨(Operand.reg 1 : Operand 64), (~~~x &&& r) >>> 63⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem canonical_third_word_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10fc8f)
      (codeRange 0x10fc8f canonicalThirdWordBytes) (Effect.post canonicalThirdWordEffect) := by
  advance_begin (add_r64_r64_effect_step 0x10fc8f 0x49 0xc8
    (by unfold RexWPrefix; decide +kernel) rfl)
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0xfc92 (by decide +kernel))
  advance_then (not_r64_effect_step 0x10fc92 0x48 0xd1
    (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fc8f canonicalThirdWordBytes 3 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfc95 (by decide +kernel))
  advance_then (and_r64_r64_effect_step 0x10fc95 0x4c 0xc1
    (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x10fc8f canonicalThirdWordBytes 6 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfc98 (by decide +kernel))
  advance_then (shr_r64_imm8_effect_step 0x10fc98 0x48 0xe9 63
    (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fc8f canonicalThirdWordBytes 9 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfc9c (by decide +kernel))
  advance_finish [canonicalThirdWordEffect]

end P256.Proofs.Sec1.Decompress.Input
