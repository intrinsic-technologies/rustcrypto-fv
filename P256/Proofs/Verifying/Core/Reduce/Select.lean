import P256.Proofs.Verifying.Core.Reduce.BlockPre
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Encoding.Serialize.Tail.ByteOps.Store
import P256.Proofs.Common.Field.Operations.Select.TestAl
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple testAlEffect test_al_al_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)
open P256.Proofs.Common.Instructions (mov_m8_r8_legacy_effect_step cmovR64R64Effect cmovR64R64Value cmov_r64_r64_effect_step)

namespace P256.Proofs.Verifying.Core.Reduce

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem test_al_local (p : BitVec 64) : Effect.Local (testAlEffect p) := by
  refine ⟨fun t t' h => ?_, fun t t' h => ?_, fun t t' h => ?_, fun t t' h i hi => ?_, fun t => ?_⟩
  · simp [testAlEffect]
  · simp [testAlEffect]
  · simp [testAlEffect]
  · cases i <;> simp [testAlEffect, testFlags, Effect.flag, StatusFlagsOutcome.get, h.read_reg]
  · simp [testAlEffect]

attribute [local x86_compose] testAlEffect testFlags cmovR64R64Effect cmovR64R64Value
attribute [local x86_local] test_al_local

structure SelectionPre (s : RamState) : Prop where
  rip : s.RIP = 0x113204
  writable : MemWritable s (stackPtr s + 7) 1
  readable : ∀ offset ∈ [7,16,24,32], MemReadable s (stackPtr s + BitVec.ofNat 64 offset) (if offset=7 then 1 else 8)
  apart : ∀ codeOffset codeLen, codeOffset + codeLen ≤ 118431 →
    RangeApart (stackPtr s + 7) 1 (Extracted.textAddress + BitVec.ofNat 64 codeOffset) codeLen

def selectionBytes : List UInt8 :=
  [0x88,0x44,0x24,0x7,0x48,0x8d,0x44,0x24,0x7,0xf,0xb6,0x44,0x24,0x7,0x48,0x8b,0x4c,0x24,0x18,0x48,0x8b,0x54,0x24,0x10,0x84,0xc0,0x48,0xf,0x45,0xca,0x84,0xc0,0x4d,0xf,0x45,0xe5,0x84,0xc0,0x49,0xf,0x45,0xef,0x84,0xc0,0x49,0xf,0x45,0xde,0x48,0x8b,0x44,0x24,0x20]

def selectionEffect (s : RamState) : Effect :=
  let al := (Operand.reg 0 : Operand 8).read s
  { rip := 0x113239
    writes := [⟨(Operand.mem (stackPtr s+7) : Operand 8), al⟩,
      ⟨(Operand.reg 0 : Operand 64), (Operand.mem (stackPtr s+32) : Operand 64).read s⟩,
      ⟨(Operand.reg 1 : Operand 64), if al = 0 then (Operand.mem (stackPtr s+24) : Operand 64).read s else (Operand.mem (stackPtr s+16) : Operand 64).read s⟩,
      ⟨(Operand.reg 2 : Operand 64), (Operand.mem (stackPtr s+16) : Operand 64).read s⟩,
      ⟨(Operand.reg 12 : Operand 64), if al = 0 then (Operand.reg 12 : Operand 64).read s else (Operand.reg 13 : Operand 64).read s⟩,
      ⟨(Operand.reg 5 : Operand 64), if al = 0 then (Operand.reg 5 : Operand 64).read s else (Operand.reg 15 : Operand 64).read s⟩,
      ⟨(Operand.reg 3 : Operand 64), if al = 0 then (Operand.reg 3 : Operand 64).read s else (Operand.reg 14 : Operand 64).read s⟩]
    flags := some (testFlags al) }

set_option maxHeartbeats 800000 in
theorem selection_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary SelectionPre (codeRange 0x113204 selectionBytes) (Effect.post selectionEffect) := by
  advance_begin (show StepEffect _ _ (fun s => storeEffect 0x113204 4 (fun t => stackPtr t + 7) (fun t => (Operand.reg 0 : Operand 8).read t) s) from mov_m8_r8_legacy_effect_step 0x113204 0 (by decide) (.sib 4 none 0 (.d8 7)) (by decide) rfl rfl)
  case pre =>
    intro s hP
    exact ⟨hP.rip,hP.writable,hP.apart 0x13204 4 (by decide)⟩
  case next => exact fun _ _ => boundary_ne_program hout (inProgram_of_textOffset 0x13208 (by decide))
  case av =>
    intro s hP
    apply Effect.avoids_codeRange
    x86_norm
    exact hP.apart 0x13204 53 (by decide)
  advance_then (lea_r64_effect_step 0x113208 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 7)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113204 selectionBytes 4 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1320d (by decide))
  advance_then (movzx_r32_m8_effect_step 0x11320d 0 (.sib 4 none 0 (.d8 7)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113204 selectionBytes 9 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 7 (by decide)
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13212 (by decide))
  advance_then (mov_r64_m64_effect_step 0x113212 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 24)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113204 selectionBytes 14 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 24 (by decide)
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13217 (by decide))
  advance_then (mov_r64_m64_effect_step 0x113217 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 16)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113204 selectionBytes 19 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 16 (by decide)
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1321c (by decide))
  advance_then (test_al_al_effect_step 0x11321c)
  case sub => exact codeRange_slice_subset 0x113204 selectionBytes 24 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1321e (by decide))
  advance_then_on [.ZF] using (show StepEffect _ _ (cmovR64R64Effect 0x11321e 5 1 2) from cmov_r64_r64_effect_step 0x11321e 0x48 0x45 0xca (by simp [RexWPrefix]) (Or.inr rfl) rfl)
  case sub => exact codeRange_slice_subset 0x113204 selectionBytes 26 4
  case mid =>
    intro s t hP hH hO hF
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13222 (by decide))
  advance_then (test_al_al_effect_step 0x113222)
  case sub => exact codeRange_slice_subset 0x113204 selectionBytes 30 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13224 (by decide))
  advance_then_on [.ZF] using (show StepEffect _ _ (cmovR64R64Effect 0x113224 5 12 13) from cmov_r64_r64_effect_step 0x113224 0x4d 0x45 0xe5 (by simp [RexWPrefix]) (Or.inr rfl) rfl)
  case sub => exact codeRange_slice_subset 0x113204 selectionBytes 32 4
  case mid =>
    intro s t hP hH hO hF
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13228 (by decide))
  advance_then (test_al_al_effect_step 0x113228)
  case sub => exact codeRange_slice_subset 0x113204 selectionBytes 36 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1322a (by decide))
  advance_then_on [.ZF] using (show StepEffect _ _ (cmovR64R64Effect 0x11322a 5 5 15) from cmov_r64_r64_effect_step 0x11322a 0x49 0x45 0xef (by simp [RexWPrefix]) (Or.inr rfl) rfl)
  case sub => exact codeRange_slice_subset 0x113204 selectionBytes 38 4
  case mid =>
    intro s t hP hH hO hF
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1322e (by decide))
  advance_then (test_al_al_effect_step 0x11322e)
  case sub => exact codeRange_slice_subset 0x113204 selectionBytes 42 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13230 (by decide))
  advance_then_on [.ZF] using (show StepEffect _ _ (cmovR64R64Effect 0x113230 5 3 14) from cmov_r64_r64_effect_step 0x113230 0x49 0x45 0xde (by simp [RexWPrefix]) (Or.inr rfl) rfl)
  case sub => exact codeRange_slice_subset 0x113204 selectionBytes 44 4
  case mid =>
    intro s t hP hH hO hF
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13234 (by decide))
  advance_then (mov_r64_m64_effect_step 0x113234 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 32)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113204 selectionBytes 48 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 32 (by decide)
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13239 (by decide))
  advance_finish [selectionEffect, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, Bool.not_eq_true, beq_iff_eq, ite_not, gprNumber, modrmReg, rexR, rexB, stackPtr, Operand.read_reg64, BitVec.ofNat_eq_ofNat]

end P256.Proofs.Verifying.Core.Reduce
