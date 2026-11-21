import P256.Proofs.Field.Subtract.Correction
import P256.Proofs.Signing.Core.Iteration.Components.Addition.Sum.Arithmetic
import P256.Proofs.Field.Add.Sum
import P256.Proofs.Common.Instructions.Setb
import P256.Proofs.Field.Representation
import P256.Proofs.Common.EffectCompose.Conditions
import P256.Proofs.Common.Instructions.MovzxByte
import P256.Proofs.Common.Instructions.ByteOps.Effects

set_option autoImplicit false

open P256.Proofs.Program

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Field.Montgomery.Reduction
open P256.Proofs.Common.Instructions (add_r64_m64_effect_step)
open P256.Proofs.Common.Instructions.Carry (adc_r64_imm8_effect_step adc_r64_r64_effect_step)
open P256.Proofs.Common.Instructions.Setb (setccM8Effect setcc_r8_effect_step setcc_r8_rex_effect_step setcc_m8_effect_step)
open P256.Proofs.Common.Instructions.MovzxByte (movzx_r32_r8_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Signing.Core.Iteration.Components.Addition.Sum

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem setb_extend_value (b : Bool) :
    ((if b then 1#8 else 0#8).setWidth 64) = BitVec.ofNat 64 b.toNat := by
  cases b <;> rfl

structure BlockPre (s : RamState) : Prop where
  rip : s.RIP = 0x11392e
  left : ∀ i ∈ [0, 8, 16, 24], MemReadable s ((Operand.reg 6 : Operand 64).read s + i) 8
  right : ∀ i ∈ [0, 8, 16, 24], MemReadable s ((Operand.reg 2 : Operand 64).read s + i) 8
  writable : MemWritable s (stackPtr s + 15) 1
  apart : ∀ offset len : Nat, offset + len ≤ 118431 →
    RangeApart (stackPtr s + 15) 1 (Extracted.textAddress + BitVec.ofNat 64 offset) len

def bytes : List UInt8 :=
  [0x4c,0x8b,0x1a,0x4c,0x8b,0x4a,0x10,0x4c,0x03,0x1e,0x4c,0x8b,0x56,0x08,
   0x49,0x83,0xd2,0x00,0x0f,0x92,0xc0,0x45,0x31,0xc0,0x4c,0x03,0x4e,0x10,
   0x41,0x0f,0x92,0xc0,0x4c,0x8b,0x72,0x18,0x31,0xdb,0x4c,0x03,0x76,0x18,
   0x0f,0xb6,0xc0,0x0f,0x92,0xc3,0x4c,0x03,0x52,0x08,0x49,0x11,0xc1,
   0x4d,0x11,0xf0,0x0f,0x92,0x44,0x24,0x0f,0x49,0x89,0xdc,0x49,0x83,0xd4,0x00]

def effect (s : RamState) : Effect :=
  let a := P256.Proofs.Field.readLimbs s ((Operand.reg 6 : Operand 64).read s)
  let b := P256.Proofs.Field.readLimbs s ((Operand.reg 2 : Operand 64).read s)
  { rip := 0x113974
    writes := [⟨(Operand.reg 0 : Operand 64), BitVec.ofNat 64 (secondCarry a b).toNat⟩,
      ⟨(Operand.reg 3 : Operand 64), BitVec.ofNat 64 (carry b.l3 a.l3 false).toNat⟩,
      ⟨(Operand.reg 8 : Operand 64), high a b⟩,
      ⟨(Operand.reg 9 : Operand 64), third a b⟩,
      ⟨(Operand.reg 10 : Operand 64), second a b⟩,
      ⟨(Operand.reg 11 : Operand 64), low a b⟩,
      ⟨(Operand.reg 12 : Operand 64), extendedCarry a b⟩,
      ⟨(Operand.reg 14 : Operand 64), highInput a b⟩,
      ⟨(Operand.mem (stackPtr s + 15) : Operand 8), if highCarry a b then 1 else 0⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

set_option maxHeartbeats 1600000 in
theorem correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary BlockPre (codeRange 0x11392e bytes) (Effect.post effect) := by
  advance_begin (mov_r64_m64_effect_step 0x11392e 0x4c (by simp [RexWPrefix]) 3 (.base 2 .none) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.right 0 (by simp)⟩
  case next =>
    intro s hP
    exact boundary_ne_program hout (inProgram_of_textOffset 0x13931 (by decide))
  advance_then (mov_r64_m64_effect_step 0x113931 0x4c (by simp [RexWPrefix]) 1 (.base 2 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11392e bytes 3 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.right 16 (by simp)
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13935 (by decide))
  advance_then (add_r64_m64_effect_step 0x113935 0x4c (by simp [RexWPrefix]) 3 (.base 6 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11392e bytes 7 3
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.left 0 (by simp)
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13938 (by decide))
  advance_then (mov_r64_m64_effect_step 0x113938 0x4c (by simp [RexWPrefix]) 2 (.base 6 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11392e bytes 10 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.left 8 (by simp)
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1393c (by decide))
  advance_then_on [.CF] using (adc_r64_imm8_effect_step 0x11393c 0x49 0xd2 0 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11392e bytes 14 4
  case mid =>
    intro s t hP hH hO hF
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13940 (by decide))
  advance_then_on [.CF] using (setcc_r8_effect_step 0x113940 0x92 0xc0 (.inl rfl) rfl (by decide))
  case sub => exact codeRange_slice_subset 0x11392e bytes 18 3
  case mid =>
    intro s t hP hH hO hF
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13943 (by decide))
  advance_then (xor_r32_r32_rex_effect_step 0x113943 0x45 0xc0 (by simp [RexNoWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x11392e bytes 21 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13946 (by decide))
  advance_then (add_r64_m64_effect_step 0x113946 0x4c (by simp [RexWPrefix]) 1 (.base 6 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11392e bytes 24 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.left 16 (by simp)
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1394a (by decide))
  advance_then_on [.CF] using (setcc_r8_rex_effect_step 0x11394a 0x41 0x92 0xc0 (by simp [RexPrefix]) (.inl rfl) rfl)
  case sub => exact codeRange_slice_subset 0x11392e bytes 28 4
  case mid =>
    intro s t hP hH hO hF
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1394e (by decide))
  advance_then (mov_r64_m64_effect_step 0x11394e 0x4c (by simp [RexWPrefix]) 6 (.base 2 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11392e bytes 32 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.right 24 (by simp)
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13952 (by decide))
  advance_then (xor_r32_r32_effect_step 0x113952 0xdb rfl)
  case sub => exact codeRange_slice_subset 0x11392e bytes 36 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13954 (by decide))
  advance_then (add_r64_m64_effect_step 0x113954 0x4c (by simp [RexWPrefix]) 6 (.base 6 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11392e bytes 38 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.left 24 (by simp)
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13958 (by decide))
  advance_then (movzx_r32_r8_effect_step 0x113958 0xc0 rfl (by decide))
  case sub => exact codeRange_slice_subset 0x11392e bytes 42 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1395b (by decide))
  advance_then_on [.CF] using (setcc_r8_effect_step 0x11395b 0x92 0xc3 (.inl rfl) rfl (by decide))
  case sub => exact codeRange_slice_subset 0x11392e bytes 45 3
  case mid =>
    intro s t hP hH hO hF
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1395e (by decide))
  advance_then (add_r64_m64_effect_step 0x11395e 0x4c (by simp [RexWPrefix]) 2 (.base 2 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11392e bytes 48 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.right 8 (by simp)
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13962 (by decide))
  advance_then_on [.CF] using (adc_r64_r64_effect_step 0x113962 0x49 0xc1 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x11392e bytes 52 3
  case mid =>
    intro s t hP hH hO hF
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13965 (by decide))
  advance_then_on [.CF] using (adc_r64_r64_effect_step 0x113965 0x4d 0xf0 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x11392e bytes 55 3
  case mid =>
    intro s t hP hH hO hF
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13968 (by decide))
  advance_then_on [.CF] using (show StepEffect _ _ (setccM8Effect 0x113968 5 (.sib 4 none 0 (.d8 15)) 2) from setcc_m8_effect_step 0x113968 0x92 (.inl rfl) 0 (.sib 4 none 0 (.d8 15)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11392e bytes 58 5
  case mid =>
    intro s t hP hH hO hF
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable
    · x86_norm [stackPtr]
      exact hP.apart 0x13968 5 (by decide)
    · apply P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids
        (by simp (config := { decide := true }) only [x86_local_on]) (hO true) (hF true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hP.apart 0x1392e 70 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1396d (by decide))
  advance_then (mov_r64_r64_effect_step 0x11396d 0x49 0xdc (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x11392e bytes 63 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13970 (by decide))
  advance_then_on [.CF] using (adc_r64_imm8_effect_step 0x113970 0x49 0xd4 0 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11392e bytes 66 4
  case mid =>
    intro s t hP hH hO hF
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13974 (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [effect]
  · x86_norm [effect, low, secondInput, secondCarry, thirdInput, highInput, second,
      third, thirdCarry, high, highCarry, extendedCarry, P256.Proofs.Field.readLimbs,
      P256.Proofs.Field.Montgomery.Reduction.adcSpec_ofBool,
      P256.Proofs.Field.Montgomery.Reduction.adcSpec_cf_ofBool,
      P256.Proofs.Field.Montgomery.Reduction.addSpec_cf_carry,
      P256.Proofs.Field.Subtract.setb_zero_value, adc,
      P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8, gprNumber, rexR, rexB, modrmReg, modrmRm,
      UInt8.toBitVec_ofNat, gprIndex, BitVec.add_zero, BitVec.reduceExtractLsb', BitVec.reduceToNat, BitVec.xor_self, BitVec.setWidth_zero,
      setb_extend_value, Bool.toNat_false, stackPtr]
    repeat first | apply And.intro | exact Or.inl rfl | apply Or.inr | rfl
  · intro i
    cases i <;> exact .inl rfl
  · x86_norm [effect, stackPtr]
    repeat first | apply And.intro | exact Or.inl rfl | apply Or.inr | rfl

end P256.Proofs.Signing.Core.Iteration.Components.Addition.Sum
