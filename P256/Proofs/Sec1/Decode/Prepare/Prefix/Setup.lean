import P256.Proofs.Sec1.Decode.Prepare.Memory
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Conditions
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decode.Prepare

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field P256.Proofs.Common.Instructions

attribute [local x86_compose] subR64R64Effect gprNumber rexB rexR modrmRm modrmReg
  UInt8.toBitVec_ofNat BitVec.add_zero subSpec condHolds

def setupBytes : List UInt8 :=
  [0x49,0x89,0xff,0xb9,0x41,0,0,0,0x48,0x29,0xd1,0x45,0x31,0xe4,
   0x48,0x83,0xfa,0x41,0xb8,0,0,0,0,0x48,0x0f,0x42,0xc1,0x48,0x8d,0x3c,0x14,
   0x48,0x89,0xf3,0x31,0xf6,0x49,0x89,0xd6,0x48,0x89,0xc2]

def setupEffect (n : Nat) (s : RamState) : Effect :=
  { rip := 0x10e54c
    flags := some ⟨none,none,none,none,none,none⟩
    writes := [⟨(.reg 15 : Operand 64), (Operand.reg 7 : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), BitVec.ofNat 64 (65-n)⟩,
      ⟨(.reg 12 : Operand 64), 0⟩,
      ⟨(.reg 0 : Operand 64), BitVec.ofNat 64 (65-n)⟩,
      ⟨(.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 n⟩,
      ⟨(.reg 3 : Operand 64), (Operand.reg 6 : Operand 64).read s⟩,
      ⟨(.reg 6 : Operand 64), 0⟩,
      ⟨(.reg 14 : Operand 64), BitVec.ofNat 64 n⟩,
      ⟨(.reg 2 : Operand 64), BitVec.ofNat 64 (65-n)⟩] }

set_option maxHeartbeats 1200000 in
theorem setup [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip)
    (n : Nat) (size : n = 1 ∨ n = 33 ∨ n = 65) :
    AdvanceTriple boundary (fun s ↦ s.RIP = 0x10e522 ∧ s.regValue .rdx = BitVec.ofNat 64 n)
      (codeRange 0x10e522 setupBytes) (Effect.post (setupEffect n)) := by
  have next (j : Nat) (hj : j < 118431) :=
    boundary_ne_program outside (inProgram_of_textOffset j hj)
  have h1 := next 0xe525 (by decide)
  have h2 := next 0xe52a (by decide)
  have h3 := next 0xe52d (by decide)
  have h4 := next 0xe530 (by decide)
  have h5 := next 0xe534 (by decide)
  have h6 := next 0xe539 (by decide)
  have h7 := next 0xe53d (by decide)
  have h8 := next 0xe541 (by decide)
  have h10 := next 0xe544 (by decide)
  have h11 := next 0xe546 (by decide)
  have h12 := next 0xe549 (by decide)
  have h13 := next 0xe54c (by decide)
  advance_begin mov_r64_r64_effect_step 0x10e522 0x49 0xff (by simp [RexWPrefix]) rfl
  advance_then mov_r32_imm32_effect_step 0x10e525 0xb9 (by decide) 65
  advance_then sub_r64_r64_effect_step 0x10e52a 0x48 0xd1 (by simp [RexWPrefix]) rfl
  advance_then xor_r32_r32_rex_effect_step 0x10e52d 0x45 0xe4 (by simp [RexNoWPrefix]) rfl
  advance_then cmp_r64_imm8_effect_step 0x10e530 0x48 0xfa 65 (by simp [RexWPrefix]) rfl rfl
  advance_then mov_r32_imm32_effect_step 0x10e534 0xb8 (by decide) 0
  advance_then_on [.CF] using cmov_r64_r64_effect_step 0x10e539 0x48 0x42 0xc1
    (by simp [RexWPrefix]) (.inl rfl) rfl
  case mid =>
    intro s t hp hh ho hf
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem
      (by simp [cmovR64R64Effect, Effect.components, Component.Covers]) _, h7⟩
  advance_then lea_r64_effect_step 0x10e53d 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 (some 2) 0 .none) (by decide) rfl rfl
  advance_then mov_r64_r64_effect_step 0x10e541 0x48 0xf3 (by simp [RexWPrefix]) rfl
  advance_then xor_r32_r32_effect_step 0x10e544 0xf6 rfl
  advance_then mov_r64_r64_effect_step 0x10e546 0x49 0xd6 (by simp [RexWPrefix]) rfl
  advance_then mov_r64_r64_effect_step 0x10e549 0x48 0xc2 (by simp [RexWPrefix]) rfl
  apply AdvanceTriple.block_end
  intro s t hp hh
  apply hh.weaken
  · x86_norm [setupEffect]
  · have hn : (Operand.reg 2 : Operand 64).read s = BitVec.ofNat 64 n := hp.2
    rcases size with rfl | rfl | rfl <;>
      x86_norm [setupEffect, hn, BitVec.xor_self,
        BitVec.reduceToNat, BitVec.reduceOfNat, Nat.reduceSub,
        BitVec.reduceSub, BitVec.reduceToInt, Int.reduceSub,
        BitVec.reduceExtractLsb', Nat.reduceShiftLeft, Nat.reducePow, Nat.reduceMod,
        Nat.reduceLT, ite_true, ite_false, BitVec.shiftLeft_zero, BitVec.zero_add]
    all_goals
      change s.GPR[2] = _ at hn
      simp [Operand.read, gprIndex, hn, cmpSpec] <;> decide +kernel
  · intro flag; cases flag <;> x86_norm [setupEffect]
  · x86_norm [setupEffect]
  all_goals first
    | exact codeRange_slice_subset 0x10e522 setupBytes 3 5
    | exact codeRange_slice_subset 0x10e522 setupBytes 8 3
    | exact codeRange_slice_subset 0x10e522 setupBytes 11 3
    | exact codeRange_slice_subset 0x10e522 setupBytes 14 4
    | exact codeRange_slice_subset 0x10e522 setupBytes 18 5
    | exact codeRange_slice_subset 0x10e522 setupBytes 23 4
    | exact codeRange_slice_subset 0x10e522 setupBytes 27 4
    | exact codeRange_slice_subset 0x10e522 setupBytes 31 3
    | exact codeRange_slice_subset 0x10e522 setupBytes 34 2
    | exact codeRange_slice_subset 0x10e522 setupBytes 36 3
    | exact codeRange_slice_subset 0x10e522 setupBytes 39 3

end P256.Proofs.Sec1.Decode.Prepare
