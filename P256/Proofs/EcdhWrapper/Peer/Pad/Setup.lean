import P256.Proofs.EcdhWrapper.Peer.Guards
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Conditions
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Add.Generated.Imm32.Triple

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Peer.Pad

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field P256.Proofs.Common.Instructions

attribute [local x86_compose] subR64R64Effect gprNumber rexB rexR modrmRm modrmReg
  UInt8.toBitVec_ofNat BitVec.add_zero subSpec condHolds

def setupBytes : List UInt8 :=
  [0xb8,0x41,0,0,0,0x48,0x29,0xe8,0x31,0xd2,0x48,0x83,0xfd,0x41,
   0x48,0x0f,0x42,0xd0,0x48,0x8d,0x3c,0x2c,0x48,0x81,0xc7,0xa8,0,0,0,0x31,0xf6]

def setupEffect (n : Nat) (s : RamState) : Effect :=
  { rip := 0x106a23
    flags := some ⟨none,none,none,none,none,none⟩
    writes := [⟨(.reg 0 : Operand 64), BitVec.ofNat 64 (65-n)⟩,
      ⟨(.reg 2 : Operand 64), BitVec.ofNat 64 (65-n)⟩,
      ⟨(.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 n + 168⟩,
      ⟨(.reg 6 : Operand 64), 0⟩] }

theorem setup [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip)
    (n : Nat) (size : n = 1 ∨ n = 33 ∨ n = 65) :
    AdvanceTriple boundary (fun s ↦ s.RIP = 0x106a04 ∧ s.regValue .rbp = BitVec.ofNat 64 n)
      (codeRange 0x106a04 setupBytes) (Effect.post (setupEffect n)) := by
  have next (j : Nat) (hj : j < 118431) :=
    boundary_ne_program outside (inProgram_of_textOffset j hj)
  have h1 := next 0x6a09 (by decide)
  have h2 := next 0x6a0c (by decide)
  have h3 := next 0x6a0e (by decide)
  have h4 := next 0x6a12 (by decide)
  have h5 := next 0x6a16 (by decide)
  have h6 := next 0x6a1a (by decide)
  have h7 := next 0x6a21 (by decide)
  have h8 := next 0x6a23 (by decide)
  advance_begin mov_r32_imm32_effect_step 0x106a04 0xb8 (by decide) 65
  advance_then sub_r64_r64_effect_step 0x106a09 0x48 0xe8 (by simp [RexWPrefix]) rfl
  advance_then xor_r32_r32_effect_step 0x106a0c 0xd2 rfl
  advance_then cmp_r64_imm8_effect_step 0x106a0e 0x48 0xfd 65 (by simp [RexWPrefix]) rfl rfl
  advance_then_on [.CF] using cmov_r64_r64_effect_step 0x106a12 0x48 0x42 0xd0
    (by simp [RexWPrefix]) (.inl rfl) rfl
  case mid =>
    intro s t hp hh ho hf
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem
      (by simp [cmovR64R64Effect, Effect.components, Component.Covers]) _, h5⟩
  advance_then lea_r64_effect_step 0x106a16 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 (some 5) 0 .none) (by decide) rfl rfl
  advance_then add_r64_imm32_effect_step 0x106a1a 0x48 0xc7 168
    (by simp [RexWPrefix]) rfl rfl
  advance_then xor_r32_r32_effect_step 0x106a21 0xf6 rfl
  apply AdvanceTriple.block_end
  intro s t hp hh
  apply hh.weaken
  · x86_norm [setupEffect]
  · have hn : (Operand.reg 5 : Operand 64).read s = BitVec.ofNat 64 n := hp.2
    rcases size with rfl | rfl | rfl <;>
      x86_norm [setupEffect, hn, BitVec.xor_self,
        BitVec.reduceToNat, BitVec.reduceOfNat, Nat.reduceSub,
        BitVec.reduceSub, BitVec.reduceToInt, Int.reduceSub,
        BitVec.reduceExtractLsb', Nat.reduceShiftLeft, Nat.reducePow, Nat.reduceMod,
        Nat.reduceLT, ite_true, ite_false, BitVec.shiftLeft_zero, BitVec.zero_add]
    all_goals
      change s.GPR[5] = _ at hn
      change _ = 65#64 - BitVec.setWidth 64 s.GPR[5] ∧
        (_ = if (cmpSpec (BitVec.setWidth 64 s.GPR[5]) 65).CF = true then 65#64 - BitVec.setWidth 64 s.GPR[5] else 0) ∧
        _ = BitVec.setWidth 64 s.GPR[5] + 168
      rw [hn]
      decide +kernel
  · intro flag; cases flag <;> x86_norm [setupEffect]
  · x86_norm [setupEffect]
  all_goals first
    | exact codeRange_slice_subset 0x106a04 setupBytes 5 3
    | exact codeRange_slice_subset 0x106a04 setupBytes 8 2
    | exact codeRange_slice_subset 0x106a04 setupBytes 10 4
    | exact codeRange_slice_subset 0x106a04 setupBytes 14 4
    | exact codeRange_slice_subset 0x106a04 setupBytes 18 4
    | exact codeRange_slice_subset 0x106a04 setupBytes 22 7
    | exact codeRange_slice_subset 0x106a04 setupBytes 29 2

end P256.Proofs.EcdhWrapper.Peer.Pad
