import P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.State
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Conditions
import P256.Proofs.Common.Instructions.Bswap
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
import X86Proofs.Instructions.Sub.Generated.Imm8.Triple
import X86Proofs.Instructions.Inc.Generated.R.Triple
import P256.Proofs.Common.Memory.Copy.RegisterOps.Cmov
import P256.Proofs.Common.Field.Operations.Add.Machine.ForgetFlags

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Loop

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Field P256.Proofs.SecretKeyFromBytes.Scalar P256.Proofs.Common.Instructions

open P256.Proofs.Common.Field

theorem incR64Effect_forgetFlags_local (p : BitVec 64) (r : BitVec 5) :
    Effect.Local (fun s => Effect.forgetFlags (incR64Effect p r s)) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [Effect.forgetFlags, incR64Effect, h.read_reg]
  · intro s
    simp [Effect.forgetFlags, incR64Effect, Write.Full, Operand.Full]

attribute [local x86_compose] subR64Imm8Effect subR64R64Effect incR64Effect
  gprNumber rexB rexR modrmRm modrmReg UInt8.toBitVec_ofNat BitVec.add_zero subSpec condHolds
attribute [local x86_local] incR64Effect_forgetFlags_local

theorem subImmediate_local (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) :
    Effect.Local (subR64Imm8Effect p dst imm) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h; simp only [subR64Imm8Effect, h.read_reg]
  · intro s; simp [subR64Imm8Effect, Write.Full, Operand.Full]

attribute [local x86_local] subImmediate_local

structure PreparePre (i : Nat) (s : RamState) : Prop where
  rip : s.RIP = 0x107050
  remaining : (Operand.reg 3 : Operand 64).read s = BitVec.ofNat 64 (32 - 8*i)
  length : (Operand.reg 2 : Operand 64).read s = BitVec.ofNat 64 (32 - 8*i)
  index : (Operand.reg 5 : Operand 64).read s = BitVec.ofNat 64 i
  readable : MemReadable s ((Operand.reg 13 : Operand 64).read s +
    ((Operand.reg 5 : Operand 64).read s <<< 3)) 8
  writable : MemWritable s (rspOf s + 16) 8
  apart : RangeApart (rspOf s + 16) 8 0x107050 53

def prepareBytes : List UInt8 :=
  [0x49, 0x8b, 0x44, 0xed, 0x0, 0x48, 0xf, 0xc8, 0x48, 0x83, 0xeb, 0x8, 0x48, 0x89, 0xdf, 0x49, 0xf, 0x42, 0xfc, 0x48, 0x29, 0xfa, 0xb9, 0x8, 0x0, 0x0, 0x0, 0x48, 0x29, 0xd1, 0x49, 0xf, 0x42, 0xcc, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8d, 0x34, 0xc, 0x48, 0x83, 0xc6, 0x10, 0x48, 0xff, 0xc5, 0x4c, 0x1, 0xf7]

def prepareEffect (i : Nat) (s : RamState) : Effect :=
  { rip := 0x107085
    flags := some ⟨none,none,none,none,none,none⟩
    writes := [
      ⟨(.reg 0 : Operand 64), bswap64 (memLoad s.external
        ((Operand.reg 13 : Operand 64).read s + ((Operand.reg 5 : Operand 64).read s <<< 3)) 64)⟩,
      ⟨(.reg 3 : Operand 64), BitVec.ofNat 64 (24 - 8*i)⟩,
      ⟨(.reg 7 : Operand 64), BitVec.ofNat 64 (24 - 8*i) + (Operand.reg 14 : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), 8⟩,
      ⟨(.reg 1 : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + 16) : Operand 64), bswap64 (memLoad s.external
        ((Operand.reg 13 : Operand 64).read s + ((Operand.reg 5 : Operand 64).read s <<< 3)) 64)⟩,
      ⟨(.reg 6 : Operand 64), rspOf s + 16⟩,
      ⟨(.reg 5 : Operand 64), BitVec.ofNat 64 (i+1)⟩] }

set_option maxHeartbeats 1600000 in
theorem prepare [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip)
    (i : Nat) (hi : i < 4) :
    AdvanceTriple boundary (PreparePre i) (codeRange 0x107050 prepareBytes)
      (Effect.post (prepareEffect i)) := by
  have next (j : Nat) (hj : j < 118431) :=
    boundary_ne_program outside (inProgram_of_textOffset j hj)
  have h1 := next 0x7055 (by decide)
  have h2 := next 0x7058 (by decide)
  have h3 := next 0x705c (by decide)
  have h4 := next 0x705f (by decide)
  have h5 := next 0x7063 (by decide)
  have h6 := next 0x7066 (by decide)
  have h7 := next 0x706b (by decide)
  have h8 := next 0x706e (by decide)
  have h9 := next 0x7072 (by decide)
  have h10 := next 0x7077 (by decide)
  have h11 := next 0x707b (by decide)
  have h12 := next 0x707f (by decide)
  have h13 := next 0x7082 (by decide)
  have h14 := next 0x7085 (by decide)
  advance_begin mov_r64_m64_effect_step 0x107050 0x49 (by simp [RexWPrefix]) 0
    (.sib 13 (some 5) 3 (.d8 0)) (by decide) rfl rfl
  case pre => intro s hp; exact ⟨hp.rip, by simpa [AddrMode.addr, AddrMode.reg64, Disp.value] using hp.readable⟩
  advance_then bswap_r64_effect_step 0x107055 0
  advance_then sub_r64_imm8_effect_step 0x107058 0x48 0xeb 8 (by simp [RexWPrefix]) rfl rfl
  advance_then mov_r64_r64_effect_step 0x10705c 0x48 0xdf (by simp [RexWPrefix]) rfl
  advance_then_on [.CF] using cmov_r64_r64_effect_step 0x10705f 0x49 0x42 0xfc
    (by simp [RexWPrefix]) (Or.inl rfl) rfl
  case mid =>
    intro s t hp hh ho hf
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem
      (by simp [cmovR64R64Effect, Effect.components, Component.Covers]) _, h5⟩
  advance_then sub_r64_r64_effect_step 0x107063 0x48 0xfa (by simp [RexWPrefix]) rfl
  advance_then mov_r32_imm32_effect_step 0x107066 0xb9 (by decide) 8
  advance_then sub_r64_r64_effect_step 0x10706b 0x48 0xd1 (by simp [RexWPrefix]) rfl
  advance_then_on [.CF] using cmov_r64_r64_effect_step 0x10706e 0x49 0x42 0xcc
    (by simp [RexWPrefix]) (Or.inl rfl) rfl
  case mid =>
    intro s t hp hh ho hf
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem
      (by simp [cmovR64R64Effect, Effect.components, Component.Covers]) _, h9⟩
  advance_then mov_m64_r64_effect_step 0x107072 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 16)) (by decide) rfl rfl
  advance_then lea_r64_effect_step 0x107077 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 (some 1) 0 .none) (by decide) rfl rfl
  advance_then add_r64_imm8_effect_step 0x10707b 0x48 0xc6 16 (by simp [RexWPrefix]) rfl rfl
  advance_then (StepEffect.forgetFlags (h := inc_r64_effect_step 0x10707f 0x48 0xc5 (by simp [RexWPrefix]) rfl rfl))
  advance_then add_r64_r64_effect_step 0x107082 0x4c 0xf7 (by simp [RexWPrefix]) rfl
  apply AdvanceTriple.block_end
  intro s t hp hh
  apply hh.weaken
  · x86_norm [prepareEffect]
  · have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    have hr : (Operand.reg (3#5) : Operand 64).read s = BitVec.ofNat 64 (32-8*i) := hp.remaining
    have hl : (Operand.reg (2#5) : Operand 64).read s = BitVec.ofNat 64 (32-8*i) := hp.length
    have hn : (Operand.reg (5#5) : Operand 64).read s = BitVec.ofNat 64 i := hp.index
    rcases cases with rfl | rfl | rfl | rfl <;>
      x86_norm [prepareEffect, BitVec.reduceExtractLsb', BitVec.reduceToNat,
        Nat.reduceShiftLeft, Nat.reduceAdd, BitVec.reduceOfNat, BitVec.reduceSub,
        BitVec.reduceNeg, hr, hl, hn, Nat.reduceMul,
        Nat.reduceSub, Nat.reduceLT, Nat.reducePow, Nat.reduceMod,
        BitVec.reduceToInt, Int.reduceSub, Bool.false_eq_true, ite_false,
        Bool.true_eq_false, ite_true, BitVec.reduceAdd, BitVec.zero_add,
        BitVec.sub_self, BitVec.shiftLeft_zero]
  · intro flag; cases flag <;> x86_norm [prepareEffect]
  · x86_norm [prepareEffect]
  all_goals try (first
    | exact codeRange_slice_subset 0x107050 prepareBytes 5 3
    | exact codeRange_slice_subset 0x107050 prepareBytes 8 4
    | exact codeRange_slice_subset 0x107050 prepareBytes 12 3
    | exact codeRange_slice_subset 0x107050 prepareBytes 15 4
    | exact codeRange_slice_subset 0x107050 prepareBytes 19 3
    | exact codeRange_slice_subset 0x107050 prepareBytes 22 5
    | exact codeRange_slice_subset 0x107050 prepareBytes 27 3
    | exact codeRange_slice_subset 0x107050 prepareBytes 30 4
    | exact codeRange_slice_subset 0x107050 prepareBytes 34 5
    | exact codeRange_slice_subset 0x107050 prepareBytes 39 4
    | exact codeRange_slice_subset 0x107050 prepareBytes 43 4
    | exact codeRange_slice_subset 0x107050 prepareBytes 47 3
    | exact codeRange_slice_subset 0x107050 prepareBytes 50 3)
  all_goals
    intro s t hp hh ho
    refine ⟨?_, Effect.Local.avoids (by x86_local) (ho true) ?_, ?_⟩
    · refine StorePre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_ ?_
      · x86_norm; exact hp.writable
      · x86_norm; intro a ha b hb he
        apply hp.apart a ha (34+b) (by omega)
        simpa [BitVec.ofNat_add, ← BitVec.add_assoc, rspOf] using he
    · apply Effect.avoids_codeRange
      x86_norm
      simpa [prepareBytes, rspOf] using hp.apart
    · x86_norm
      exact h10

end P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Loop
