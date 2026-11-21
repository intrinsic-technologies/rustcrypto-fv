import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Conditions
import P256.Proofs.Common.Encoding.Parser.CompressedRoute.Movzx
import P256.Proofs.Program.Code
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
import X86Proofs.Instructions.Inc.Generated.R.Triple

set_option autoImplicit false

open P256.Proofs.Common.Encoding.Parser.CompressedRoute (movzxAlEffect movzx_r32_al_effect_step)
open P256.Proofs.Common.Instructions (cmovR64R64Effect cmov_r64_r64_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.SecretKeyFromBytes.Scalar.Equal

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

attribute [x86_compose] incR64Effect incSpec movzxAlEffect

@[x86_local] theorem incR64Effect_local (p : BitVec 64) (dst : BitVec 5) :
    Effect.Local (incR64Effect p dst) := by
  refine ⟨fun t t' h => rfl, fun t t' h => ?_, fun t t' h => rfl,
    fun t t' h i hi => ?_, fun t => ?_⟩
  · simp [incR64Effect, h.read_reg]
  · cases i <;> simp_all [incR64Effect, incSpec, Effect.flag, StatusFlagsOutcome.get,
      StatusFlags.get, StatusFlagsOutcome.ofStatusFlags, h.read_reg]
  · simp [incR64Effect, Write.Full, Operand.Full]

@[x86_local] theorem movzxAlEffect_local (p : BitVec 64) (dst : BitVec 5) :
    Effect.Local (movzxAlEffect p dst) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro t t' ho
    simp [movzxAlEffect, ho.read_reg]
  · intro t
    simp [movzxAlEffect, Write.Full, Operand.Full]

def loopAddress (s : RamState) (r : BitVec 5) : BitVec 64 :=
  (Operand.reg r : Operand 64).read s + ((Operand.reg 8 : Operand 64).read s <<< 3 + 0)

def loopLimb (s : RamState) (r : BitVec 5) : BitVec 64 :=
  (Operand.mem (loopAddress s r) : Operand 64).read s

structure LoopBodyPre (s : RamState) : Prop where
  rip : s.RIP = 0x119290
  left : MemReadable s (loopAddress s 7) 8
  right : MemReadable s (loopAddress s 2) 8

def loopValue (s : RamState) : BitVec 64 :=
  if loopLimb s 7 = loopLimb s 2 then
    ((Operand.reg 0 : Operand 8).read s).setWidth 64
  else (Operand.reg 1 : Operand 64).read s

def loopEffect (s : RamState) : Effect :=
  { rip := 0x1192a8
    writes := [⟨(Operand.reg 8 : Operand 64), (Operand.reg 8 : Operand 64).read s + 1⟩,
      ⟨(Operand.reg 9 : Operand 64), loopLimb s 7 ^^^ loopLimb s 2⟩,
      ⟨(Operand.reg 10 : Operand 64), loopLimb s 2⟩,
      ⟨(Operand.reg 0 : Operand 64), loopValue s⟩]
    flags := some (.ofStatusFlags (cmpSpec ((Operand.reg 6 : Operand 64).read s)
      ((Operand.reg 8 : Operand 64).read s + 1))) }

def loopBytes : List UInt8 :=
  [0x4e,0x8b,0x0c,0xc7,0x4e,0x8b,0x14,0xc2,0x49,0xff,0xc0,0x0f,0xb6,0xc0,
    0x4d,0x31,0xd1,0x48,0x0f,0x45,0xc1,0x4c,0x39,0xc6]

set_option maxHeartbeats 800000 in
theorem loop_body [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    P256.Proofs.Common.Field.AdvanceTriple boundary LoopBodyPre (codeRange 0x119290 loopBytes)
      (Effect.post loopEffect) := by
  have er8 : gprNumber 0 (rexB (UInt8.toBitVec 0x49)) (modrmRm 0xc0) = 8#5 := by decide +kernel
  have er1 : gprNumber 0 (rexB (UInt8.toBitVec 0x48)) (modrmRm 0xc1) = 1#5 := by decide +kernel
  have ecc : ((UInt8.toBitVec 0x45).extractLsb' 0 4).toNat = 5 := by decide +kernel
  advance_begin (mov_r64_m64_effect_step 0x119290 0x4e (by simp [RexWPrefix])
    9 (.sib 7 (some 8) 3 .none) (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    refine ⟨h.rip, ?_⟩
    x86_norm
    exact h.left
  case next => exact fun _ _ => boundary_ne_program hout (inProgram_of_textOffset 0x19294 (by decide))
  advance_then (mov_r64_m64_effect_step 0x119294 0x4e (by simp [RexWPrefix])
    10 (.sib 2 (some 8) 3 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x119290 loopBytes 4 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.right
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x19298 (by decide))
  advance_then (inc_r64_effect_step 0x119298 0x49 0xc0 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x119290 loopBytes 8 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1929b (by decide))
  advance_then (movzx_r32_al_effect_step 0x11929b 0xc0 rfl rfl)
  case sub => exact codeRange_slice_subset 0x119290 loopBytes 11 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [movzxAlEffect, Effect.components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1929e (by decide))
  advance_then (xor_r64_r64_effect_step 0x11929e 0x4d 0xd1 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x119290 loopBytes 14 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x192a1 (by decide))
  advance_then_on [.ZF] using (cmov_r64_r64_effect_step 0x1192a1 0x48 0x45 0xc1
    (by simp [RexWPrefix]) (Or.inr rfl) rfl)
  case sub => exact codeRange_slice_subset 0x119290 loopBytes 17 4
  case mid =>
    intro s t hP hH hO hF
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [cmovR64R64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x192a5 (by decide))
  advance_then (cmp_r64_r64_effect_step 0x1192a5 0x4c 0xc6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x119290 loopBytes 21 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x192a8 (by decide))
  advance_finish [loopEffect, loopLimb, loopAddress, loopValue,
    er8, er1, ecc, Bool.not_eq_true, beq_iff_eq, BitVec.xor_eq_zero_iff, ite_not]

end P256.Proofs.SecretKeyFromBytes.Scalar.Equal
