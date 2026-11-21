import Sha1.Proofs.Compress.Machine.Run
import Sha1.Proofs.Compress.Rounds.Scalar
import Sha1.Proofs.Common.Instructions.MovStore.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Mov.Generated.RM.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RM.Triple
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import X86Proofs.Instructions.Add.Generated.AccImm32.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Or.Generated.RR.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.Lea.Generated.RM.Triple

namespace Sha1.Proofs.Compress.Machine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Spec.Program
open Standards.NIST.SHA1 Standards.NIST.SHA2.SHA256 Sha1.Proofs.Compress.Rounds

attribute [local irreducible] workingAfter scheduleWord messageSchedule

def bytes051 : List UInt8 :=
  [0x4c, 0x8b, 0x54, 0x24, 0x38, 0x45, 0x31, 0xd7, 0x44, 0x33, 0x6c, 0x24, 0x8, 0x44, 0x33, 0x3c,
    0x24, 0x4c, 0x8b, 0x5c, 0x24, 0x48, 0x45, 0x31, 0xdf, 0x41, 0xd1, 0xc7, 0x41, 0x31, 0xed, 0x44,
    0x33, 0x6c, 0x24, 0x30, 0x41, 0xd1, 0xc5, 0xc1, 0xc7, 0x1e, 0x41, 0x89, 0xf9, 0x41, 0x31, 0xd1,
    0x41, 0x21, 0xf1, 0x46, 0x8d, 0x4, 0x2a, 0x21, 0xfa, 0x44, 0x31, 0xca]

set_option maxHeartbeats 800000 in
def effect051 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    ((movR64M64Effect 0x102fc0 10 (.sib 4 none 0 (.d8 0x38)))) (xorR32R32Effect 0x102fc5 3 15 10))
    (xorR32M32Effect 0x102fc8 13 (.sib 4 none 0 (.d8 0x8)))) (xorR32M32Effect 0x102fcd 15 (.sib 4
    none 0 .none))) (movR64M64Effect 0x102fd1 11 (.sib 4 none 0 (.d8 0x48)))) (xorR32R32Effect
    0x102fd6 3 15 11)) (rolR32Effect 0x102fd9 3 15 1)) (xorR32R32Effect 0x102fdc 3 13 5))
    (xorR32M32Effect 0x102fdf 13 (.sib 4 none 0 (.d8 0x30)))) (rolR32Effect 0x102fe4 3 13 1))
    (rolR32Effect 0x102fe7 3 7 30)) (movR32R32Effect 0x102fea 3 9 7)) (xorR32R32Effect 0x102fed 3 9
    2)) (andR32R32Effect 0x102ff0 3 9 6)) (leaR32Effect 0x102ff3 4 8 (.sib 2 (some 13) 0 .none)))
    (andR32R32Effect 0x102ff7 2 2 7)) (xorR32R32Effect 0x102ff9 3 2 9)

set_option maxHeartbeats 1600000 in
theorem block051 [Bindings] (boundary : ReturnBoundary)
    (stack input : BitVec 64) (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes051.length → 0x102fc0 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x102fc0 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut051 stack input H M))
      (codeRange 0x102fc0 bytes051) effect051 := by
  unfold bytes051 at hout ⊢
  sha1_run_begin (mov_r64_m64_effect_step 0x102fc0 0x4c (by unfold RexWPrefix; decide +kernel) 2 (.sib 4 none 0 (.d8 0x38)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102fc5 0x45 0xd7 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_m32_effect_step 0x102fc8 0x44 (by unfold RexNoWPrefix; decide +kernel) 5 (.sib 4 none 0 (.d8 0x8)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_m32_effect_step 0x102fcd 0x44 (by unfold RexNoWPrefix; decide +kernel) 7 (.sib 4 none 0 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_m64_effect_step 0x102fd1 0x4c (by unfold RexWPrefix; decide +kernel) 3 (.sib 4 none 0 (.d8 0x48)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102fd6 0x45 0xdf (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_one_rex_effect_step 0x102fd9 0x41 0xc7 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102fdc 0x41 0xed (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_m32_effect_step 0x102fdf 0x44 (by unfold RexNoWPrefix; decide +kernel) 5 (.sib 4 none 0 (.d8 0x30)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_one_rex_effect_step 0x102fe4 0x41 0xc5 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x102fe7 0xc7 0x1e (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x102fea 0x41 0xf9 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102fed 0x41 0xd1 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (and_r32_r32_rex_effect_step 0x102ff0 0x41 0xf1 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (lea_r32_rex_effect_step 0x102ff3 0x46 (by unfold RexNoWPrefix; decide +kernel) 0 (.sib 2 (some 13) 0 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (and_r32_r32_effect_step 0x102ff7 0xfa (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102ff9 0x44 0xca (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_finish [effect051]

private def genericCut051 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), ((A 45)).rotateLeft 30⟩,
    ⟨(.reg 1 : Operand 32), (A 49)⟩,
    ⟨(.reg 2 : Operand 32), ((A 46)).rotateLeft 30⟩,
    ⟨(.reg 3 : Operand 32), (W 48)⟩,
    ⟨(.reg 5 : Operand 32), (W 42)⟩,
    ⟨(.reg 6 : Operand 32), (A 48)⟩,
    ⟨(.reg 7 : Operand 32), (A 47)⟩,
    ⟨(.reg 12 : Operand 32), (W 44)⟩,
    ⟨(.reg 13 : Operand 32), (W 34)⟩,
    ⟨(.reg 14 : Operand 32), (W 40)⟩,
    ⟨(.reg 15 : Operand 32), (W 33)⟩,
    ⟨(.mem (stack + 0) : Operand 32), (W 41)⟩,
    ⟨(.mem (stack + 4) : Operand 32), (W 37)⟩,
    ⟨(.mem (stack + 8) : Operand 32), (W 36)⟩,
    ⟨(.mem (stack + 12) : Operand 32), (W 48)⟩,
    ⟨(.mem (stack + 16) : Operand 32), (W 45)⟩,
    ⟨(.mem (stack + 24) : Operand 32), (W 42)⟩,
    ⟨(.mem (stack + 32) : Operand 32), (W 38)⟩,
    ⟨(.mem (stack + 40) : Operand 32), (W 39)⟩,
    ⟨(.mem (stack + 48) : Operand 32), (W 47)⟩,
    ⟨(.mem (stack + 56) : Operand 32), (W 35)⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), (W 46)⟩,
    ⟨(.mem (stack + 80) : Operand 32), (W 43)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

private def genericCut052 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), ((A 45)).rotateLeft 30⟩,
    ⟨(.reg 1 : Operand 32), (A 49)⟩,
    ⟨(.reg 2 : Operand 32), (((A 48) &&& ((A 46)).rotateLeft 30) ^^^ ((A 48) &&& ((A 47)).rotateLeft 30) ^^^ (((A 46)).rotateLeft 30 &&& ((A 47)).rotateLeft 30))⟩,
    ⟨(.reg 3 : Operand 32), (W 48)⟩,
    ⟨(.reg 6 : Operand 32), (A 48)⟩,
    ⟨(.reg 7 : Operand 32), ((A 47)).rotateLeft 30⟩,
    ⟨(.reg 8 : Operand 32), ((W 50) + ((A 46)).rotateLeft 30)⟩,
    ⟨(.reg 10 : Operand 32), (W 35)⟩,
    ⟨(.reg 11 : Operand 32), (W 46)⟩,
    ⟨(.reg 12 : Operand 32), (W 44)⟩,
    ⟨(.reg 13 : Operand 32), (W 50)⟩,
    ⟨(.reg 14 : Operand 32), (W 40)⟩,
    ⟨(.reg 15 : Operand 32), (W 49)⟩,
    ⟨(.mem (stack + 0) : Operand 32), (W 41)⟩,
    ⟨(.mem (stack + 4) : Operand 32), (W 37)⟩,
    ⟨(.mem (stack + 8) : Operand 32), (W 36)⟩,
    ⟨(.mem (stack + 12) : Operand 32), (W 48)⟩,
    ⟨(.mem (stack + 16) : Operand 32), (W 45)⟩,
    ⟨(.mem (stack + 24) : Operand 32), (W 42)⟩,
    ⟨(.mem (stack + 32) : Operand 32), (W 38)⟩,
    ⟨(.mem (stack + 40) : Operand 32), (W 39)⟩,
    ⟨(.mem (stack + 48) : Operand 32), (W 47)⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), (W 46)⟩,
    ⟨(.mem (stack + 80) : Operand 32), (W 43)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

theorem effect051_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (_hf : FrameData stack input M s)
    (he : (effect051 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hfoot : ∀ c ∈ (effect051 s).components, c ∈ [.reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect051
    iterate 16 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [leaR32Effect_components, andR32R32Effect_components, movR32R32Effect_components,
        movR64M64Effect_components, rolR32Effect_components, xorR32M32Effect_components,
        xorR32R32Effect_components, List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and,
        forall_eq]
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose]
  have ha := he.agrees.mono hfoot
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all (config := {decide := true, implicitDefEqProofs := false}) only [scratchComponents, x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hCov.elim

theorem effect051_rip {s t : RamState}
    (he : (effect051 s).Holds s t) :
    t.RIP = 0x102ffc := by
  exact he.rip.trans (by rfl)

section Words051
private theorem obs051 {s t : RamState} (he : (effect051 s).Holds s t) :
    Obs ((effect051 s).after s true) t := by
  apply he.obsAfter _ true
  apply Effect.Local.full
  unfold effect051
  repeat' first | (solve | x86_local) | apply Effect.Local.seq

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem rawR2_051 {s t : RamState}
    (v2 v6 v7 : BitVec 32)
    (h2 : (Operand.reg 2 : Operand 32).read s = v2)
    (h6 : (Operand.reg 6 : Operand 32).read s = v6)
    (h7 : (Operand.reg 7 : Operand 32).read s = v7)
    (he : (effect051 s).Holds s t) :
    (Operand.reg 2 : Operand 32).read t = (v2 &&& v7.rotateLeft 30) ^^^ ((v7.rotateLeft 30 ^^^ v2) &&& v6) := by
  simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose] at h2 h6 h7
  have ho := obs051 he
  simp only [← ho.read_reg]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [x86_compose, effect051, leaSpec, h2, h6, h7,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem rawR7_051 {s t : RamState}
    (v7 : BitVec 32)
    (h7 : (Operand.reg 7 : Operand 32).read s = v7)
    (he : (effect051 s).Holds s t) :
    (Operand.reg 7 : Operand 32).read t = v7.rotateLeft 30 := by
  simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose] at h7
  have ho := obs051 he
  simp only [← ho.read_reg]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [x86_compose, effect051, leaSpec, h7,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem rawR8_051 {s t : RamState}
    (v2 v5 v13 : BitVec 32)
    (m8 : BitVec 32)
    (m48 : BitVec 32)
    (stack : BitVec 64)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (h2 : (Operand.reg 2 : Operand 32).read s = v2)
    (h5 : (Operand.reg 5 : Operand 32).read s = v5)
    (h13 : (Operand.reg 13 : Operand 32).read s = v13)
    (hm8 : (Operand.mem (stack + 8) : Operand 32).read s = m8)
    (hm48 : (Operand.mem (stack + 48) : Operand 32).read s = m48)
    (he : (effect051 s).Holds s t) :
    (Operand.reg 8 : Operand 32).read t = ((v13 ^^^ m8 ^^^ v5 ^^^ m48).rotateLeft 1) + v2 := by
  simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose] at hs h2 h5 h13 hm8 hm48
  have ho := obs051 he
  simp only [← ho.read_reg]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [x86_compose, effect051, leaSpec, hs, h2, h5, h13, hm8, hm48,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [BitVec.shiftLeft_zero, BitVec.add_zero, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
  ac_rfl

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem rawR10_051 {s t : RamState}
    (m56 : BitVec 64)
    (stack : BitVec 64)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hm56 : (Operand.mem (stack + 56) : Operand 64).read s = m56)
    (he : (effect051 s).Holds s t) :
    (Operand.reg 10 : Operand 32).read t = m56.setWidth 32 := by
  simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose] at hs hm56
  have ho := obs051 he
  simp only [← ho.read_reg]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [x86_compose, effect051, leaSpec, hs, hm56,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem rawR11_051 {s t : RamState}
    (m72 : BitVec 64)
    (stack : BitVec 64)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hm72 : (Operand.mem (stack + 72) : Operand 64).read s = m72)
    (he : (effect051 s).Holds s t) :
    (Operand.reg 11 : Operand 32).read t = m72.setWidth 32 := by
  simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose] at hs hm72
  have ho := obs051 he
  simp only [← ho.read_reg]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [x86_compose, effect051, leaSpec, hs, hm72,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem rawR13_051 {s t : RamState}
    (v5 v13 : BitVec 32)
    (m8 : BitVec 32)
    (m48 : BitVec 32)
    (stack : BitVec 64)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (h5 : (Operand.reg 5 : Operand 32).read s = v5)
    (h13 : (Operand.reg 13 : Operand 32).read s = v13)
    (hm8 : (Operand.mem (stack + 8) : Operand 32).read s = m8)
    (hm48 : (Operand.mem (stack + 48) : Operand 32).read s = m48)
    (he : (effect051 s).Holds s t) :
    (Operand.reg 13 : Operand 32).read t = (v13 ^^^ m8 ^^^ v5 ^^^ m48).rotateLeft 1 := by
  simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose] at hs h5 h13 hm8 hm48
  have ho := obs051 he
  simp only [← ho.read_reg]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [x86_compose, effect051, leaSpec, hs, h5, h13, hm8, hm48,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem rawR15_051 {s t : RamState}
    (v15 : BitVec 32)
    (m0 : BitVec 32)
    (m56 : BitVec 64)
    (m72 : BitVec 64)
    (stack : BitVec 64)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (h15 : (Operand.reg 15 : Operand 32).read s = v15)
    (hm0 : (Operand.mem (stack + 0) : Operand 32).read s = m0)
    (hm56 : (Operand.mem (stack + 56) : Operand 64).read s = m56)
    (hm72 : (Operand.mem (stack + 72) : Operand 64).read s = m72)
    (he : (effect051 s).Holds s t) :
    (Operand.reg 15 : Operand 32).read t = (v15 ^^^ m56.setWidth 32 ^^^ m0 ^^^ m72.setWidth 32).rotateLeft 1 := by
  simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose] at hs h15 hm0 hm56 hm72
  have ho := obs051 he
  simp only [← ho.read_reg]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [x86_compose, effect051, leaSpec, hs, h15, hm0, hm56, hm72,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem genericWords051 {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) {s t : RamState}
    (hW49 : W 49 = (W 46 ^^^ W 41 ^^^ W 35 ^^^ W 33).rotateLeft 1)
    (hW50 : W 50 = (W 47 ^^^ W 42 ^^^ W 36 ^^^ W 34).rotateLeft 1)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hw : Write.AllHold s (genericCut051 stack input H A W))
    (he : (effect051 s).Holds s t) :
    Write.AllHold t (genericCut052 stack input H A W) := by
  have hw0 := hw
  simp only [genericCut051, Write.AllHold] at hw0
  obtain ⟨h0,h1,h2,h3,h5,h6,h7,h12,h13,h14,h15,
    hM0,hM4,hM8,hM12,hM16,hM24,hM32,hM40,hM48,hM56,hM64,hM72,hM80,
    hM116,hM120,hM124,hM144,hM152⟩ := hw0
  have lo56 := (read32_of_read64_low
    (s:=s) (a:=stack+56) (v:=(Operand.mem (stack+56) : Operand 64).read s) rfl).symm.trans hM56
  have lo72 := (read32_of_read64_low
    (s:=s) (a:=stack+72) (v:=(Operand.mem (stack+72) : Operand 64).read s) rfl).symm.trans hM72
  have hR2 := rawR2_051 ((A 46).rotateLeft 30) (A 48) (A 47) h2 h6 h7 he
  have hR7 := rawR7_051 (A 47) h7 he
  have hR8 := rawR8_051 ((A 46).rotateLeft 30) (W 42) (W 34) (W 36) (W 47)
    stack hs h2 h5 h13 hM8 hM48 he
  have hR10 := rawR10_051 ((Operand.mem (stack+56) : Operand 64).read s) stack hs rfl he
  have hR11 := rawR11_051 ((Operand.mem (stack+72) : Operand 64).read s) stack hs rfl he
  have hR13 := rawR13_051 (W 42) (W 34) (W 36) (W 47) stack hs h5 h13 hM8 hM48 he
  have hR15 := rawR15_051 (W 33) (W 41)
    ((Operand.mem (stack+56) : Operand 64).read s)
    ((Operand.mem (stack+72) : Operand 64).read s) stack hs h15 hM0 rfl rfl he
  have hSchedule50 : (W 34 ^^^ W 36 ^^^ W 42 ^^^ W 47).rotateLeft 1 = W 50 := by
    rw [hW50]
    congr 1
    ac_rfl
  have hSchedule49 : (W 33 ^^^ W 35 ^^^ W 41 ^^^ W 46).rotateLeft 1 = W 49 := by
    rw [hW49]
    congr 1
    ac_rfl
  rw [hSchedule50] at hR8 hR13
  rw [lo56,lo72,hSchedule49] at hR15
  rw [lo56] at hR10
  rw [lo72] at hR11
  have hMaj (a b c : BitVec 32) :
      (b &&& c) ^^^ ((c ^^^ b) &&& a) =
      (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and]
    cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.getLsbD i <;> decide
  rw [hMaj] at hR2
  have hfoot : ∀ c ∈ (effect051 s).components,
      c ∈ [.reg 2,.reg 7,.reg 8,.reg 9,.reg 10,.reg 11,.reg 13,.reg 15,.flags,.rip] := by
    unfold effect051
    iterate 16 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [movR64M64Effect_components, xorR32R32Effect_components, xorR32M32Effect_components,
       rolR32Effect_components, movR32R32Effect_components, andR32R32Effect_components,
       leaR32Effect_components,
       List.mem_cons,List.not_mem_nil,or_false,or_imp,forall_and,forall_eq]
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose]
  have ha := he.agrees.mono hfoot
  have hExt : t.external = s.external := by
    apply ha.external
    intro c hc x
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact fun h => h.elim
  have hmem {n : Nat} (a : BitVec 64) :
      (Operand.mem a : Operand n).read t = (Operand.mem a : Operand n).read s := by
    change memLoad t.external a n = memLoad s.external a n
    rw [hExt]
  simp only [genericCut052,Write.AllHold]
  refine ⟨?f0, ?f1, ?f2, ?f3, ?f4, ?f5, ?f6, ?f7, ?f8, ?f9, ?f10, ?f11, ?f12, ?f13, ?f14, ?f15, ?f16, ?f17, ?f18, ?f19, ?f20, ?f21, ?f22, ?f23, ?f24, ?f25, ?f26, ?f27, ?f28, ?f29⟩
  case f0 => exact (ha.read (by simp)).trans h0
  case f1 => exact (ha.read (by simp)).trans h1
  case f2 => exact hR2
  case f3 => exact (ha.read (by simp)).trans h3
  case f4 => exact (ha.read (by simp)).trans h6
  case f5 => exact hR7
  case f6 => exact hR8
  case f7 => exact hR10
  case f8 => exact hR11
  case f9 => exact (ha.read (by simp)).trans h12
  case f10 => exact hR13
  case f11 => exact (ha.read (by simp)).trans h14
  case f12 => exact hR15
  case f13 => exact (hmem (stack+0)).trans hM0
  case f14 => exact (hmem (stack+4)).trans hM4
  case f15 => exact (hmem (stack+8)).trans hM8
  case f16 => exact (hmem (stack+12)).trans hM12
  case f17 => exact (hmem (stack+16)).trans hM16
  case f18 => exact (hmem (stack+24)).trans hM24
  case f19 => exact (hmem (stack+32)).trans hM32
  case f20 => exact (hmem (stack+40)).trans hM40
  case f21 => exact (hmem (stack+48)).trans hM48
  case f22 => exact (hmem (stack+64)).trans hM64
  case f23 => exact (hmem (stack+72)).trans hM72
  case f24 => exact (hmem (stack+80)).trans hM80
  case f25 => exact (hmem (stack+116)).trans hM116
  case f26 => exact (hmem (stack+120)).trans hM120
  case f27 => exact (hmem (stack+124)).trans hM124
  case f28 => exact (hmem (stack+144)).trans hM144
  case f29 => exact (hmem (stack+152)).trans hM152

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
theorem effect051_words {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut051 stack input H M))
    (he : (effect051 s).Holds s t) :
    Write.AllHold t (cut052 stack input H M) := by
  have hW49 : scheduleWord M 49 =
      (scheduleWord M 46 ^^^ scheduleWord M 41 ^^^ scheduleWord M 35 ^^^ scheduleWord M 33).rotateLeft 1 := by
    rw [scheduleWord_recurrence M (49 : Fin 80) (by decide), sha1Rotl_eq_rotateLeft 1 _ (by decide)]
    rfl
  have hW50 : scheduleWord M 50 =
      (scheduleWord M 47 ^^^ scheduleWord M 42 ^^^ scheduleWord M 36 ^^^ scheduleWord M 34).rotateLeft 1 := by
    rw [scheduleWord_recurrence M (50 : Fin 80) (by decide), sha1Rotl_eq_rotateLeft 1 _ (by decide)]
    rfl
  exact genericWords051 (fun n => (workingAfter M H n).a) (scheduleWord M)
    hW49 hW50 hf.stackPointer hw he

end Words051

theorem segment051 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x102fc0 0x102ffc
      cut051 cut052 := by
  have hout : ∀ d : Nat, d ≤ bytes051.length →
      0x102fc0 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    have hd' : d ≤ 60 := hd
    have hd64 : d < 2 ^ 64 := by omega
    have hsum : 0x102fc0 + d < 2 ^ 64 := by omega
    have hpc : (0x102fc0 + BitVec.ofNat 64 d).toNat = 0x102fc0 + d := by
      change (0x102fc0 + d % 2 ^ 64) % 2 ^ 64 = 0x102fc0 + d
      rw [Nat.mod_eq_of_lt hd64, Nat.mod_eq_of_lt hsum]
    exact outsideCompression_ne hOutside (by rw [hpc]; omega) (by rw [hpc]; omega)
  apply Segment.of_block (fun _ _ _ _ => effect051)
    (fun stack input H M => block051 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64
      0x2fc0) bytes051,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect051_rip he
  · intro stack input H M s t _ hf _ he
    exact effect051_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect051_words hf hw he

end Sha1.Proofs.Compress.Machine

namespace Sha1.Proofs.Compress.Machine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Spec.Program
open Standards.NIST.SHA1 Standards.NIST.SHA2.SHA256 Sha1.Proofs.Compress.Rounds

attribute [local irreducible] workingAfter scheduleWord messageSchedule

def bytes052 : List UInt8 :=
  [0x44, 0x1, 0xf8, 0x1, 0xd0, 0x89, 0xca, 0xc1, 0xc2, 0x5, 0x1, 0xd0, 0x5, 0xdc, 0xbc, 0x1b, 0x8f,
    0x4c, 0x89, 0xd2, 0x8b, 0x6c, 0x24, 0x4, 0x31, 0xea, 0x33, 0x54, 0x24, 0x50, 0x31, 0xda, 0xd1,
    0xc2, 0x49, 0x89, 0xd2, 0xc1, 0xc6, 0x1e, 0x89, 0xf2, 0x31, 0xfa, 0x21, 0xca, 0x45, 0x8d, 0xc,
    0x3a, 0x4c, 0x89, 0xd3]

set_option maxHeartbeats 800000 in
def effect052 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq ((addR32R32Effect 0x102ffc 3 0 15)) (addR32R32Effect 0x102fff 2 0 2))
    (movR32R32Effect 0x103001 2 2 1)) (rolR32Effect 0x103003 3 2 5)) (addR32R32Effect 0x103006 2 0
    2)) (addEaxImm32Effect 0x103008 0x8f1bbcdc)) (movR64R64Effect 0x10300d 2 10))
    (movR32M32LowEffect 0x103010 5 (.sib 4 none 0 (.d8 0x4)))) (xorR32R32Effect 0x103014 2 2 5))
    (xorR32M32LowEffect 0x103016 2 (.sib 4 none 0 (.d8 0x50)))) (xorR32R32Effect 0x10301a 2 2 3))
    (rolR32Effect 0x10301c 2 2 1)) (movR64R64Effect 0x10301e 10 2)) (rolR32Effect 0x103021 3 6 30))
    (movR32R32Effect 0x103024 2 2 6)) (xorR32R32Effect 0x103026 2 2 7)) (andR32R32Effect 0x103028 2
    2 1)) (leaR32Effect 0x10302a 4 9 (.sib 10 (some 7) 0 .none))) (movR64R64Effect 0x10302e 3 10)

set_option maxHeartbeats 1600000 in
theorem block052 [Bindings] (boundary : ReturnBoundary)
    (stack input : BitVec 64) (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes052.length → 0x102ffc + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x102ffc ∧ FrameData stack input M s ∧
        Write.AllHold s (cut052 stack input H M))
      (codeRange 0x102ffc bytes052) effect052 := by
  unfold bytes052 at hout ⊢
  sha1_run_begin (add_r32_r32_rex_effect_step 0x102ffc 0x44 0xf8 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x102fff 0xd0 (by decide +kernel))
  sha1_run_then (mov_r32_r32_effect_step 0x103001 0xca (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x103003 0xc2 0x5 (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x103006 0xd0 (by decide +kernel))
  sha1_run_then (add_eax_imm32_effect_step 0x103008 0x8f1bbcdc)
  sha1_run_then (mov_r64_r64_effect_step 0x10300d 0x4c 0xd2 (by unfold RexWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_m32_low_effect_step 0x103010 5 (.sib 4 none 0 (.d8 0x4)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x103014 0xea (by decide +kernel))
  sha1_run_then (xor_r32_m32_low_effect_step 0x103016 2 (.sib 4 none 0 (.d8 0x50)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x10301a 0xda (by decide +kernel))
  sha1_run_then (rol_r32_one_effect_step 0x10301c 0xc2 (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_r64_effect_step 0x10301e 0x49 0xd2 (by unfold RexWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x103021 0xc6 0x1e (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_effect_step 0x103024 0xf2 (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x103026 0xfa (by decide +kernel))
  sha1_run_then (and_r32_r32_effect_step 0x103028 0xca (by decide +kernel))
  sha1_run_then (lea_r32_rex_effect_step 0x10302a 0x45 (by unfold RexNoWPrefix; decide +kernel) 1 (.sib 10 (some 7) 0 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_r64_effect_step 0x10302e 0x4c 0xd3 (by unfold RexWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_finish [effect052]

private def genericCut053 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), (A 50)⟩,
    ⟨(.reg 1 : Operand 32), (A 49)⟩,
    ⟨(.reg 2 : Operand 32), (((A 49) &&& ((A 47)).rotateLeft 30) ^^^ ((A 49) &&& ((A 48)).rotateLeft 30))⟩,
    ⟨(.reg 3 : Operand 32), (W 51)⟩,
    ⟨(.reg 5 : Operand 32), (W 37)⟩,
    ⟨(.reg 6 : Operand 32), ((A 48)).rotateLeft 30⟩,
    ⟨(.reg 7 : Operand 32), ((A 47)).rotateLeft 30⟩,
    ⟨(.reg 8 : Operand 32), ((W 50) + ((A 46)).rotateLeft 30)⟩,
    ⟨(.reg 9 : Operand 32), ((W 51) + ((A 47)).rotateLeft 30)⟩,
    ⟨(.reg 10 : Operand 32), (W 51)⟩,
    ⟨(.reg 11 : Operand 32), (W 46)⟩,
    ⟨(.reg 12 : Operand 32), (W 44)⟩,
    ⟨(.reg 13 : Operand 32), (W 50)⟩,
    ⟨(.reg 14 : Operand 32), (W 40)⟩,
    ⟨(.reg 15 : Operand 32), (W 49)⟩,
    ⟨(.mem (stack + 0) : Operand 32), (W 41)⟩,
    ⟨(.mem (stack + 8) : Operand 32), (W 36)⟩,
    ⟨(.mem (stack + 12) : Operand 32), (W 48)⟩,
    ⟨(.mem (stack + 16) : Operand 32), (W 45)⟩,
    ⟨(.mem (stack + 24) : Operand 32), (W 42)⟩,
    ⟨(.mem (stack + 32) : Operand 32), (W 38)⟩,
    ⟨(.mem (stack + 40) : Operand 32), (W 39)⟩,
    ⟨(.mem (stack + 48) : Operand 32), (W 47)⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), (W 46)⟩,
    ⟨(.mem (stack + 80) : Operand 32), (W 43)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

theorem effect052_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (_hf : FrameData stack input M s)
    (he : (effect052 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hfoot : ∀ c ∈ (effect052 s).components, c ∈ [.reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect052
    iterate 18 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [movR32M32LowEffect, leaR32Effect_components, addEaxImm32Effect_components,
        addR32R32Effect_components, andR32R32Effect_components, movR32R32Effect_components,
        movR64R64Effect_components, rolR32Effect_components, xorR32M32LowEffect,
        xorR32R32Effect_components, List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and,
        forall_eq]
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose]
  have ha := he.agrees.mono hfoot
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all (config := {decide := true, implicitDefEqProofs := false}) only [scratchComponents, x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hCov.elim

theorem effect052_rip {s t : RamState}
    (he : (effect052 s).Holds s t) :
    t.RIP = 0x103031 := by
  exact he.rip.trans (by rfl)

section Words052
private theorem obs052 {s t : RamState} (he : (effect052 s).Holds s t) :
    Obs ((effect052 s).after s true) t := by
  apply he.obsAfter _ true
  apply Effect.Local.full
  unfold effect052
  repeat' first | (solve | x86_local) | apply Effect.Local.seq

private theorem rawR0_052 {s t : RamState}
    (v0 v1 v2 v15 : BitVec 32)
    (h0 : (Operand.reg 0 : Operand 32).read s = v0)
    (h1 : (Operand.reg 1 : Operand 32).read s = v1)
    (h2 : (Operand.reg 2 : Operand 32).read s = v2)
    (h15 : (Operand.reg 15 : Operand 32).read s = v15)
    (he : (effect052 s).Holds s t) :
    (Operand.reg 0 : Operand 32).read t = v0 + v15 + v2 + v1.rotateLeft 5 + 0x8f1bbcdc := by
  simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose] at h0 h1 h2 h15
  have ho := obs052 he
  simp only [← ho.read_reg]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [x86_compose, effect052, leaSpec, movR32M32LowEffect, h0, h1, h2, h15,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, BitVec.add_zero]

private theorem rawR2_052 {s t : RamState}
    (v1 v6 v7 : BitVec 32)
    (h1 : (Operand.reg 1 : Operand 32).read s = v1)
    (h6 : (Operand.reg 6 : Operand 32).read s = v6)
    (h7 : (Operand.reg 7 : Operand 32).read s = v7)
    (he : (effect052 s).Holds s t) :
    (Operand.reg 2 : Operand 32).read t = (v6.rotateLeft 30 ^^^ v7) &&& v1 := by
  simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose] at h1 h6 h7
  have ho := obs052 he
  simp only [← ho.read_reg]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [x86_compose, effect052, leaSpec, movR32M32LowEffect, h1, h6, h7,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, BitVec.add_zero]

private theorem rawR3_052 {s t : RamState}
    (v3 v10 : BitVec 32)
    (m4 m80 : BitVec 32) (stack : BitVec 64)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (h3 : (Operand.reg 3 : Operand 32).read s = v3)
    (h10 : (Operand.reg 10 : Operand 32).read s = v10)
    (hm4 : (Operand.mem (stack+4) : Operand 32).read s = m4)
    (hm80 : (Operand.mem (stack+80) : Operand 32).read s = m80)
    (he : (effect052 s).Holds s t) :
    (Operand.reg 3 : Operand 32).read t = (v10 ^^^ m4 ^^^ m80 ^^^ v3).rotateLeft 1 := by
  simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose] at hs h3 h10 hm4 hm80
  have ho := obs052 he
  simp only [← ho.read_reg]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [x86_compose, effect052, leaSpec, movR32M32LowEffect, hs, h3, h10, hm4, hm80,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, BitVec.add_zero]

private theorem rawR5_052 {s t : RamState}
    (m4 m80 : BitVec 32) (stack : BitVec 64)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hm4 : (Operand.mem (stack+4) : Operand 32).read s = m4)
    (hm80 : (Operand.mem (stack+80) : Operand 32).read s = m80)
    (he : (effect052 s).Holds s t) :
    (Operand.reg 5 : Operand 32).read t = m4 := by
  simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose] at hs hm4 hm80
  have ho := obs052 he
  simp only [← ho.read_reg]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [x86_compose, effect052, leaSpec, movR32M32LowEffect, hs, hm4, hm80,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, BitVec.add_zero]

private theorem rawR6_052 {s t : RamState}
    (v6 : BitVec 32)
    (h6 : (Operand.reg 6 : Operand 32).read s = v6)
    (he : (effect052 s).Holds s t) :
    (Operand.reg 6 : Operand 32).read t = v6.rotateLeft 30 := by
  simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose] at h6
  have ho := obs052 he
  simp only [← ho.read_reg]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [x86_compose, effect052, leaSpec, movR32M32LowEffect, h6,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, BitVec.add_zero]

private theorem rawR9_052 {s t : RamState}
    (v3 v7 v10 : BitVec 32)
    (m4 m80 : BitVec 32) (stack : BitVec 64)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (h3 : (Operand.reg 3 : Operand 32).read s = v3)
    (h7 : (Operand.reg 7 : Operand 32).read s = v7)
    (h10 : (Operand.reg 10 : Operand 32).read s = v10)
    (hm4 : (Operand.mem (stack+4) : Operand 32).read s = m4)
    (hm80 : (Operand.mem (stack+80) : Operand 32).read s = m80)
    (he : (effect052 s).Holds s t) :
    (Operand.reg 9 : Operand 32).read t = (v10 ^^^ m4 ^^^ m80 ^^^ v3).rotateLeft 1 + v7 := by
  simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose] at hs h3 h7 h10 hm4 hm80
  have ho := obs052 he
  simp only [← ho.read_reg]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [x86_compose, effect052, leaSpec, movR32M32LowEffect, hs, h3, h7, h10, hm4, hm80,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, BitVec.add_zero]

private theorem rawR10_052 {s t : RamState}
    (v3 v10 : BitVec 32)
    (m4 m80 : BitVec 32) (stack : BitVec 64)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (h3 : (Operand.reg 3 : Operand 32).read s = v3)
    (h10 : (Operand.reg 10 : Operand 32).read s = v10)
    (hm4 : (Operand.mem (stack+4) : Operand 32).read s = m4)
    (hm80 : (Operand.mem (stack+80) : Operand 32).read s = m80)
    (he : (effect052 s).Holds s t) :
    (Operand.reg 10 : Operand 32).read t = (v10 ^^^ m4 ^^^ m80 ^^^ v3).rotateLeft 1 := by
  simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose] at hs h3 h10 hm4 hm80
  have ho := obs052 he
  simp only [← ho.read_reg]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [x86_compose, effect052, leaSpec, movR32M32LowEffect, hs, h3, h10, hm4, hm80,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, BitVec.add_zero]

private theorem work052_actual (M : Vector (BitVec 32) 16)
    (H : Vector (BitVec 32) 5) :
    (workingAfter M H 50).a =
      ((workingAfter M H 49).a).rotateLeft 5 +
        (((workingAfter M H 48).a &&& ((workingAfter M H 46).a).rotateLeft 30) ^^^
          ((workingAfter M H 48).a &&& ((workingAfter M H 47).a).rotateLeft 30) ^^^
          (((workingAfter M H 46).a).rotateLeft 30 &&& ((workingAfter M H 47).a).rotateLeft 30)) +
        ((workingAfter M H 45).a).rotateLeft 30 + 0x8f1bbcdc + scheduleWord M 49 := by
  rw [workingAfter_step_a_values M H 45 (by decide +kernel)]
  rw [sha1_f_majority (t := ⟨49, by decide⟩) (by decide) (by decide)]
  have hMaj (x y z : BitVec 32) :
      Standards.NIST.SHA2.SHA256.Maj x y z = (x &&& y) ^^^ ((x ^^^ y) &&& z) := by
    rw [sha1Maj_eq_xor]
  have hMajAlt (x y z : BitVec 32) :
      (x &&& y) ^^^ ((x ^^^ y) &&& z) =
        (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and]
    cases x.getLsbD i <;> cases y.getLsbD i <;> cases z.getLsbD i <;> decide
  have hK : K (⟨49, by decide⟩ : Fin 80) = 0x8f1bbcdc := by decide
  rw [hMaj, hMajAlt, hK]
  ac_rfl

private theorem genericWords052 {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32)
    (hWork : A 50 = (A 49).rotateLeft 5 +
      ((A 48 &&& (A 46).rotateLeft 30) ^^^
        (A 48 &&& (A 47).rotateLeft 30) ^^^
        ((A 46).rotateLeft 30 &&& (A 47).rotateLeft 30)) +
      (A 45).rotateLeft 30 + 0x8f1bbcdc + W 49)
    (hSched51 : W 51 = (W 48 ^^^ W 43 ^^^ W 37 ^^^ W 35).rotateLeft 1)
    {s t : RamState}
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hw : Write.AllHold s (genericCut052 stack input H A W))
    (he : (effect052 s).Holds s t) :
    Write.AllHold t (genericCut053 stack input H A W) := by
  have hw0 := hw
  simp only [genericCut052, Write.AllHold] at hw0
  obtain ⟨h0,h1,h2,h3,h6,h7,h8,h10,h11,h12,h13,h14,h15,
    hM0,hM4,hM8,hM12,hM16,hM24,hM32,hM40,hM48,hM64,hM72,hM80,
    hM116,hM120,hM124,hM144,hM152⟩ := hw0
  have hR0 := rawR0_052 ((A 45).rotateLeft 30) (A 49)
    (((A 48 &&& (A 46).rotateLeft 30) ^^^ (A 48 &&& (A 47).rotateLeft 30)) ^^^
     ((A 46).rotateLeft 30 &&& (A 47).rotateLeft 30)) (W 49) h0 h1 h2 h15 he
  have hR2 := rawR2_052 (A 49) (A 48) ((A 47).rotateLeft 30) h1 h6 h7 he
  have hR3 := rawR3_052 (W 48) (W 35) (W 37) (W 43) stack hs h3 h10 hM4 hM80 he
  have hR5 := rawR5_052 (W 37) (W 43) stack hs hM4 hM80 he
  have hR6 := rawR6_052 (A 48) h6 he
  have hR9 := rawR9_052 (W 48) ((A 47).rotateLeft 30) (W 35)
    (W 37) (W 43) stack hs h3 h7 h10 hM4 hM80 he
  have hR10 := rawR10_052 (W 48) (W 35) (W 37) (W 43) stack hs h3 h10 hM4 hM80 he
  have hSchedule : (W 35 ^^^ W 37 ^^^ W 43 ^^^ W 48).rotateLeft 1 = W 51 := by
    rw [hSched51]
    congr 1
    ac_rfl
  rw [hSchedule] at hR3 hR9 hR10
  have hAndXor (a b c : BitVec 32) :
      (c ^^^ b) &&& a = (a &&& b) ^^^ (a &&& c) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and]
    cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.getLsbD i <;> decide
  rw [hAndXor] at hR2
  have hV0 : (Operand.reg 0 : Operand 32).read t = A 50 := by
    calc
      _ = _ := hR0
      _ = _ := by rw [hWork]; ac_rfl
  have hfoot : ∀ c ∈ (effect052 s).components,
      c ∈ [.reg 0,.reg 2,.reg 3,.reg 5,.reg 6,.reg 9,.reg 10,.flags,.rip] := by
    unfold effect052
    iterate 18 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [movR32M32LowEffect,
       leaR32Effect_components,
       addEaxImm32Effect_components, addR32R32Effect_components,
       andR32R32Effect_components, movR32R32Effect_components,
       movR64R64Effect_components, rolR32Effect_components,
       xorR32M32LowEffect, xorR32R32Effect_components,
       List.mem_cons,List.not_mem_nil,or_false,or_imp,forall_and,forall_eq]
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose]
  have ha := he.agrees.mono hfoot
  have hmem {n : Nat} (off : BitVec 64) :
      (Operand.mem (stack+off) : Operand n).read t =
      (Operand.mem (stack+off) : Operand n).read s := by
    apply memLoad_congr
    intro i hi
    apply congrArg (fun b : Option UInt8 => b.getD 0)
    apply ha.byte
    intro c hc hCov
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact hCov.elim
  simp only [genericCut053,Write.AllHold]
  refine ⟨?f0, ?f1, ?f2, ?f3, ?f4, ?f5, ?f6, ?f7, ?f8, ?f9, ?f10, ?f11, ?f12, ?f13, ?f14, ?f15, ?f16, ?f17, ?f18, ?f19, ?f20, ?f21, ?f22, ?f23, ?f24, ?f25, ?f26, ?f27, ?f28, ?f29, ?f30⟩
  case f0 => exact hV0
  case f1 => exact (ha.read (by simp)).trans h1
  case f2 => exact hR2
  case f3 => exact hR3
  case f4 => exact hR5
  case f5 => exact hR6
  case f6 => exact (ha.read (by simp)).trans h7
  case f7 => exact (ha.read (by simp)).trans h8
  case f8 => exact hR9
  case f9 => exact hR10
  case f10 => exact (ha.read (by simp)).trans h11
  case f11 => exact (ha.read (by simp)).trans h12
  case f12 => exact (ha.read (by simp)).trans h13
  case f13 => exact (ha.read (by simp)).trans h14
  case f14 => exact (ha.read (by simp)).trans h15
  case f15 => exact (hmem 0).trans hM0
  case f16 => exact (hmem 8).trans hM8
  case f17 => exact (hmem 12).trans hM12
  case f18 => exact (hmem 16).trans hM16
  case f19 => exact (hmem 24).trans hM24
  case f20 => exact (hmem 32).trans hM32
  case f21 => exact (hmem 40).trans hM40
  case f22 => exact (hmem 48).trans hM48
  case f23 => exact (hmem 64).trans hM64
  case f24 => exact (hmem 72).trans hM72
  case f25 => exact (hmem 80).trans hM80
  case f26 => exact (hmem 116).trans hM116
  case f27 => exact (hmem 120).trans hM120
  case f28 => exact (hmem 124).trans hM124
  case f29 => exact (hmem 144).trans hM144
  case f30 => exact (hmem 152).trans hM152

theorem effect052_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16}
    {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut052 stack input H M))
    (he : (effect052 s).Holds s t) :
    Write.AllHold t (cut053 stack input H M) := by
  have hWork := work052_actual M H
  have hSched51 : scheduleWord M 51 =
      (scheduleWord M 48 ^^^ scheduleWord M 43 ^^^ scheduleWord M 37 ^^^
        scheduleWord M 35).rotateLeft 1 := by
    change scheduleWord M (⟨51, by decide⟩ : Fin 80) = _
    rw [scheduleWord_recurrence M ⟨51, by decide⟩ (by decide)]
    simp only [Nat.reduceSub]
    rw [sha1Rotl_eq_rotateLeft 1 _ (by decide)]
    rfl
  have hpre : Write.AllHold s
      (genericCut052 stack input H (fun n ↦ (workingAfter M H n).a) (scheduleWord M)) := by
    change Write.AllHold s (cut052 stack input H M)
    exact hw
  exact genericWords052 (fun n ↦ (workingAfter M H n).a) (scheduleWord M)
    hWork hSched51 hf.stackPointer hpre he
end Words052

theorem segment052 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x102ffc 0x103031
      cut052 cut053 := by
  have hout : ∀ d : Nat, d ≤ bytes052.length →
      0x102ffc + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    have hd' : d ≤ 53 := hd
    have hd64 : d < 2 ^ 64 := by omega
    have hsum : 0x102ffc + d < 2 ^ 64 := by omega
    have hpc : (0x102ffc + BitVec.ofNat 64 d).toNat = 0x102ffc + d := by
      change (0x102ffc + d % 2 ^ 64) % 2 ^ 64 = 0x102ffc + d
      rw [Nat.mod_eq_of_lt hd64, Nat.mod_eq_of_lt hsum]
    exact outsideCompression_ne hOutside (by rw [hpc]; omega) (by rw [hpc]; omega)
  apply Segment.of_block (fun _ _ _ _ => effect052)
    (fun stack input H M => block052 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64
      0x2ffc) bytes052,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect052_rip he
  · intro stack input H M s t _ hf _ he
    exact effect052_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect052_words hf hw he

end Sha1.Proofs.Compress.Machine

namespace Sha1.Proofs.Compress.Machine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Spec.Program
open Standards.NIST.SHA1 Standards.NIST.SHA2.SHA256 Sha1.Proofs.Compress.Rounds

attribute [local irreducible] workingAfter scheduleWord messageSchedule

def bytes053 : List UInt8 :=
  [0x4c, 0x89, 0x54, 0x24, 0x38, 0x21, 0xf7, 0x31, 0xd7, 0x44, 0x1, 0xc7, 0x89, 0xc2, 0xc1, 0xc2,
    0x5, 0x1, 0xd7, 0x81, 0xc7, 0xdc, 0xbc, 0x1b, 0x8f, 0xc1, 0xc1, 0x1e, 0x89, 0xca, 0x31, 0xf2,
    0x21, 0xc2, 0x41, 0x89, 0xc8, 0x41, 0x21, 0xf0, 0x41, 0x31, 0xd0, 0x89, 0xfa, 0xc1, 0xc2, 0x5,
    0x45, 0x1, 0xc8, 0x44, 0x1, 0xc2, 0x81, 0xc2, 0xdc, 0xbc, 0x1b, 0x8f]

set_option maxHeartbeats 800000 in
def effect053 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq (Effect.seq ((movM64R64Effect 0x103031 10 (.sib 4 none 0 (.d8 0x38))))
    (andR32R32Effect 0x103036 2 7 6)) (xorR32R32Effect 0x103038 2 7 2)) (addR32R32Effect 0x10303a 3
    7 8)) (movR32R32Effect 0x10303d 2 2 0)) (rolR32Effect 0x10303f 3 2 5)) (addR32R32Effect 0x103042
    2 7 2)) (addR32Imm32Effect 0x103044 6 7 0x8f1bbcdc)) (rolR32Effect 0x10304a 3 1 30))
    (movR32R32Effect 0x10304d 2 2 1)) (xorR32R32Effect 0x10304f 2 2 6)) (andR32R32Effect 0x103051 2
    2 0)) (movR32R32Effect 0x103053 3 8 1)) (andR32R32Effect 0x103056 3 8 6)) (xorR32R32Effect
    0x103059 3 8 2)) (movR32R32Effect 0x10305c 2 2 7)) (rolR32Effect 0x10305e 3 2 5))
    (addR32R32Effect 0x103061 3 8 9)) (addR32R32Effect 0x103064 3 2 8)) (addR32Imm32Effect 0x103067
    6 2 0x8f1bbcdc)

set_option maxHeartbeats 1600000 in
theorem block053 [Bindings] (boundary : ReturnBoundary)
    (stack input : BitVec 64) (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes053.length → 0x103031 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x103031 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut053 stack input H M))
      (codeRange 0x103031 bytes053) effect053 := by
  unfold bytes053 at hout ⊢
  sha1_run_begin (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step 0x103031 0x4c (by unfold RexWPrefix; decide +kernel) 2 (.sib 4 none 0 (.d8 0x38)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (and_r32_r32_effect_step 0x103036 0xf7 (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x103038 0xd7 (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x10303a 0x44 0xc7 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_effect_step 0x10303d 0xc2 (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x10303f 0xc2 0x5 (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x103042 0xd7 (by decide +kernel))
  sha1_run_then (add_r32_imm32_effect_step 0x103044 0xc7 0x8f1bbcdc (by decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x10304a 0xc1 0x1e (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_effect_step 0x10304d 0xca (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x10304f 0xf2 (by decide +kernel))
  sha1_run_then (and_r32_r32_effect_step 0x103051 0xc2 (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x103053 0x41 0xc8 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (and_r32_r32_rex_effect_step 0x103056 0x41 0xf0 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x103059 0x41 0xd0 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_effect_step 0x10305c 0xfa (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x10305e 0xc2 0x5 (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x103061 0x45 0xc8 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x103064 0x44 0xc2 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_imm32_effect_step 0x103067 0xc2 0x8f1bbcdc (by decide +kernel) (by decide +kernel))
  sha1_run_finish [effect053]

private def genericCut054 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), (A 50)⟩,
    ⟨(.reg 1 : Operand 32), ((A 49)).rotateLeft 30⟩,
    ⟨(.reg 2 : Operand 32), (A 52)⟩,
    ⟨(.reg 3 : Operand 32), (W 51)⟩,
    ⟨(.reg 5 : Operand 32), (W 37)⟩,
    ⟨(.reg 6 : Operand 32), ((A 48)).rotateLeft 30⟩,
    ⟨(.reg 7 : Operand 32), (A 51)⟩,
    ⟨(.reg 11 : Operand 32), (W 46)⟩,
    ⟨(.reg 12 : Operand 32), (W 44)⟩,
    ⟨(.reg 13 : Operand 32), (W 50)⟩,
    ⟨(.reg 14 : Operand 32), (W 40)⟩,
    ⟨(.reg 15 : Operand 32), (W 49)⟩,
    ⟨(.mem (stack + 0) : Operand 32), (W 41)⟩,
    ⟨(.mem (stack + 8) : Operand 32), (W 36)⟩,
    ⟨(.mem (stack + 12) : Operand 32), (W 48)⟩,
    ⟨(.mem (stack + 16) : Operand 32), (W 45)⟩,
    ⟨(.mem (stack + 24) : Operand 32), (W 42)⟩,
    ⟨(.mem (stack + 32) : Operand 32), (W 38)⟩,
    ⟨(.mem (stack + 40) : Operand 32), (W 39)⟩,
    ⟨(.mem (stack + 48) : Operand 32), (W 47)⟩,
    ⟨(.mem (stack + 56) : Operand 32), (W 51)⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), (W 46)⟩,
    ⟨(.mem (stack + 80) : Operand 32), (W 43)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

theorem effect053_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (he : (effect053 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hfoot : ∀ c ∈ (effect053 s).components, c ∈ [.mem ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 56) 8, .reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect053
    iterate 19 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [addR32Imm32Effect_components, addR32R32Effect_components, andR32R32Effect_components,
        movM64R64Effect_components, movR32R32Effect_components, rolR32Effect_components,
        xorR32R32Effect_components, List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and,
        forall_eq, or_true]
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose]
  have ha := he.agrees.mono hfoot
  rw [hs] at ha
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all (config := {decide := true, implicitDefEqProofs := false}) only [Component.isMem, scratchComponents, x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hCov.elim
      | exact scratchComponents_stack (Or.inl (by decide +kernel)) hCov

theorem effect053_rip {s t : RamState}
    (he : (effect053 s).Holds s t) :
    t.RIP = 0x10306d := by
  exact he.rip.trans (by rfl)

section Words053

private def prefix053 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq ((movM64R64Effect 0x103031 10 (.sib 4 none 0 (.d8 0x38))))
    (andR32R32Effect 0x103036 2 7 6)) (xorR32R32Effect 0x103038 2 7 2)) (addR32R32Effect 0x10303a 3
    7 8)) (movR32R32Effect 0x10303d 2 2 0)) (rolR32Effect 0x10303f 3 2 5)) (addR32R32Effect 0x103042
    2 7 2)) (addR32Imm32Effect 0x103044 6 7 0x8f1bbcdc)) (rolR32Effect 0x10304a 3 1 30))
    (movR32R32Effect 0x10304d 2 2 1)) (xorR32R32Effect 0x10304f 2 2 6)) (andR32R32Effect 0x103051 2
    2 0)) (movR32R32Effect 0x103053 3 8 1)) (andR32R32Effect 0x103056 3 8 6)) (xorR32R32Effect
    0x103059 3 8 2)) (movR32R32Effect 0x10305c 2 2 7)) (rolR32Effect 0x10305e 3 2 5))
    (addR32R32Effect 0x103061 3 8 9)) (addR32R32Effect 0x103064 3 2 8)

private theorem effect053_split : effect053 = Effect.seq prefix053 (addR32Imm32Effect 0x103067 6 2 0x8f1bbcdc) := by rfl

private theorem seqLastWrites {E F : RamState → Effect} {s t : RamState}
    (h : (Effect.seq E F s).Holds s t) :
    Write.AllHold t (F ((E s).after s true)).writes := by
  apply Write.allHold_iff.mpr
  intro w hw
  apply Write.allHold_iff.mp h.writes w
  exact List.mem_append_right _ hw

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem rawR2_053 {s t : RamState}
    (v0 v1 v2 v6 v7 v8 v9 : BitVec 32)
    (h0 : (Operand.reg 0 : Operand 32).read s = v0)
    (h1 : (Operand.reg 1 : Operand 32).read s = v1)
    (h2 : (Operand.reg 2 : Operand 32).read s = v2)
    (h6 : (Operand.reg 6 : Operand 32).read s = v6)
    (h7 : (Operand.reg 7 : Operand 32).read s = v7)
    (h8 : (Operand.reg 8 : Operand 32).read s = v8)
    (h9 : (Operand.reg 9 : Operand 32).read s = v9)
    (he : (effect053 s).Holds s t) :
    (Operand.reg 2 : Operand 32).read t =
      (((v7 &&& v6 ^^^ v2) + v8 + v0.rotateLeft 5 + 0x8f1bbcdc).rotateLeft 5 +
        ((v1.rotateLeft 30 &&& v6 ^^^ ((v1.rotateLeft 30 ^^^ v6) &&& v0)) + v9)) +
        0x8f1bbcdc := by
  x86_norm at h0 h1 h2 h6 h7 h8 h9
  rw [effect053_split] at he
  have hl := seqLastWrites he
  change (Operand.reg 2 : Operand 64).read t =
    (((Operand.reg 2 : Operand 32).read ((prefix053 s).after s true) +
      (0x8f1bbcdc : BitVec 32).signExtend 32).setWidth 64) at hl
  have hr := congrArg (fun x : BitVec 64 ↦ x.setWidth 32) hl
  simp (config := { decide := true, implicitDefEqProofs := false }) only [Operand.read,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq] at hr
  change (Operand.reg 2 : Operand 32).read t =
    (Operand.reg 2 : Operand 32).read ((prefix053 s).after s true) +
      (0x8f1bbcdc : BitVec 32).signExtend 32 at hr
  rw [hr]
  simp (config := { decide := true, implicitDefEqProofs := false }) only
    [x86_compose, prefix053, h0,h1,h2,h6,h7,h8,h9]
  simp (config := { decide := true, implicitDefEqProofs := false }) only [BitVec.setWidth_setWidth_of_le,
    BitVec.setWidth_eq]
  ac_rfl

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem genericR2_053 {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) {s t : RamState}
    (hWork51 : A 51 = (A 50).rotateLeft 5 +
      (((A 47).rotateLeft 30 &&& (A 48).rotateLeft 30) ^^^
        ((A 49 &&& (A 47).rotateLeft 30) ^^^ (A 49 &&& (A 48).rotateLeft 30))) +
      (W 50 + (A 46).rotateLeft 30) + 0x8f1bbcdc)
    (hWork52 : A 52 = (A 51).rotateLeft 5 +
      (((A 49).rotateLeft 30 &&& (A 48).rotateLeft 30) ^^^
        ((((A 49).rotateLeft 30 ^^^ (A 48).rotateLeft 30) &&& A 50))) +
      (W 51 + (A 47).rotateLeft 30) + 0x8f1bbcdc)
    (hw : Write.AllHold s (genericCut053 stack input H A W))
    (he : (effect053 s).Holds s t) :
    (Operand.reg 2 : Operand 32).read t = A 52 := by
  let r51 : BitVec 32 :=
    ((A 47).rotateLeft 30 &&& (A 48).rotateLeft 30 ^^^
      (A 49 &&& (A 47).rotateLeft 30 ^^^ A 49 &&& (A 48).rotateLeft 30)) +
        (W 50 + (A 46).rotateLeft 30) + (A 50).rotateLeft 5 + 0x8f1bbcdc
  let maj52 : BitVec 32 :=
    ((A 49).rotateLeft 30 &&& (A 48).rotateLeft 30) ^^^
      (((A 49).rotateLeft 30 ^^^ (A 48).rotateLeft 30) &&& A 50)
  have hMachine51 : r51 = A 51 := by
    dsimp only [r51]
    calc
      _ = (A 50).rotateLeft 5 +
          ((A 47).rotateLeft 30 &&& (A 48).rotateLeft 30 ^^^
            (A 49 &&& (A 47).rotateLeft 30 ^^^ A 49 &&& (A 48).rotateLeft 30)) +
          (W 50 + (A 46).rotateLeft 30) + 0x8f1bbcdc := by ac_rfl
      _ = A 51 := hWork51.symm
  have hMachine52 :
      r51.rotateLeft 5 + (maj52 + (W 51 + (A 47).rotateLeft 30)) + 0x8f1bbcdc = A 52 := by
    rw [hMachine51, hWork52]
    simp only [maj52, BitVec.add_assoc]
  simp only [genericCut053, Write.AllHold] at hw
  obtain ⟨h0,h1,h2,_,_,h6,h7,h8,h9,_⟩ := hw
  have hr := rawR2_053 (A 50) (A 49)
    ((A 49 &&& (A 47).rotateLeft 30) ^^^ (A 49 &&& (A 48).rotateLeft 30))
    ((A 48).rotateLeft 30) ((A 47).rotateLeft 30)
    (W 50 + (A 46).rotateLeft 30) (W 51 + (A 47).rotateLeft 30)
    h0 h1 h2 h6 h7 h8 h9 he
  exact hr.trans (by simpa only [r51, maj52, BitVec.add_assoc] using hMachine52)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem rawR1_053 {s t : RamState} (v1 : BitVec 32)
    (h1 : (Operand.reg 1 : Operand 32).read s = v1)
    (he : (effect053 s).Holds s t) :
    (Operand.reg 1 : Operand 32).read t = v1.rotateLeft 30 := by
  have hfull : ∀ w ∈ (effect053 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect053
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  x86_norm at h1
  simp only [← ho.read_reg]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [x86_compose, effect053, h1, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem rawR7_053 {s t : RamState} (v0 v2 v6 v7 v8 : BitVec 32)
    (h0 : (Operand.reg 0 : Operand 32).read s = v0)
    (h2 : (Operand.reg 2 : Operand 32).read s = v2)
    (h6 : (Operand.reg 6 : Operand 32).read s = v6)
    (h7 : (Operand.reg 7 : Operand 32).read s = v7)
    (h8 : (Operand.reg 8 : Operand 32).read s = v8)
    (he : (effect053 s).Holds s t) :
    (Operand.reg 7 : Operand 32).read t =
      (v7 &&& v6 ^^^ v2) + v8 + v0.rotateLeft 5 + 0x8f1bbcdc := by
  have hfull : ∀ w ∈ (effect053 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect053
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  x86_norm at h0 h2 h6 h7 h8
  simp only [← ho.read_reg]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [x86_compose, effect053, h0, h2, h6, h7, h8,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem rawM56_053 {s t : RamState} (stack : BitVec 64) (v10 : BitVec 32)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (h10 : (Operand.reg 10 : Operand 32).read s = v10)
    (he : (effect053 s).Holds s t) :
    (Operand.mem (stack + 56) : Operand 32).read t = v10 := by
  have hfull : ∀ w ∈ (effect053 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect053
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  x86_norm at hs h10
  simp only [← ho.read_mem]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [x86_compose, effect053, hs]
  rw [read32_memStore64_low]
  exact h10

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem genericWords053 {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) {s t : RamState}
    (hWork51 : A 51 = (A 50).rotateLeft 5 +
      (((A 47).rotateLeft 30 &&& (A 48).rotateLeft 30) ^^^
        ((A 49 &&& (A 47).rotateLeft 30) ^^^ (A 49 &&& (A 48).rotateLeft 30))) +
      (W 50 + (A 46).rotateLeft 30) + 0x8f1bbcdc)
    (hWork52 : A 52 = (A 51).rotateLeft 5 +
      (((A 49).rotateLeft 30 &&& (A 48).rotateLeft 30) ^^^
        ((((A 49).rotateLeft 30 ^^^ (A 48).rotateLeft 30) &&& A 50))) +
      (W 51 + (A 47).rotateLeft 30) + 0x8f1bbcdc)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hw : Write.AllHold s (genericCut053 stack input H A W))
    (he : (effect053 s).Holds s t) :
    Write.AllHold t (genericCut054 stack input H A W) := by
  have hR2 := genericR2_053 A W hWork51 hWork52 hw he
  have hw0 := hw
  simp only [genericCut053, Write.AllHold] at hw0
  obtain ⟨h0,h1,h2,h3,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,
    hM0,hM8,hM12,hM16,hM24,hM32,hM40,hM48,hM64,hM72,hM80,hM116,hM120,hM124,hM144,hM152⟩ := hw0
  have hR1 := rawR1_053 (A 49) h1 he
  have hR7 := rawR7_053 (A 50)
    ((A 49 &&& (A 47).rotateLeft 30) ^^^ (A 49 &&& (A 48).rotateLeft 30))
    ((A 48).rotateLeft 30) ((A 47).rotateLeft 30)
    (W 50 + (A 46).rotateLeft 30) h0 h2 h6 h7 h8 he
  have hV7 : (Operand.reg 7 : Operand 32).read t = A 51 := by
    calc
      _ = _ := hR7
      _ = _ := by rw [hWork51]; ac_rfl
  have hM56 := rawM56_053 stack (W 51) hs h10 he
  have hfoot : ∀ c ∈ (effect053 s).components,
      c ∈ [.mem ((Operand.reg 4 : Operand 64).read s + 56) 8,
        .reg 1, .reg 2, .reg 7, .reg 8, .flags, .rip] := by
    unfold effect053
    iterate 19 apply components_seq_of
    all_goals simp (config := {decide := true}) only
      [movM64R64Effect_components, andR32R32Effect_components,
       xorR32R32Effect_components, addR32R32Effect_components,
       movR32R32Effect_components, rolR32Effect_components,
       addR32Imm32Effect_components, List.mem_cons, List.not_mem_nil,
       or_false, or_imp, forall_and, forall_eq, or_true]
    all_goals x86_norm
  have ha := he.agrees.mono hfoot
  rw [hs] at ha
  have hmem {n : Nat} (off : BitVec 64) (hb : OffsetsApart 56 8 off (n / 8))
      (hsize : 8 + n / 8 < 2 ^ 64) :
      (Operand.mem (stack + off) : Operand n).read t =
      (Operand.mem (stack + off) : Operand n).read s := by
    apply memLoad_congr
    intro i hi
    apply congrArg (fun b : Option UInt8 ↦ b.getD 0)
    apply ha.byte
    intro c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨j,hj,heq⟩ := hCov
      exact hb.ne stack hj hi hsize heq.symm
    all_goals exact hCov.elim
  simp only [genericCut054, Write.AllHold]
  refine ⟨?f0, ?f1, ?f2, ?f3, ?f4, ?f5, ?f6, ?f7, ?f8, ?f9, ?f10, ?f11, ?f12, ?f13, ?f14, ?f15, ?f16, ?f17, ?f18, ?f19, ?f20, ?f21, ?f22, ?f23, ?f24, ?f25, ?f26, ?f27, ?f28⟩
  case f1 => exact hR1
  case f2 => exact hR2
  case f6 => exact hV7
  case f20 => exact hM56
  case f0 => exact (ha.read (by simp)).trans h0
  case f3 => exact (ha.read (by simp)).trans h3
  case f4 => exact (ha.read (by simp)).trans h5
  case f5 => exact (ha.read (by simp)).trans h6
  case f7 => exact (ha.read (by simp)).trans h11
  case f8 => exact (ha.read (by simp)).trans h12
  case f9 => exact (ha.read (by simp)).trans h13
  case f10 => exact (ha.read (by simp)).trans h14
  case f11 => exact (ha.read (by simp)).trans h15
  case f12 => exact (hmem 0 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM0
  case f13 => exact (hmem 8 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM8
  case f14 => exact (hmem 12 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM12
  case f15 => exact (hmem 16 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM16
  case f16 => exact (hmem 24 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM24
  case f17 => exact (hmem 32 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM32
  case f18 => exact (hmem 40 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM40
  case f19 => exact (hmem 48 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM48
  case f21 => exact (hmem 64 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM64
  case f22 => exact (hmem 72 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM72
  case f23 => exact (hmem 80 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM80
  case f24 => exact (hmem 116 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM116
  case f25 => exact (hmem 120 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM120
  case f26 => exact (hmem 124 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM124
  case f27 => exact (hmem 144 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM144
  case f28 => exact (hmem 152 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM152

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
theorem effect053_words {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut053 stack input H M))
    (he : (effect053 s).Holds s t) :
    Write.AllHold t (cut054 stack input H M) := by
  have hMaj51 (x y z : BitVec 32) :
      Standards.NIST.SHA2.SHA256.Maj x y z =
      (z &&& y) ^^^ ((x &&& z) ^^^ (x &&& y)) := by
    simp only [Standards.NIST.SHA2.SHA256.Maj]
    rw [BitVec.and_comm z y]
    ac_rfl
  have hMaj52 (x y z : BitVec 32) :
      Standards.NIST.SHA2.SHA256.Maj x y z =
      (y &&& z) ^^^ ((y ^^^ z) &&& x) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [Standards.NIST.SHA2.SHA256.Maj, BitVec.getLsbD_xor, BitVec.getLsbD_and]
    cases x.getLsbD i <;> cases y.getLsbD i <;> cases z.getLsbD i <;> decide
  have h51 := workingAfter_step_a_values M H 46 (by decide)
  rw [sha1_f_majority (t := ⟨50, by decide⟩) (by decide) (by decide)] at h51
  simp only [Nat.reduceAdd] at h51
  rw [show K (⟨50, by decide⟩ : Fin 80) = 0x8f1bbcdc by decide, hMaj51] at h51
  have h52 := workingAfter_step_a_values M H 47 (by decide)
  rw [sha1_f_majority (t := ⟨51, by decide⟩) (by decide) (by decide)] at h52
  simp only [Nat.reduceAdd] at h52
  rw [show K (⟨51, by decide⟩ : Fin 80) = 0x8f1bbcdc by decide, hMaj52] at h52
  apply genericWords053 (fun n ↦ (workingAfter M H n).a) (scheduleWord M)
  · calc
      _ = _ := h51
      _ = _ := by ac_rfl
  · calc
      _ = _ := h52
      _ = _ := by ac_rfl
  · exact hf.stackPointer
  · exact hw
  · exact he

end Words053

theorem segment053 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x103031 0x10306d
      cut053 cut054 := by
  have hout : ∀ d : Nat, d ≤ bytes053.length →
      0x103031 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    have hd' : d ≤ 60 := hd
    have hd64 : d < 2 ^ 64 := by omega
    have hsum : 0x103031 + d < 2 ^ 64 := by omega
    have hpc : (0x103031 + BitVec.ofNat 64 d).toNat = 0x103031 + d := by
      change (0x103031 + d % 2 ^ 64) % 2 ^ 64 = 0x103031 + d
      rw [Nat.mod_eq_of_lt hd64, Nat.mod_eq_of_lt hsum]
    exact outsideCompression_ne hOutside (by rw [hpc]; omega) (by rw [hpc]; omega)
  apply Segment.of_block (fun _ _ _ _ => effect053)
    (fun stack input H M => block053 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64
      0x3031) bytes053,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect053_rip he
  · intro stack input H M s t _ hf _ he
    exact effect053_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect053_words hf hw he

end Sha1.Proofs.Compress.Machine

namespace Sha1.Proofs.Compress.Machine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Spec.Program
open Standards.NIST.SHA1 Standards.NIST.SHA2.SHA256 Sha1.Proofs.Compress.Rounds

attribute [local irreducible] workingAfter scheduleWord messageSchedule

def bytes054 : List UInt8 :=
  [0xc1, 0xc0, 0x1e, 0x41, 0x89, 0xc0, 0x41, 0x31, 0xc8, 0x41, 0x21, 0xf8, 0x41, 0x89, 0xc1, 0x41,
    0x21, 0xc9, 0x45, 0x31, 0xc1, 0x44, 0x8b, 0x44, 0x24, 0x8, 0x4c, 0x8b, 0x54, 0x24, 0x20, 0x45,
    0x31, 0xd0, 0x45, 0x31, 0xf2, 0x45, 0x31, 0xe0, 0x45, 0x31, 0xf8, 0x4c, 0x89, 0x7c, 0x24, 0x60,
    0x41, 0xd1, 0xc0, 0x45, 0x31, 0xda, 0x41, 0x31, 0xda, 0x41, 0xd1, 0xc2]

set_option maxHeartbeats 800000 in
def effect054 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq ((rolR32Effect 0x10306d 3 0 30)) (movR32R32Effect 0x103070 3 8 0)) (xorR32R32Effect
    0x103073 3 8 1)) (andR32R32Effect 0x103076 3 8 7)) (movR32R32Effect 0x103079 3 9 0))
    (andR32R32Effect 0x10307c 3 9 1)) (xorR32R32Effect 0x10307f 3 9 8)) (movR32M32Effect 0x103082 8
    (.sib 4 none 0 (.d8 0x8)))) (movR64M64Effect 0x103087 10 (.sib 4 none 0 (.d8 0x20))))
    (xorR32R32Effect 0x10308c 3 8 10)) (xorR32R32Effect 0x10308f 3 10 14)) (xorR32R32Effect 0x103092
    3 8 12)) (xorR32R32Effect 0x103095 3 8 15)) (movM64R64Effect 0x103098 15 (.sib 4 none 0 (.d8
    0x60)))) (rolR32Effect 0x10309d 3 8 1)) (xorR32R32Effect 0x1030a0 3 10 11)) (xorR32R32Effect
    0x1030a3 3 10 3)) (rolR32Effect 0x1030a6 3 10 1)

set_option maxHeartbeats 1600000 in
theorem block054 [Bindings] (boundary : ReturnBoundary)
    (stack input : BitVec 64) (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes054.length → 0x10306d + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x10306d ∧ FrameData stack input M s ∧
        Write.AllHold s (cut054 stack input H M))
      (codeRange 0x10306d bytes054) effect054 := by
  unfold bytes054 at hout ⊢
  sha1_run_begin (rol_r32_imm8_effect_step 0x10306d 0xc0 0x1e (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x103070 0x41 0xc0 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x103073 0x41 0xc8 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (and_r32_r32_rex_effect_step 0x103076 0x41 0xf8 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x103079 0x41 0xc1 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (and_r32_r32_rex_effect_step 0x10307c 0x41 0xc9 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x10307f 0x45 0xc1 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_m32_effect_step 0x103082 0x44 (by unfold RexNoWPrefix; decide +kernel) 0 (.sib 4 none 0 (.d8 0x8)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_m64_effect_step 0x103087 0x4c (by unfold RexWPrefix; decide +kernel) 2 (.sib 4 none 0 (.d8 0x20)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x10308c 0x45 0xd0 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x10308f 0x45 0xf2 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x103092 0x45 0xe0 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x103095 0x45 0xf8 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step 0x103098 0x4c (by unfold RexWPrefix; decide +kernel) 7 (.sib 4 none 0 (.d8 0x60)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_one_rex_effect_step 0x10309d 0x41 0xc0 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x1030a0 0x45 0xda (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x1030a3 0x41 0xda (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_one_rex_effect_step 0x1030a6 0x41 0xc2 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_finish [effect054]

private def genericCut055 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), ((A 50)).rotateLeft 30⟩,
    ⟨(.reg 1 : Operand 32), ((A 49)).rotateLeft 30⟩,
    ⟨(.reg 2 : Operand 32), (A 52)⟩,
    ⟨(.reg 5 : Operand 32), (W 37)⟩,
    ⟨(.reg 6 : Operand 32), ((A 48)).rotateLeft 30⟩,
    ⟨(.reg 7 : Operand 32), (A 51)⟩,
    ⟨(.reg 8 : Operand 32), (W 52)⟩,
    ⟨(.reg 9 : Operand 32), (((A 51) &&& ((A 49)).rotateLeft 30) ^^^ ((A 51) &&& ((A 50)).rotateLeft 30) ^^^ (((A 49)).rotateLeft 30 &&& ((A 50)).rotateLeft 30))⟩,
    ⟨(.reg 10 : Operand 32), (W 54)⟩,
    ⟨(.reg 12 : Operand 32), (W 44)⟩,
    ⟨(.reg 13 : Operand 32), (W 50)⟩,
    ⟨(.reg 14 : Operand 32), (W 40)⟩,
    ⟨(.reg 15 : Operand 32), (W 49)⟩,
    ⟨(.mem (stack + 0) : Operand 32), (W 41)⟩,
    ⟨(.mem (stack + 12) : Operand 32), (W 48)⟩,
    ⟨(.mem (stack + 16) : Operand 32), (W 45)⟩,
    ⟨(.mem (stack + 24) : Operand 32), (W 42)⟩,
    ⟨(.mem (stack + 40) : Operand 32), (W 39)⟩,
    ⟨(.mem (stack + 48) : Operand 32), (W 47)⟩,
    ⟨(.mem (stack + 56) : Operand 32), (W 51)⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), (W 46)⟩,
    ⟨(.mem (stack + 80) : Operand 32), (W 43)⟩,
    ⟨(.mem (stack + 96) : Operand 32), (W 49)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

theorem effect054_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (he : (effect054 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hfoot : ∀ c ∈ (effect054 s).components, c ∈ [.mem ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 96) 8, .reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect054
    iterate 17 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [andR32R32Effect_components, movM64R64Effect_components, movR32M32Effect_components,
        movR32R32Effect_components, movR64M64Effect_components, rolR32Effect_components,
        xorR32R32Effect_components, List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and,
        forall_eq, or_true]
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose]
  have ha := he.agrees.mono hfoot
  rw [hs] at ha
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all (config := {decide := true, implicitDefEqProofs := false}) only [Component.isMem, scratchComponents, x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hCov.elim
      | exact scratchComponents_stack (Or.inl (by decide +kernel)) hCov

theorem effect054_rip {s t : RamState}
    (he : (effect054 s).Holds s t) :
    t.RIP = 0x1030a9 := by
  exact he.rip.trans (by rfl)

section Words054
private theorem obs054 {s t : RamState} (he : (effect054 s).Holds s t) :
    Obs ((effect054 s).after s true) t := by
  apply he.obsAfter _ true
  apply Effect.Local.full
  unfold effect054
  repeat' first | (solve | x86_local) | apply Effect.Local.seq

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem rawR0_054 {s t : RamState} (v0 : BitVec 32)
    (h0 : (Operand.reg 0 : Operand 32).read s = v0)
    (he : (effect054 s).Holds s t) :
    (Operand.reg 0 : Operand 32).read t = v0.rotateLeft 30 := by
  sha1_norm at h0
  have ho := obs054 he
  simp only [← ho.read_reg]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [x86_compose, effect054, h0,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem rawR9_054 {s t : RamState} (v0 v1 v7 : BitVec 32)
    (h0 : (Operand.reg 0 : Operand 32).read s = v0)
    (h1 : (Operand.reg 1 : Operand 32).read s = v1)
    (h7 : (Operand.reg 7 : Operand 32).read s = v7)
    (he : (effect054 s).Holds s t) :
    (Operand.reg 9 : Operand 32).read t = (v0.rotateLeft 30 &&& v1) ^^^ ((v0.rotateLeft 30 ^^^ v1) &&& v7) := by
  sha1_norm at h0 h1 h7
  have ho := obs054 he
  simp only [← ho.read_reg]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [x86_compose, effect054, h0, h1, h7,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem rawR8_054 {s t : RamState} (v12 v15 m8 : BitVec 32) (m32 : BitVec 64) (stack : BitVec 64)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (h12 : (Operand.reg 12 : Operand 32).read s = v12)
    (h15 : (Operand.reg 15 : Operand 32).read s = v15)
    (hm8 : (Operand.mem (stack + 8) : Operand 32).read s = m8)
    (hm32 : (Operand.mem (stack + 32) : Operand 64).read s = m32)
    (he : (effect054 s).Holds s t) :
    (Operand.reg 8 : Operand 32).read t = (m8 ^^^ m32.setWidth 32 ^^^ v12 ^^^ v15).rotateLeft 1 := by
  sha1_norm at hs h12 h15 hm8 hm32
  have ho := obs054 he
  simp only [← ho.read_reg]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [x86_compose, effect054, hs, h12, h15, hm8, hm32,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem rawR10_054 {s t : RamState} (v3 v11 v14 : BitVec 32) (m32 : BitVec 64) (stack : BitVec 64)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (h3 : (Operand.reg 3 : Operand 32).read s = v3)
    (h11 : (Operand.reg 11 : Operand 32).read s = v11)
    (h14 : (Operand.reg 14 : Operand 32).read s = v14)
    (hm32 : (Operand.mem (stack + 32) : Operand 64).read s = m32)
    (he : (effect054 s).Holds s t) :
    (Operand.reg 10 : Operand 32).read t = (m32.setWidth 32 ^^^ v14 ^^^ v11 ^^^ v3).rotateLeft 1 := by
  sha1_norm at hs h3 h11 h14 hm32
  have ho := obs054 he
  simp only [← ho.read_reg]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [x86_compose, effect054, hs, h3, h11, h14, hm32,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem rawM96_054 {s t : RamState} (stack : BitVec 64) (v15 : BitVec 32)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (h15 : (Operand.reg 15 : Operand 32).read s = v15)
    (he : (effect054 s).Holds s t) :
    (Operand.mem (stack + 96) : Operand 32).read t = v15 := by
  sha1_norm at hs h15
  have ho := obs054 he
  simp only [← ho.read_mem]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [x86_compose, effect054, hs, h15,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
  rw [read32_memStore64_low]
  exact h15

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem genericWords054 {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32)
    (hW52 : W 52 = (W 49 ^^^ W 44 ^^^ W 38 ^^^ W 36).rotateLeft 1)
    (hW54 : W 54 = (W 51 ^^^ W 46 ^^^ W 40 ^^^ W 38).rotateLeft 1)
    {s t : RamState}
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hw : Write.AllHold s (genericCut054 stack input H A W))
    (he : (effect054 s).Holds s t) :
    Write.AllHold t (genericCut055 stack input H A W) := by
  simp only [genericCut054, Write.AllHold] at hw
  obtain ⟨h0,h1,h2,h3,h5,h6,h7,h11,h12,h13,h14,h15,
    hM0,hM8,hM12,hM16,hM24,hM32,hM40,hM48,hM56,hM64,hM72,hM80,
    hM116,hM120,hM124,hM144,hM152⟩ := hw
  have lo32 := (read32_of_read64_low
    (s:=s) (a:=stack+32) (v:=(Operand.mem (stack+32) : Operand 64).read s) rfl).symm.trans hM32
  have hR0 := rawR0_054 (A 50) h0 he
  have hR9 := rawR9_054 (A 50) ((A 49).rotateLeft 30) (A 51) h0 h1 h7 he
  have hR8 := rawR8_054 (W 44) (W 49) (W 36)
    ((Operand.mem (stack+32) : Operand 64).read s) stack hs h12 h15 hM8 rfl he
  have hR10 := rawR10_054 (W 51) (W 46) (W 40)
    ((Operand.mem (stack+32) : Operand 64).read s) stack hs h3 h11 h14 rfl he
  have hM96 := rawM96_054 stack (W 49) hs h15 he
  have hSchedule52 : (W 36 ^^^ W 38 ^^^ W 44 ^^^ W 49).rotateLeft 1 = W 52 := by
    rw [hW52]
    congr 1
    ac_rfl
  have hSchedule54 : (W 38 ^^^ W 40 ^^^ W 46 ^^^ W 51).rotateLeft 1 = W 54 := by
    rw [hW54]
    congr 1
    ac_rfl
  rw [lo32, hSchedule52] at hR8
  rw [lo32, hSchedule54] at hR10
  have hMaj (a b c : BitVec 32) :
      (c &&& b ^^^ ((c ^^^ b) &&& a)) =
        (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and]
    cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.getLsbD i <;> decide
  rw [hMaj] at hR9
  have hfoot : ∀ c ∈ (effect054 s).components,
      c ∈ [.mem ((Operand.reg 4 : Operand 64).read s + 96) 8,
        .reg 0, .reg 8, .reg 9, .reg 10, .flags, .rip] := by
    unfold effect054
    iterate 17 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [movM64R64Effect_components, andR32R32Effect_components,
       xorR32R32Effect_components, movR32M32Effect_components,
       movR32R32Effect_components, movR64M64Effect_components,
       rolR32Effect_components, List.mem_cons, List.not_mem_nil,
       or_false, or_imp, forall_and, forall_eq, or_true]
    all_goals sha1_norm
  have ha := he.agrees.mono hfoot
  rw [hs] at ha
  have hmem {n : Nat} (off : BitVec 64) (hb : OffsetsApart 96 8 off (n / 8))
      (hsize : 8 + n / 8 < 2 ^ 64) :
      (Operand.mem (stack + off) : Operand n).read t =
      (Operand.mem (stack + off) : Operand n).read s := by
    apply memLoad_congr
    intro i hi
    apply congrArg (fun b : Option UInt8 ↦ b.getD 0)
    apply ha.byte
    intro c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨j,hj,heq⟩ := hCov
      exact hb.ne stack hj hi hsize heq.symm
    all_goals exact hCov.elim
  simp only [genericCut055, Write.AllHold]
  refine ⟨?f0, ?f1, ?f2, ?f3, ?f4, ?f5, ?f6, ?f7, ?f8, ?f9, ?f10, ?f11, ?f12, ?f13, ?f14, ?f15, ?f16, ?f17, ?f18, ?f19, ?f20, ?f21, ?f22, ?f23, ?f24, ?f25, ?f26, ?f27, ?f28⟩
  case f0 => exact hR0
  case f1 => exact (ha.read (by simp)).trans h1
  case f2 => exact (ha.read (by simp)).trans h2
  case f3 => exact (ha.read (by simp)).trans h5
  case f4 => exact (ha.read (by simp)).trans h6
  case f5 => exact (ha.read (by simp)).trans h7
  case f6 => exact hR8
  case f7 => exact hR9
  case f8 => exact hR10
  case f9 => exact (ha.read (by simp)).trans h12
  case f10 => exact (ha.read (by simp)).trans h13
  case f11 => exact (ha.read (by simp)).trans h14
  case f12 => exact (ha.read (by simp)).trans h15
  case f13 => exact (hmem 0 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM0
  case f14 => exact (hmem 12 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM12
  case f15 => exact (hmem 16 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM16
  case f16 => exact (hmem 24 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM24
  case f17 => exact (hmem 40 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM40
  case f18 => exact (hmem 48 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM48
  case f19 => exact (hmem 56 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM56
  case f20 => exact (hmem 64 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM64
  case f21 => exact (hmem 72 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM72
  case f22 => exact (hmem 80 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM80
  case f23 => exact hM96
  case f24 => exact (hmem 116 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM116
  case f25 => exact (hmem 120 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM120
  case f26 => exact (hmem 124 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM124
  case f27 => exact (hmem 144 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM144
  case f28 => exact (hmem 152 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM152

theorem effect054_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16}
    {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut054 stack input H M))
    (he : (effect054 s).Holds s t) :
    Write.AllHold t (cut055 stack input H M) := by
  let A : Nat → BitVec 32 := fun n ↦ (workingAfter M H n).a
  let W : Fin 80 → BitVec 32 := scheduleWord M
  have hW52 : W 52 = (W 49 ^^^ W 44 ^^^ W 38 ^^^ W 36).rotateLeft 1 := by
    dsimp [W]
    change scheduleWord M (⟨52, by decide⟩ : Fin 80) = _
    rw [scheduleWord_recurrence M ⟨52, by decide⟩ (by decide)]
    simp only [Nat.reduceSub]
    rw [sha1Rotl_eq_rotateLeft 1 _ (by decide)]
    rfl
  have hW54 : W 54 = (W 51 ^^^ W 46 ^^^ W 40 ^^^ W 38).rotateLeft 1 := by
    dsimp [W]
    change scheduleWord M (⟨54, by decide⟩ : Fin 80) = _
    rw [scheduleWord_recurrence M ⟨54, by decide⟩ (by decide)]
    simp only [Nat.reduceSub]
    rw [sha1Rotl_eq_rotateLeft 1 _ (by decide)]
    rfl
  have hpre : Write.AllHold s (genericCut054 stack input H A W) := by
    change Write.AllHold s (cut054 stack input H M)
    exact hw
  have hraw := genericWords054 A W hW52 hW54 hf.stackPointer hpre he
  change Write.AllHold t (cut055 stack input H M)
  exact hraw
end Words054

theorem segment054 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x10306d 0x1030a9
      cut054 cut055 := by
  have hout : ∀ d : Nat, d ≤ bytes054.length →
      0x10306d + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    have hd' : d ≤ 60 := hd
    have hd64 : d < 2 ^ 64 := by omega
    have hsum : 0x10306d + d < 2 ^ 64 := by omega
    have hpc : (0x10306d + BitVec.ofNat 64 d).toNat = 0x10306d + d := by
      change (0x10306d + d % 2 ^ 64) % 2 ^ 64 = 0x10306d + d
      rw [Nat.mod_eq_of_lt hd64, Nat.mod_eq_of_lt hsum]
    exact outsideCompression_ne hOutside (by rw [hpc]; omega) (by rw [hpc]; omega)
  apply Segment.of_block (fun _ _ _ _ => effect054)
    (fun stack input H M => block054 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64
      0x306d) bytes054,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect054_rip he
  · intro stack input H M s t _ hf _ he
    exact effect054_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect054_words hf hw he

end Sha1.Proofs.Compress.Machine

namespace Sha1.Proofs.Compress.Machine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Spec.Program
open Standards.NIST.SHA1 Standards.NIST.SHA2.SHA256 Sha1.Proofs.Compress.Rounds

attribute [local irreducible] workingAfter scheduleWord messageSchedule

def bytes055 : List UInt8 :=
  [0x4c, 0x89, 0x54, 0x24, 0x20, 0xc1, 0xc7, 0x1e, 0x44, 0x1, 0xc6, 0x44, 0x89, 0xc3, 0x44, 0x89,
    0x44, 0x24, 0x8, 0x44, 0x1, 0xce, 0x41, 0x89, 0xd0, 0x41, 0xc1, 0xc0, 0x5, 0x44, 0x1, 0xc6,
    0x81, 0xc6, 0xdc, 0xbc, 0x1b, 0x8f, 0x41, 0x89, 0xf9, 0x41, 0x31, 0xc1, 0x41, 0x21, 0xd1, 0x45,
    0x8d, 0x4, 0x2, 0x21, 0xf8, 0x44, 0x31, 0xc8, 0x41, 0x89, 0xe9, 0x4c, 0x8b, 0x54, 0x24, 0x28,
    0x45, 0x31, 0xd1]

set_option maxHeartbeats 800000 in
def effect055 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq ((movM64R64Effect 0x1030a9 10 (.sib 4 none 0 (.d8 0x20)))) (rolR32Effect
    0x1030ae 3 7 30)) (addR32R32Effect 0x1030b1 3 6 8)) (movR32R32Effect 0x1030b4 3 3 8))
    (movM32R32Effect 0x1030b7 8 (.sib 4 none 0 (.d8 0x8)))) (addR32R32Effect 0x1030bc 3 6 9))
    (movR32R32Effect 0x1030bf 3 8 2)) (rolR32Effect 0x1030c2 4 8 5)) (addR32R32Effect 0x1030c6 3 6
    8)) (addR32Imm32Effect 0x1030c9 6 6 0x8f1bbcdc)) (movR32R32Effect 0x1030cf 3 9 7))
    (xorR32R32Effect 0x1030d2 3 9 0)) (andR32R32Effect 0x1030d5 3 9 2)) (leaR32Effect 0x1030d8 4 8
    (.sib 10 (some 0) 0 .none))) (andR32R32Effect 0x1030dc 2 0 7)) (xorR32R32Effect 0x1030de 3 0 9))
    (movR32R32Effect 0x1030e1 3 9 5)) (movR64M64Effect 0x1030e4 10 (.sib 4 none 0 (.d8 0x28))))
    (xorR32R32Effect 0x1030e9 3 9 10)

set_option maxHeartbeats 1600000 in
theorem block055 [Bindings] (boundary : ReturnBoundary)
    (stack input : BitVec 64) (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes055.length → 0x1030a9 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x1030a9 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut055 stack input H M))
      (codeRange 0x1030a9 bytes055) effect055 := by
  unfold bytes055 at hout ⊢
  sha1_run_begin (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step 0x1030a9 0x4c (by unfold RexWPrefix; decide +kernel) 2 (.sib 4 none 0 (.d8 0x20)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x1030ae 0xc7 0x1e (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x1030b1 0x44 0xc6 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x1030b4 0x44 0xc3 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m32_r32_effect_step 0x1030b7 0x44 (by unfold RexNoWPrefix; decide +kernel) 0 (.sib 4 none 0 (.d8 0x8)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x1030bc 0x44 0xce (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x1030bf 0x41 0xd0 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_imm8_rex_effect_step 0x1030c2 0x41 0xc0 0x5 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x1030c6 0x44 0xc6 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_imm32_effect_step 0x1030c9 0xc6 0x8f1bbcdc (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x1030cf 0x41 0xf9 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x1030d2 0x41 0xc1 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (and_r32_r32_rex_effect_step 0x1030d5 0x41 0xd1 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (lea_r32_rex_effect_step 0x1030d8 0x45 (by unfold RexNoWPrefix; decide +kernel) 0 (.sib 10 (some 0) 0 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (and_r32_r32_effect_step 0x1030dc 0xf8 (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x1030de 0x44 0xc8 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x1030e1 0x41 0xe9 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_m64_effect_step 0x1030e4 0x4c (by unfold RexWPrefix; decide +kernel) 2 (.sib 4 none 0 (.d8 0x28)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x1030e9 0x45 0xd1 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_finish [effect055]

private def genericCut056 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), (((A 52) &&& ((A 50)).rotateLeft 30) ^^^ ((A 52) &&& ((A 51)).rotateLeft
    30) ^^^ (((A 50)).rotateLeft 30 &&& ((A 51)).rotateLeft 30))⟩,
    ⟨(.reg 1 : Operand 32), ((A 49)).rotateLeft 30⟩,
    ⟨(.reg 2 : Operand 32), (A 52)⟩,
    ⟨(.reg 3 : Operand 32), (W 52)⟩,
    ⟨(.reg 6 : Operand 32), (A 53)⟩,
    ⟨(.reg 7 : Operand 32), ((A 51)).rotateLeft 30⟩,
    ⟨(.reg 8 : Operand 32), ((W 54) + ((A 50)).rotateLeft 30)⟩,
    ⟨(.reg 9 : Operand 32), ((W 37) ^^^ (W 39))⟩,
    ⟨(.reg 10 : Operand 32), (W 39)⟩,
    ⟨(.reg 12 : Operand 32), (W 44)⟩,
    ⟨(.reg 13 : Operand 32), (W 50)⟩,
    ⟨(.reg 14 : Operand 32), (W 40)⟩,
    ⟨(.reg 15 : Operand 32), (W 49)⟩,
    ⟨(.mem (stack + 0) : Operand 32), (W 41)⟩,
    ⟨(.mem (stack + 8) : Operand 32), (W 52)⟩,
    ⟨(.mem (stack + 12) : Operand 32), (W 48)⟩,
    ⟨(.mem (stack + 16) : Operand 32), (W 45)⟩,
    ⟨(.mem (stack + 24) : Operand 32), (W 42)⟩,
    ⟨(.mem (stack + 32) : Operand 32), (W 54)⟩,
    ⟨(.mem (stack + 48) : Operand 32), (W 47)⟩,
    ⟨(.mem (stack + 56) : Operand 32), (W 51)⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), (W 46)⟩,
    ⟨(.mem (stack + 80) : Operand 32), (W 43)⟩,
    ⟨(.mem (stack + 96) : Operand 32), (W 49)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

theorem effect055_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (he : (effect055 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hfoot : ∀ c ∈ (effect055 s).components, c ∈ [.mem ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 8) 4, .mem ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 32) 8, .reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect055
    iterate 18 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [leaR32Effect_components, addR32Imm32Effect_components, addR32R32Effect_components,
        andR32R32Effect_components, movM32R32Effect_components, movM64R64Effect_components,
        movR32R32Effect_components, movR64M64Effect_components, rolR32Effect_components,
        xorR32R32Effect_components, List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and,
        forall_eq, or_true]
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose]
  have ha := he.agrees.mono hfoot
  rw [hs] at ha
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all (config := {decide := true, implicitDefEqProofs := false}) only [Component.isMem, scratchComponents, x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hCov.elim
      | exact scratchComponents_stack (Or.inl (by decide +kernel)) hCov
      | exact scratchComponents_stack (Or.inl (by decide +kernel)) hCov

theorem effect055_rip {s t : RamState}
    (he : (effect055 s).Holds s t) :
    t.RIP = 0x1030ec := by
  exact he.rip.trans (by rfl)

section Words055
set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem obs055 {s t : RamState} (he : (effect055 s).Holds s t) :
    Obs ((effect055 s).after s true) t := by
  apply he.obsAfter _ true
  apply Effect.Local.full
  unfold effect055
  repeat' first | (solve | x86_local) | apply Effect.Local.seq

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem rawR0_055 {s t : RamState}
    (v0 v2 v7 : BitVec 32)
    (h0 : (Operand.reg 0 : Operand 32).read s = v0)
    (h2 : (Operand.reg 2 : Operand 32).read s = v2)
    (h7 : (Operand.reg 7 : Operand 32).read s = v7)
    (he : (effect055 s).Holds s t) :
    (Operand.reg 0 : Operand 32).read t = (v0 &&& v7.rotateLeft 30) ^^^ ((v7.rotateLeft 30 ^^^ v0) &&& v2) := by
  simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose] at h0 h2 h7
  have ho := obs055 he
  simp only [← ho.read_reg]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [x86_compose, effect055, leaSpec, h0, h2, h7,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, BitVec.add_zero]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem rawR3_055 {s t : RamState}
    (v8 : BitVec 32)
    (h8 : (Operand.reg 8 : Operand 32).read s = v8)
    (he : (effect055 s).Holds s t) :
    (Operand.reg 3 : Operand 32).read t = v8 := by
  simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose] at h8
  have ho := obs055 he
  simp only [← ho.read_reg]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [x86_compose, effect055, leaSpec, h8,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, BitVec.add_zero]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem rawR6_055 {s t : RamState}
    (v2 v6 v8 v9 : BitVec 32)
    (h2 : (Operand.reg 2 : Operand 32).read s = v2)
    (h6 : (Operand.reg 6 : Operand 32).read s = v6)
    (h8 : (Operand.reg 8 : Operand 32).read s = v8)
    (h9 : (Operand.reg 9 : Operand 32).read s = v9)
    (he : (effect055 s).Holds s t) :
    (Operand.reg 6 : Operand 32).read t = v6 + v8 + v9 + v2.rotateLeft 5 + 0x8f1bbcdc := by
  simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose] at h2 h6 h8 h9
  have ho := obs055 he
  simp only [← ho.read_reg]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [x86_compose, effect055, leaSpec, h2, h6, h8, h9,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, BitVec.add_zero]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem rawR7_055 {s t : RamState}
    (v7 : BitVec 32)
    (h7 : (Operand.reg 7 : Operand 32).read s = v7)
    (he : (effect055 s).Holds s t) :
    (Operand.reg 7 : Operand 32).read t = v7.rotateLeft 30 := by
  simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose] at h7
  have ho := obs055 he
  simp only [← ho.read_reg]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [x86_compose, effect055, leaSpec, h7,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, BitVec.add_zero]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem rawR8_055 {s t : RamState}
    (v0 v10 : BitVec 32)
    (h0 : (Operand.reg 0 : Operand 32).read s = v0)
    (h10 : (Operand.reg 10 : Operand 32).read s = v10)
    (he : (effect055 s).Holds s t) :
    (Operand.reg 8 : Operand 32).read t = v10 + v0 := by
  simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose] at h0 h10
  have ho := obs055 he
  simp only [← ho.read_reg]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [x86_compose, effect055, leaSpec, h0, h10,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, BitVec.add_zero]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem rawR9_055 {s t : RamState}
    (v5 : BitVec 32)
    (stack : BitVec 64)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (h5 : (Operand.reg 5 : Operand 32).read s = v5)
    (m40 : BitVec 32)
    (hm40 : (memLoad s.external (stack+40) 64).setWidth 32 = m40)
    (he : (effect055 s).Holds s t) :
    (Operand.reg 9 : Operand 32).read t = v5 ^^^ m40 := by
  simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose] at hs h5 hm40
  have ho := obs055 he
  simp only [← ho.read_reg]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [x86_compose, effect055, leaSpec, hs, h5, hm40,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, BitVec.add_zero]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem rawR10_055 {s t : RamState}
    (stack : BitVec 64)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (m40 : BitVec 32)
    (hm40 : (memLoad s.external (stack+40) 64).setWidth 32 = m40)
    (he : (effect055 s).Holds s t) :
    (Operand.reg 10 : Operand 32).read t = m40 := by
  simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose] at hs hm40
  have ho := obs055 he
  simp only [← ho.read_reg]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [x86_compose, effect055, leaSpec, hs, hm40,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, BitVec.add_zero]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem rawM8_055 {s t : RamState}
    (v8 : BitVec 32)
    (stack : BitVec 64)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (h8 : (Operand.reg 8 : Operand 32).read s = v8)
    (he : (effect055 s).Holds s t) :
    (Operand.mem (stack+8) : Operand 32).read t = v8 := by
  simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose] at hs h8
  have ho := obs055 he
  simp only [← ho.read_mem]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [x86_compose, effect055, leaSpec, hs, h8,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, BitVec.add_zero,
      extractLsb'_zero_eq_setWidth]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem rawM32_055 {s t : RamState}
    (v10 : BitVec 32)
    (stack : BitVec 64)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (h10 : (Operand.reg 10 : Operand 32).read s = v10)
    (he : (effect055 s).Holds s t) :
    (Operand.mem (stack+32) : Operand 32).read t = v10 := by
  simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose] at hs h10
  have ho := obs055 he
  simp only [← ho.read_mem]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [x86_compose, effect055, leaSpec, hs, h10,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, BitVec.add_zero, read32_memStore64_low,
      extractLsb'_zero_eq_setWidth]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem genericWords055 {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32)
    (hWork53 : A 53 = (A 52).rotateLeft 5 +
      ((A 51 &&& (A 49).rotateLeft 30) ^^^
        (A 51 &&& (A 50).rotateLeft 30) ^^^
        ((A 49).rotateLeft 30 &&& (A 50).rotateLeft 30)) +
      (A 48).rotateLeft 30 + 0x8f1bbcdc + W 52)
    {s t : RamState}
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hw : Write.AllHold s (genericCut055 stack input H A W))
    (he : (effect055 s).Holds s t) :
    Write.AllHold t (genericCut056 stack input H A W) := by
  have hw0 := hw
  simp only [genericCut055, Write.AllHold] at hw0
  obtain ⟨h0,h1,h2,h5,h6,h7,h8,h9,h10,h12,h13,h14,h15,
    hM0,hM12,hM16,hM24,hM40,hM48,hM56,hM64,hM72,hM80,hM96,
    hM116,hM120,hM124,hM144,hM152⟩ := hw0
  have hLow40 := (read32_of_read64_low
    (rfl : (Operand.mem (stack+40) : Operand 64).read s = _)).symm
  have hm40 : (memLoad s.external (stack+40) 64).setWidth 32 = W 39 :=
    hLow40.trans hM40
  have hR0 := rawR0_055 ((A 50).rotateLeft 30) (A 52) (A 51) h0 h2 h7 he
  have hR3 := rawR3_055 (W 52) h8 he
  have hR6 := rawR6_055 (A 52) ((A 48).rotateLeft 30) (W 52)
    (((A 51 &&& (A 49).rotateLeft 30) ^^^ (A 51 &&& (A 50).rotateLeft 30)) ^^^
     ((A 49).rotateLeft 30 &&& (A 50).rotateLeft 30)) h2 h6 h8 h9 he
  have hR7 := rawR7_055 (A 51) h7 he
  have hR8 := rawR8_055 ((A 50).rotateLeft 30) (W 54) h0 h10 he
  have hR9 := rawR9_055 (W 37) stack hs h5 (W 39) hm40 he
  have hR10 := rawR10_055 stack hs (W 39) hm40 he
  have hM8 := rawM8_055 (W 52) stack hs h8 he
  have hM32 := rawM32_055 (W 54) stack hs h10 he
  have hMaj (a b c : BitVec 32) :
      (b &&& c) ^^^ ((c ^^^ b) &&& a) =
      (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and]
    cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.getLsbD i <;> decide
  rw [hMaj] at hR0
  have hV6 : (Operand.reg 6 : Operand 32).read t = A 53 := by
    calc
      _ = _ := hR6
      _ = _ := by rw [hWork53]; ac_rfl
  have hfoot : ∀ c ∈ (effect055 s).components,
      c ∈ [.mem ((Operand.reg 4 : Operand 64).read s + 8) 4,
        .mem ((Operand.reg 4 : Operand 64).read s + 32) 8,
        .reg 0,.reg 3,.reg 6,.reg 7,.reg 8,.reg 9,.reg 10,.flags,.rip] := by
    unfold effect055
    iterate 18 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [movM64R64Effect_components, rolR32Effect_components, addR32R32Effect_components,
       movR32R32Effect_components, movM32R32Effect_components, addR32Imm32Effect_components,
       xorR32R32Effect_components, andR32R32Effect_components,
       leaR32Effect_components,
       movR64M64Effect_components,
       List.mem_cons,List.not_mem_nil,or_false,or_imp,forall_and,forall_eq,or_true]
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose]
  have ha := he.agrees.mono hfoot
  rw [hs] at ha
  have hmem {n : Nat} (off : BitVec 64)
      (h8 : OffsetsApart 8 4 off (n / 8))
      (h32 : OffsetsApart 32 8 off (n / 8))
      (hsize : 8 + n / 8 < 2 ^ 64) :
      (Operand.mem (stack+off) : Operand n).read t =
      (Operand.mem (stack+off) : Operand n).read s := by
    apply memLoad_congr
    intro i hi
    apply congrArg (fun b : Option UInt8 => b.getD 0)
    apply ha.byte
    intro c hc hCov
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨j,hj,heq⟩ := hCov
      exact h8.ne stack hj hi (by omega) heq.symm
    · obtain ⟨j,hj,heq⟩ := hCov
      exact h32.ne stack hj hi hsize heq.symm
    all_goals exact hCov.elim
  simp only [genericCut056,Write.AllHold]
  refine ⟨?f0, ?f1, ?f2, ?f3, ?f4, ?f5, ?f6, ?f7, ?f8, ?f9, ?f10, ?f11, ?f12, ?f13, ?f14, ?f15, ?f16, ?f17, ?f18, ?f19, ?f20, ?f21, ?f22, ?f23, ?f24, ?f25, ?f26, ?f27, ?f28, ?f29⟩
  case f0 => exact hR0
  case f1 => exact (ha.read (by simp)).trans h1
  case f2 => exact (ha.read (by simp)).trans h2
  case f3 => exact hR3
  case f4 => exact hV6
  case f5 => exact hR7
  case f6 => exact hR8
  case f7 => exact hR9
  case f8 => exact hR10
  case f9 => exact (ha.read (by simp)).trans h12
  case f10 => exact (ha.read (by simp)).trans h13
  case f11 => exact (ha.read (by simp)).trans h14
  case f12 => exact (ha.read (by simp)).trans h15
  case f13 => exact (hmem 0 (by unfold OffsetsApart; decide +kernel) (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM0
  case f14 => exact hM8
  case f15 => exact (hmem 12 (by unfold OffsetsApart; decide +kernel) (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM12
  case f16 => exact (hmem 16 (by unfold OffsetsApart; decide +kernel) (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM16
  case f17 => exact (hmem 24 (by unfold OffsetsApart; decide +kernel) (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM24
  case f18 => exact hM32
  case f19 => exact (hmem 48 (by unfold OffsetsApart; decide +kernel) (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM48
  case f20 => exact (hmem 56 (by unfold OffsetsApart; decide +kernel) (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM56
  case f21 => exact (hmem 64 (by unfold OffsetsApart; decide +kernel) (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM64
  case f22 => exact (hmem 72 (by unfold OffsetsApart; decide +kernel) (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM72
  case f23 => exact (hmem 80 (by unfold OffsetsApart; decide +kernel) (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM80
  case f24 => exact (hmem 96 (by unfold OffsetsApart; decide +kernel) (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM96
  case f25 => exact (hmem 116 (by unfold OffsetsApart; decide +kernel) (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM116
  case f26 => exact (hmem 120 (by unfold OffsetsApart; decide +kernel) (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM120
  case f27 => exact (hmem 124 (by unfold OffsetsApart; decide +kernel) (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM124
  case f28 => exact (hmem 144 (by unfold OffsetsApart; decide +kernel) (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM144
  case f29 => exact (hmem 152 (by unfold OffsetsApart; decide +kernel) (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM152

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
theorem effect055_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16}
    {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut055 stack input H M))
    (he : (effect055 s).Holds s t) :
    Write.AllHold t (cut056 stack input H M) := by
  let A : Nat → BitVec 32 := fun n ↦ (workingAfter M H n).a
  let W : Fin 80 → BitVec 32 := scheduleWord M
  have hWork53 : A 53 = (A 52).rotateLeft 5 +
      ((A 51 &&& (A 49).rotateLeft 30) ^^^
        (A 51 &&& (A 50).rotateLeft 30) ^^^
        ((A 49).rotateLeft 30 &&& (A 50).rotateLeft 30)) +
      (A 48).rotateLeft 30 + 0x8f1bbcdc + W 52 := by
    dsimp [A, W]
    rw [workingAfter_step_a_values M H 48 (by decide)]
    rw [sha1_f_majority (t := ⟨52, by decide⟩) (by decide) (by decide)]
    rw [sha1Maj_eq_xor]
    have hMajCanonical (x y z : BitVec 32) :
        (x &&& y) ^^^ ((x ^^^ y) &&& z) =
          (x &&& z) ^^^ (x &&& y) ^^^ (y &&& z) := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and]
      cases x.getLsbD i <;> cases y.getLsbD i <;> cases z.getLsbD i <;> decide
    rw [hMajCanonical]
    simp [K]
    ac_rfl
  have hpre : Write.AllHold s (genericCut055 stack input H A W) := by
    change Write.AllHold s (cut055 stack input H M)
    exact hw
  have hraw := genericWords055 A W hWork53 hf.stackPointer hpre he
  change Write.AllHold t (cut056 stack input H M)
  exact hraw
end Words055

theorem segment055 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x1030a9 0x1030ec
      cut055 cut056 := by
  have hout : ∀ d : Nat, d ≤ bytes055.length →
      0x1030a9 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    have hd' : d ≤ 67 := hd
    have hd64 : d < 2 ^ 64 := by omega
    have hsum : 0x1030a9 + d < 2 ^ 64 := by omega
    have hpc : (0x1030a9 + BitVec.ofNat 64 d).toNat = 0x1030a9 + d := by
      change (0x1030a9 + d % 2 ^ 64) % 2 ^ 64 = 0x1030a9 + d
      rw [Nat.mod_eq_of_lt hd64, Nat.mod_eq_of_lt hsum]
    exact outsideCompression_ne hOutside (by rw [hpc]; omega) (by rw [hpc]; omega)
  apply Segment.of_block (fun _ _ _ _ => effect055)
    (fun stack input H M => block055 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64
      0x30a9) bytes055,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect055_rip he
  · intro stack input H M s t _ hf _ he
    exact effect055_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect055_words hf hw he

end Sha1.Proofs.Compress.Machine

namespace Sha1.Proofs.Compress.Machine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Spec.Program
open Standards.NIST.SHA1 Standards.NIST.SHA2.SHA256 Sha1.Proofs.Compress.Rounds

attribute [local irreducible] workingAfter scheduleWord messageSchedule

def bytes056 : List UInt8 :=
  [0x44, 0x33, 0x4c, 0x24, 0x10, 0x4d, 0x89, 0xeb, 0x4c, 0x89, 0x6c, 0x24, 0x58, 0x45, 0x31, 0xd9,
    0x41, 0xd1, 0xc1, 0x44, 0x1, 0xc9, 0x44, 0x89, 0xcd, 0x44, 0x89, 0x4c, 0x24, 0x4, 0x1, 0xc1,
    0x4c, 0x89, 0xd0, 0x33, 0x4, 0x24, 0x33, 0x44, 0x24, 0x30, 0x31, 0xd8, 0xd1, 0xc0, 0x49, 0x89,
    0xc2, 0x89, 0xf0, 0xc1, 0xc0, 0x5, 0xc1, 0xc2, 0x1e, 0x1, 0xc8, 0x5, 0xdc, 0xbc, 0x1b, 0x8f]

set_option maxHeartbeats 800000 in
def effect056 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq (Effect.seq ((xorR32M32Effect 0x1030ec 9 (.sib 4 none 0 (.d8 0x10))))
    (movR64R64Effect 0x1030f1 11 13)) (movM64R64Effect 0x1030f4 13 (.sib 4 none 0 (.d8 0x58))))
    (xorR32R32Effect 0x1030f9 3 9 11)) (rolR32Effect 0x1030fc 3 9 1)) (addR32R32Effect 0x1030ff 3 1
    9)) (movR32R32Effect 0x103102 3 5 9)) (movM32R32Effect 0x103105 9 (.sib 4 none 0 (.d8 0x4))))
    (addR32R32Effect 0x10310a 2 1 0)) (movR64R64Effect 0x10310c 0 10)) (xorR32M32LowEffect 0x10310f
    0 (.sib 4 none 0 .none))) (xorR32M32LowEffect 0x103112 0 (.sib 4 none 0 (.d8 0x30))))
    (xorR32R32Effect 0x103116 2 0 3)) (rolR32Effect 0x103118 2 0 1)) (movR64R64Effect 0x10311a 10
    0)) (movR32R32Effect 0x10311d 2 0 6)) (rolR32Effect 0x10311f 3 0 5)) (rolR32Effect 0x103122 3 2
    30)) (addR32R32Effect 0x103125 2 0 1)) (addEaxImm32Effect 0x103127 0x8f1bbcdc)

set_option maxHeartbeats 1600000 in
theorem block056 [Bindings] (boundary : ReturnBoundary)
    (stack input : BitVec 64) (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes056.length → 0x1030ec + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x1030ec ∧ FrameData stack input M s ∧
        Write.AllHold s (cut056 stack input H M))
      (codeRange 0x1030ec bytes056) effect056 := by
  unfold bytes056 at hout ⊢
  sha1_run_begin (xor_r32_m32_effect_step 0x1030ec 0x44 (by unfold RexNoWPrefix; decide +kernel) 1 (.sib 4 none 0 (.d8 0x10)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_r64_effect_step 0x1030f1 0x4d 0xeb (by unfold RexWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step 0x1030f4 0x4c (by unfold RexWPrefix; decide +kernel) 5 (.sib 4 none 0 (.d8 0x58)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x1030f9 0x45 0xd9 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_one_rex_effect_step 0x1030fc 0x41 0xc1 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x1030ff 0x44 0xc9 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x103102 0x44 0xcd (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m32_r32_effect_step 0x103105 0x44 (by unfold RexNoWPrefix; decide +kernel) 1 (.sib 4 none 0 (.d8 0x4)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x10310a 0xc1 (by decide +kernel))
  sha1_run_then (mov_r64_r64_effect_step 0x10310c 0x4c 0xd0 (by unfold RexWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_m32_low_effect_step 0x10310f 0 (.sib 4 none 0 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_m32_low_effect_step 0x103112 0 (.sib 4 none 0 (.d8 0x30)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x103116 0xd8 (by decide +kernel))
  sha1_run_then (rol_r32_one_effect_step 0x103118 0xc0 (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_r64_effect_step 0x10311a 0x49 0xc2 (by unfold RexWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_effect_step 0x10311d 0xf0 (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x10311f 0xc0 0x5 (by decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x103122 0xc2 0x1e (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x103125 0xc8 (by decide +kernel))
  sha1_run_then (add_eax_imm32_effect_step 0x103127 0x8f1bbcdc)
  sha1_run_finish [effect056]

private def genericCut057 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), (A 54)⟩,
    ⟨(.reg 2 : Operand 32), ((A 52)).rotateLeft 30⟩,
    ⟨(.reg 5 : Operand 32), (W 53)⟩,
    ⟨(.reg 6 : Operand 32), (A 53)⟩,
    ⟨(.reg 7 : Operand 32), ((A 51)).rotateLeft 30⟩,
    ⟨(.reg 8 : Operand 32), ((W 54) + ((A 50)).rotateLeft 30)⟩,
    ⟨(.reg 10 : Operand 32), (W 55)⟩,
    ⟨(.reg 11 : Operand 32), (W 50)⟩,
    ⟨(.reg 12 : Operand 32), (W 44)⟩,
    ⟨(.reg 14 : Operand 32), (W 40)⟩,
    ⟨(.reg 15 : Operand 32), (W 49)⟩,
    ⟨(.mem (stack + 0) : Operand 32), (W 41)⟩,
    ⟨(.mem (stack + 4) : Operand 32), (W 53)⟩,
    ⟨(.mem (stack + 8) : Operand 32), (W 52)⟩,
    ⟨(.mem (stack + 12) : Operand 32), (W 48)⟩,
    ⟨(.mem (stack + 16) : Operand 32), (W 45)⟩,
    ⟨(.mem (stack + 24) : Operand 32), (W 42)⟩,
    ⟨(.mem (stack + 32) : Operand 32), (W 54)⟩,
    ⟨(.mem (stack + 48) : Operand 32), (W 47)⟩,
    ⟨(.mem (stack + 56) : Operand 32), (W 51)⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), (W 46)⟩,
    ⟨(.mem (stack + 80) : Operand 32), (W 43)⟩,
    ⟨(.mem (stack + 88) : Operand 32), (W 50)⟩,
    ⟨(.mem (stack + 96) : Operand 32), (W 49)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

theorem effect056_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (he : (effect056 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hfoot : ∀ c ∈ (effect056 s).components, c ∈ [.mem ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 4) 4, .mem ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 88) 8, .reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect056
    iterate 19 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [addEaxImm32Effect_components, addR32R32Effect_components, movM32R32Effect_components,
        movM64R64Effect_components, movR32R32Effect_components, movR64R64Effect_components,
        rolR32Effect_components, xorR32M32Effect_components, xorR32M32LowEffect,
        xorR32R32Effect_components, List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and,
        forall_eq, or_true]
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose]
  have ha := he.agrees.mono hfoot
  rw [hs] at ha
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all (config := {decide := true, implicitDefEqProofs := false}) only [Component.isMem, scratchComponents, x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hCov.elim
      | exact scratchComponents_stack (Or.inl (by decide +kernel)) hCov
      | exact scratchComponents_stack (Or.inl (by decide +kernel)) hCov

theorem effect056_rip {s t : RamState}
    (he : (effect056 s).Holds s t) :
    t.RIP = 0x10312c := by
  exact he.rip.trans (by rfl)

section Words056
private theorem work056_actual (M : Vector (BitVec 32) 16)
    (H : Vector (BitVec 32) 5) :
    (workingAfter M H 54).a =
      ((workingAfter M H 53).a).rotateLeft 5 +
        (((workingAfter M H 52).a &&& ((workingAfter M H 50).a).rotateLeft 30) ^^^
          ((workingAfter M H 52).a &&& ((workingAfter M H 51).a).rotateLeft 30) ^^^
          (((workingAfter M H 50).a).rotateLeft 30 &&& ((workingAfter M H 51).a).rotateLeft 30)) +
        ((workingAfter M H 49).a).rotateLeft 30 + K ⟨53, by decide⟩ +
        scheduleWord M 53 := by
  rw [workingAfter_step_a_values M H 49 (by decide)]
  have hF := sha1_f_majority (t := ⟨53, by decide⟩)
    (x := (workingAfter M H 52).a)
    (y := ((workingAfter M H 51).a).rotateLeft 30)
    (z := ((workingAfter M H 50).a).rotateLeft 30) (by decide) (by decide)
  simp only [Nat.reduceAdd]
  rw [hF]
  have hMaj (x y z : BitVec 32) :
      Standards.NIST.SHA2.SHA256.Maj x y z = (x &&& z) ^^^ (x &&& y) ^^^ (z &&& y) := by
    rw [sha1Maj_eq_xor]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and]
    cases x.getLsbD i <;> cases y.getLsbD i <;> cases z.getLsbD i <;> decide
  rw [hMaj]
  ac_rfl

private theorem schedule053_actual (M : Vector (BitVec 32) 16) :
    scheduleWord M 53 =
      (scheduleWord M 50 ^^^ scheduleWord M 45 ^^^ scheduleWord M 39 ^^^
        scheduleWord M 37).rotateLeft 1 := by
  change scheduleWord M (⟨53, by decide⟩ : Fin 80) = _
  rw [scheduleWord_recurrence M ⟨53, by decide⟩ (by decide),
    sha1Rotl_eq_rotateLeft 1 _ (by decide)]
  simp only [Nat.reduceSub]
  have h50 : (⟨50, by decide⟩ : Fin 80) = 50 := by decide
  have h45 : (⟨45, by decide⟩ : Fin 80) = 45 := by decide
  have h39 : (⟨39, by decide⟩ : Fin 80) = 39 := by decide
  have h37 : (⟨37, by decide⟩ : Fin 80) = 37 := by decide
  simp only [h50, h45, h39, h37]

private theorem schedule055_actual (M : Vector (BitVec 32) 16) :
    scheduleWord M 55 =
      (scheduleWord M 52 ^^^ scheduleWord M 47 ^^^ scheduleWord M 41 ^^^
        scheduleWord M 39).rotateLeft 1 := by
  change scheduleWord M (⟨55, by decide⟩ : Fin 80) = _
  rw [scheduleWord_recurrence M ⟨55, by decide⟩ (by decide),
    sha1Rotl_eq_rotateLeft 1 _ (by decide)]
  simp only [Nat.reduceSub]
  have h52 : (⟨52, by decide⟩ : Fin 80) = 52 := by decide
  have h47 : (⟨47, by decide⟩ : Fin 80) = 47 := by decide
  have h41 : (⟨41, by decide⟩ : Fin 80) = 41 := by decide
  have h39 : (⟨39, by decide⟩ : Fin 80) = 39 := by decide
  simp only [h52, h47, h41, h39]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem full056 (s : RamState) : ∀ w ∈ (effect056 s).writes, w.Full := by
  apply Effect.Local.full
  unfold effect056
  repeat' first | (solve | x86_local) | apply Effect.Local.seq

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem rawR0_056 {s t : RamState} (stack : BitVec 64)
    (v0 v1 v6 v9 v13 m16 : BitVec 32)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (h0 : (Operand.reg 0 : Operand 32).read s = v0)
    (h1 : (Operand.reg 1 : Operand 32).read s = v1)
    (h6 : (Operand.reg 6 : Operand 32).read s = v6)
    (h9 : (Operand.reg 9 : Operand 32).read s = v9)
    (h13 : (Operand.reg 13 : Operand 32).read s = v13)
    (hM16 : (Operand.mem (stack + 16) : Operand 32).read s = m16)
    (he : (effect056 s).Holds s t) :
    (Operand.reg 0 : Operand 32).read t = v6.rotateLeft 5 + (v1 + ((v9 ^^^ m16) ^^^ v13).rotateLeft 1 + v0) + 0x8f1bbcdc := by
  have ho := he.obsAfter (full056 s) true
  sha1_norm at hs h0 h1 h6 h9 h13 hM16
  simp only [← ho.read_reg]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [x86_compose, effect056, hs, h0, h1, h6, h9, h13, hM16, BitVec.setWidth_setWidth_of_le,
      BitVec.setWidth_eq]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem rawR2_056 {s t : RamState}
    (v2 : BitVec 32)
    (h2 : (Operand.reg 2 : Operand 32).read s = v2)
    (he : (effect056 s).Holds s t) :
    (Operand.reg 2 : Operand 32).read t = v2.rotateLeft 30 := by
  have ho := he.obsAfter (full056 s) true
  sha1_norm at h2
  simp only [← ho.read_reg]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [x86_compose, effect056, h2, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem rawR5_056 {s t : RamState} (stack : BitVec 64)
    (v9 v13 m16 : BitVec 32)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (h9 : (Operand.reg 9 : Operand 32).read s = v9)
    (h13 : (Operand.reg 13 : Operand 32).read s = v13)
    (hM16 : (Operand.mem (stack + 16) : Operand 32).read s = m16)
    (he : (effect056 s).Holds s t) :
    (Operand.reg 5 : Operand 32).read t = ((v9 ^^^ m16) ^^^ v13).rotateLeft 1 := by
  have ho := he.obsAfter (full056 s) true
  sha1_norm at hs h9 h13 hM16
  simp only [← ho.read_reg]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [x86_compose, effect056, hs, h9, h13, hM16, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem rawR10_056 {s t : RamState} (stack : BitVec 64)
    (v3 v10 m0 m48 : BitVec 32)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (h3 : (Operand.reg 3 : Operand 32).read s = v3)
    (h10 : (Operand.reg 10 : Operand 32).read s = v10)
    (hM0 : (Operand.mem (stack + 0) : Operand 32).read s = m0)
    (hM48 : (Operand.mem (stack + 48) : Operand 32).read s = m48)
    (he : (effect056 s).Holds s t) :
    (Operand.reg 10 : Operand 32).read t = (((v10 ^^^ m0) ^^^ m48) ^^^ v3).rotateLeft 1 := by
  have ho := he.obsAfter (full056 s) true
  sha1_norm at hs h3 h10 hM0 hM48
  simp only [← ho.read_reg]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [x86_compose, effect056, hs, h3, h10, hM0, hM48, BitVec.setWidth_setWidth_of_le,
      BitVec.setWidth_eq]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem rawR11_056 {s t : RamState}
    (v13 : BitVec 32)
    (h13 : (Operand.reg 13 : Operand 32).read s = v13)
    (he : (effect056 s).Holds s t) :
    (Operand.reg 11 : Operand 32).read t = v13 := by
  have ho := he.obsAfter (full056 s) true
  sha1_norm at h13
  simp only [← ho.read_reg]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [x86_compose, effect056, h13, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem rawM4_056 {s t : RamState} (stack : BitVec 64)
    (v9 v13 m16 : BitVec 32)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (h9 : (Operand.reg 9 : Operand 32).read s = v9)
    (h13 : (Operand.reg 13 : Operand 32).read s = v13)
    (hM16 : (Operand.mem (stack + 16) : Operand 32).read s = m16)
    (he : (effect056 s).Holds s t) :
    (Operand.mem (stack + 4) : Operand 32).read t = ((v9 ^^^ m16) ^^^ v13).rotateLeft 1 := by
  have ho := he.obsAfter (full056 s) true
  sha1_norm at hs h9 h13 hM16
  simp only [← ho.read_mem]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [x86_compose, effect056, hs, h9, h13, hM16, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem rawM88_056 {s t : RamState} (stack : BitVec 64)
    (v13 : BitVec 32)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (h13 : (Operand.reg 13 : Operand 32).read s = v13)
    (he : (effect056 s).Holds s t) :
    (Operand.mem (stack + 88) : Operand 32).read t = v13 := by
  have ho := he.obsAfter (full056 s) true
  sha1_norm at hs h13
  simp only [← ho.read_mem]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [x86_compose, effect056, hs, h13, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
  rw [read32_memStore64_low]
  exact h13

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem genericWords056 {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32)
    (hWork : A 54 = (A 53).rotateLeft 5 +
      (((A 52) &&& (A 50).rotateLeft 30) ^^^
        ((A 52) &&& (A 51).rotateLeft 30) ^^^
        ((A 50).rotateLeft 30 &&& (A 51).rotateLeft 30)) +
      (A 49).rotateLeft 30 + K ⟨53, by decide⟩ + W 53)
    (hSchedule : W 53 = (W 50 ^^^ W 45 ^^^ W 39 ^^^ W 37).rotateLeft 1)
    (hSchedule55 : W 55 = (W 52 ^^^ W 47 ^^^ W 41 ^^^ W 39).rotateLeft 1)
    {s t : RamState}
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hw : Write.AllHold s (genericCut056 stack input H A W))
    (he : (effect056 s).Holds s t) :
    Write.AllHold t (genericCut057 stack input H A W) := by
  simp only [genericCut056, Write.AllHold] at hw
  obtain ⟨h0,h1,h2,h3,h6,h7,h8,h9,h10,h12,h13,h14,h15,
    hM0,hM8,hM12,hM16,hM24,hM32,hM48,hM56,hM64,hM72,hM80,hM96,
    hM116,hM120,hM124,hM144,hM152⟩ := hw
  have h53 : (((W 37 ^^^ W 39) ^^^ W 45) ^^^ W 50).rotateLeft 1 = W 53 := by
    rw [hSchedule]
    congr 1
    ac_rfl
  have h55 : (((W 39 ^^^ W 41) ^^^ W 47) ^^^ W 52).rotateLeft 1 = W 55 := by
    rw [hSchedule55]
    congr 1
    ac_rfl
  have hR0 := rawR0_056 stack
    ((A 52 &&& (A 50).rotateLeft 30) ^^^ (A 52 &&& (A 51).rotateLeft 30) ^^^
      ((A 50).rotateLeft 30 &&& (A 51).rotateLeft 30))
    ((A 49).rotateLeft 30) (A 53) (W 37 ^^^ W 39) (W 50) (W 45)
    hs h0 h1 h6 h9 h13 hM16 he
  rw [h53] at hR0
  have hV0 : (Operand.reg 0 : Operand 32).read t = A 54 := by
    rw [hR0, hWork]
    change _ = _ + _ + _ + (0x8f1bbcdc : BitVec 32) + _
    ac_rfl
  have hR2 := rawR2_056 (A 52) h2 he
  have hR5 := rawR5_056 stack (W 37 ^^^ W 39) (W 50) (W 45) hs h9 h13 hM16 he
  rw [h53] at hR5
  have hR10 := rawR10_056 stack (W 52) (W 39) (W 41) (W 47) hs h3 h10 hM0 hM48 he
  rw [h55] at hR10
  have hR11 := rawR11_056 (W 50) h13 he
  have hM4 := rawM4_056 stack (W 37 ^^^ W 39) (W 50) (W 45) hs h9 h13 hM16 he
  rw [h53] at hM4
  have hM88 := rawM88_056 stack (W 50) hs h13 he
  have hfoot : ∀ c ∈ (effect056 s).components,
      c ∈ [.mem ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 4) 4,
        .mem ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 88) 8,
        .reg 0, .reg 1, .reg 2, .reg 3, .reg 5,
        .reg 9, .reg 10, .reg 11, .flags, .rip] := by
    unfold effect056
    iterate 19 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [addEaxImm32Effect_components, addR32R32Effect_components, movM32R32Effect_components,
        movM64R64Effect_components, movR32R32Effect_components, movR64R64Effect_components,
        rolR32Effect_components, xorR32M32Effect_components, xorR32M32LowEffect,
        xorR32R32Effect_components, List.mem_cons, List.not_mem_nil, or_false, or_imp,
        forall_and, forall_eq, or_true]
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose]
  have ha := he.agrees.mono hfoot
  rw [hs] at ha
  have hmem {n : Nat} (off : BitVec 64)
      (h4 : OffsetsApart 4 4 off (n / 8))
      (h88 : OffsetsApart 88 8 off (n / 8))
      (hsize : 8 + n / 8 < 2 ^ 64) :
      (Operand.mem (stack + off) : Operand n).read t =
        (Operand.mem (stack + off) : Operand n).read s := by
    have hsize4 : 4 + n / 8 < 2 ^ 64 := by omega
    apply memLoad_congr
    intro i hi
    apply congrArg (fun b : Option UInt8 ↦ b.getD 0)
    apply ha.byte
    intro c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨j,hj,heq⟩ := hCov
      exact h4.ne stack hj hi hsize4 heq.symm
    · obtain ⟨j,hj,heq⟩ := hCov
      exact h88.ne stack hj hi hsize heq.symm
    all_goals exact hCov.elim
  simp only [genericCut057, Write.AllHold]
  refine ⟨?f0, ?f1, ?f2, ?f3, ?f4, ?f5, ?f6, ?f7, ?f8, ?f9, ?f10,
    ?f11, ?f12, ?f13, ?f14, ?f15, ?f16, ?f17, ?f18, ?f19, ?f20,
    ?f21, ?f22, ?f23, ?f24, ?f25, ?f26, ?f27, ?f28, ?f29⟩
  case f11 => exact (hmem 0 (by unfold OffsetsApart; decide +kernel)
    (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM0
  case f13 => exact (hmem 8 (by unfold OffsetsApart; decide +kernel)
    (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM8
  case f14 => exact (hmem 12 (by unfold OffsetsApart; decide +kernel)
    (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM12
  case f15 => exact (hmem 16 (by unfold OffsetsApart; decide +kernel)
    (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM16
  case f16 => exact (hmem 24 (by unfold OffsetsApart; decide +kernel)
    (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM24
  case f17 => exact (hmem 32 (by unfold OffsetsApart; decide +kernel)
    (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM32
  case f18 => exact (hmem 48 (by unfold OffsetsApart; decide +kernel)
    (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM48
  case f19 => exact (hmem 56 (by unfold OffsetsApart; decide +kernel)
    (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM56
  case f20 => exact (hmem 64 (by unfold OffsetsApart; decide +kernel)
    (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM64
  case f21 => exact (hmem 72 (by unfold OffsetsApart; decide +kernel)
    (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM72
  case f22 => exact (hmem 80 (by unfold OffsetsApart; decide +kernel)
    (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM80
  case f24 => exact (hmem 96 (by unfold OffsetsApart; decide +kernel)
    (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM96
  case f25 => exact (hmem 116 (by unfold OffsetsApart; decide +kernel)
    (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM116
  case f26 => exact (hmem 120 (by unfold OffsetsApart; decide +kernel)
    (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM120
  case f27 => exact (hmem 124 (by unfold OffsetsApart; decide +kernel)
    (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM124
  case f28 => exact (hmem 144 (by unfold OffsetsApart; decide +kernel)
    (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM144
  case f29 => exact (hmem 152 (by unfold OffsetsApart; decide +kernel)
    (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM152
  case f0 => exact hV0
  case f1 => exact hR2
  case f2 => exact hR5
  case f6 => exact hR10
  case f7 => exact hR11
  case f12 => exact hM4
  case f23 => exact hM88
  case f3 => exact (ha.read (by simp)).trans h6
  case f4 => exact (ha.read (by simp)).trans h7
  case f5 => exact (ha.read (by simp)).trans h8
  case f8 => exact (ha.read (by simp)).trans h12
  case f9 => exact (ha.read (by simp)).trans h14
  case f10 => exact (ha.read (by simp)).trans h15

theorem effect056_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16}
    {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut056 stack input H M))
    (he : (effect056 s).Holds s t) :
    Write.AllHold t (cut057 stack input H M) := by
  have hWork : (workingAfter M H 54).a =
      ((workingAfter M H 53).a).rotateLeft 5 +
        (((workingAfter M H 52).a &&& ((workingAfter M H 50).a).rotateLeft 30) ^^^
          ((workingAfter M H 52).a &&& ((workingAfter M H 51).a).rotateLeft 30) ^^^
          (((workingAfter M H 50).a).rotateLeft 30 &&& ((workingAfter M H 51).a).rotateLeft 30)) +
        ((workingAfter M H 49).a).rotateLeft 30 + K ⟨53, by decide⟩ +
        scheduleWord M 53 := by
    exact work056_actual M H
  have hSchedule : scheduleWord M 53 =
      (scheduleWord M 50 ^^^ scheduleWord M 45 ^^^ scheduleWord M 39 ^^^
        scheduleWord M 37).rotateLeft 1 := by
    exact schedule053_actual M
  have hSchedule55 := schedule055_actual M
  have hpre : Write.AllHold s
      (genericCut056 stack input H (fun n ↦ (workingAfter M H n).a) (scheduleWord M)) := by
    change Write.AllHold s (cut056 stack input H M)
    exact hw
  have hmodel := genericWords056 (fun n ↦ (workingAfter M H n).a) (scheduleWord M)
    hWork hSchedule hSchedule55 hf.stackPointer hpre he
  change Write.AllHold t (cut057 stack input H M) at hmodel
  exact hmodel
end Words056

theorem segment056 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x1030ec 0x10312c
      cut056 cut057 := by
  have hout : ∀ d : Nat, d ≤ bytes056.length →
      0x1030ec + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    have hd' : d ≤ 64 := hd
    have hd64 : d < 2 ^ 64 := by omega
    have hsum : 0x1030ec + d < 2 ^ 64 := by omega
    have hpc : (0x1030ec + BitVec.ofNat 64 d).toNat = 0x1030ec + d := by
      change (0x1030ec + d % 2 ^ 64) % 2 ^ 64 = 0x1030ec + d
      rw [Nat.mod_eq_of_lt hd64, Nat.mod_eq_of_lt hsum]
    exact outsideCompression_ne hOutside (by rw [hpc]; omega) (by rw [hpc]; omega)
  apply Segment.of_block (fun _ _ _ _ => effect056)
    (fun stack input H M => block056 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64
      0x30ec) bytes056,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect056_rip he
  · intro stack input H M s t _ hf _ he
    exact effect056_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect056_words hf hw he

end Sha1.Proofs.Compress.Machine

namespace Sha1.Proofs.Compress.Machine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Spec.Program
open Standards.NIST.SHA1 Sha1.Proofs.Compress.Rounds

attribute [local irreducible] workingAfter scheduleWord messageSchedule

def bytes057 : List UInt8 :=
  [0x89, 0xd1, 0x31, 0xf9, 0x21, 0xf1, 0x45, 0x8d, 0xc, 0x3a, 0x4d, 0x89, 0xd5, 0x4c, 0x89, 0x54,
    0x24, 0x28, 0x21, 0xd7, 0x31, 0xcf, 0x44, 0x1, 0xc7, 0x89, 0xc1, 0xc1, 0xc1, 0x5, 0x44, 0x8d,
    0x4, 0x39, 0x41, 0x81, 0xc0, 0xdc, 0xbc, 0x1b, 0x8f]

def effect057 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq (Effect.seq (Effect.seq (movR32R32Effect 0x10312c 2 1 2)
    (xorR32R32Effect 0x10312e 2 1 7)) (andR32R32Effect 0x103130 2 1 6)) (leaR32Effect 0x103132 4 9
    (.sib 10 (some 7) 0 .none))) (movR64R64Effect 0x103136 13 10)) (movM64R64Effect 0x103139 10
    (.sib 4 none 0 (.d8 0x28)))) (andR32R32Effect 0x10313e 2 7 2)) (xorR32R32Effect 0x103140 2 7 1))
    (addR32R32Effect 0x103142 3 7 8)) (movR32R32Effect 0x103145 2 1 0)) (rolR32Effect 0x103147 3 1
    5)) (leaR32Effect 0x10314a 4 8 (.sib 1 (some 7) 0 .none))) (addR32Imm32Effect 0x10314e 7 8
    0x8f1bbcdc)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem block057 [Bindings] (boundary : ReturnBoundary) (stack input : BitVec 64)
    (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes057.length →
      0x10312c + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x10312c ∧ FrameData stack input M s ∧
        Write.AllHold s (cut057 stack input H M))
      (codeRange 0x10312c bytes057) effect057 := by
  unfold bytes057 at hout ⊢
  sha1_run_begin (mov_r32_r32_effect_step 0x10312c 0xd1 (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x10312e 0xf9 (by decide +kernel))
  sha1_run_then (and_r32_r32_effect_step 0x103130 0xf1 (by decide +kernel))
  sha1_run_then (lea_r32_rex_effect_step 0x103132 0x45 (by decide +kernel) 1 (.sib 10 (some 7) 0 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_r64_effect_step 0x103136 0x4d 0xd5 (by decide +kernel) (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step 0x103139 0x4c (by decide +kernel) 2 (.sib 4 none 0 (.d8 0x28)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (and_r32_r32_effect_step 0x10313e 0xd7 (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x103140 0xcf (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x103142 0x44 0xc7 (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_effect_step 0x103145 0xc1 (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x103147 0xc1 5 (by decide +kernel) (by decide +kernel))
  sha1_run_then (lea_r32_rex_effect_step 0x10314a 0x44 (by decide +kernel) 0 (.sib 1 (some 7) 0 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_imm32_rex_effect_step 0x10314e 0x41 0xc0 0x8f1bbcdc (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_finish [effect057]

theorem effect057_rip {s t : RamState} (he : (effect057 s).Holds s t) :
    t.RIP = 0x103155 := he.rip.trans rfl

private theorem footprint057 (s : RamState) :
    ∀ c ∈ (effect057 s).components,
      c ∈ [.mem ((Operand.reg 4 : Operand 64).read s + 40) 8,
        .reg 1, .reg 7, .reg 8, .reg 9, .reg 13, .flags, .rip] := by
  unfold effect057
  iterate 12 apply components_seq_of
  all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
    [movM64R64Effect_components, movR32R32Effect_components, movR64R64Effect_components,
      xorR32R32Effect_components, andR32R32Effect_components, leaR32Effect_components,
      addR32R32Effect_components, rolR32Effect_components, addR32Imm32Effect_components,
      List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and, forall_eq, or_true]
  all_goals sha1_norm

theorem effect057_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (he : (effect057 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have ha := he.agrees.mono (footprint057 s)
  rw [hs] at ha
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all only [Component.isMem, scratchComponents, x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact scratchComponents_stack (Or.inl (by decide +kernel)) hCov
    all_goals exact hCov.elim

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
theorem effect057_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut057 stack input H M))
    (he : (effect057 s).Holds s t) :
    Write.AllHold t (cut058 stack input H M) := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hfull : ∀ w ∈ (effect057 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect057
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  have ha := he.agrees.mono (footprint057 s)
  rw [hs] at ha
  have hmem {n : Nat} (off : BitVec 64) (hb : OffsetsApart 40 8 off (n / 8))
      (hsize : 8 + n / 8 < 2 ^ 64) :
      (Operand.mem (stack + off) : Operand n).read t =
      (Operand.mem (stack + off) : Operand n).read s := by
    apply memLoad_congr
    intro i hi
    apply congrArg (fun b : Option UInt8 ↦ b.getD 0)
    apply ha.byte
    intro c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨j, hj, heq⟩ := hCov
      exact hb.ne stack hj hi hsize heq.symm
    all_goals exact hCov.elim
  simp only [cut057, Write.AllHold] at hw
  obtain ⟨h0,h2,h5,h6,h7,h8,h10,h11,h12,h14,h15,
    hM0,hM4,hM8,hM12,hM16,hM24,hM32,hM48,hM56,hM64,hM72,hM80,hM88,hM96,
    hM116,hM120,hM124,hM144,hM152⟩ := hw
  have hWork := workingAfter_step_a_values M H 50 (by decide +kernel)
  rw [sha1_f_majority (by decide) (by decide), sha1_K_majority (by decide) (by decide)] at hWork
  simp only [Nat.reduceAdd] at hWork
  have hMaj (x y z : BitVec 32) :
      Standards.NIST.SHA2.SHA256.Maj x y z = (z &&& y) ^^^ ((y ^^^ z) &&& x) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [Standards.NIST.SHA2.SHA256.Maj, BitVec.getLsbD_xor, BitVec.getLsbD_and]
    cases x.getLsbD i <;> cases y.getLsbD i <;> cases z.getLsbD i <;> decide
  rw [hMaj] at hWork
  change (workingAfter M H 55).a =
    (workingAfter M H 54).a.rotateLeft 5 +
      ((workingAfter M H 51).a.rotateLeft 30 &&& (workingAfter M H 52).a.rotateLeft 30 ^^^
        ((workingAfter M H 52).a.rotateLeft 30 ^^^ (workingAfter M H 51).a.rotateLeft 30) &&&
          (workingAfter M H 53).a) +
      (workingAfter M H 50).a.rotateLeft 30 + 0x8f1bbcdc#32 + scheduleWord M 54 at hWork
  simp only [cut058, Write.AllHold]
  refine ⟨?f0, ?f1, ?f2, ?f3, ?f4, ?f5, ?f6, ?f7, ?f8, ?f9, ?f10, ?f11, ?f12, ?f13, ?f14, ?f15, ?f16, ?f17, ?f18, ?f19, ?f20, ?f21, ?f22, ?f23, ?f24, ?f25, ?f26, ?f27, ?f28, ?f29, ?f30⟩
  case f0 => exact (ha.read (by simp)).trans h0
  case f1 => exact (ha.read (by simp)).trans h2
  case f2 => exact (ha.read (by simp)).trans h5
  case f3 => exact (ha.read (by simp)).trans h6
  case f4 =>
    sha1_norm at hs h0 h2 h5 h6 h7 h8 h10
    simp only [← ho.read_reg]
    sha1_norm [effect057, leaSpec, hs, h0, h2, h5, h6, h7, h8, h10,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, BitVec.add_zero]
    rw [hWork]
    ac_rfl
  case f5 =>
    sha1_norm at hs h0 h2 h5 h6 h7 h8 h10
    simp only [← ho.read_reg]
    sha1_norm [effect057, leaSpec, hs, h0, h2, h5, h6, h7, h8, h10,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, BitVec.add_zero]
  case f6 => exact (ha.read (by simp)).trans h11
  case f7 => exact (ha.read (by simp)).trans h12
  case f8 =>
    sha1_norm at hs h0 h2 h5 h6 h7 h8 h10
    simp only [← ho.read_reg]
    sha1_norm [effect057, leaSpec, hs, h0, h2, h5, h6, h7, h8, h10,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, BitVec.add_zero]
  case f9 => exact (ha.read (by simp)).trans h14
  case f10 => exact (ha.read (by simp)).trans h15
  case f11 => exact (hmem 0 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM0
  case f12 => exact (hmem 4 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM4
  case f13 => exact (hmem 8 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM8
  case f14 => exact (hmem 12 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM12
  case f15 => exact (hmem 16 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM16
  case f16 => exact (hmem 24 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM24
  case f17 => exact (hmem 32 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM32
  case f18 =>
    sha1_norm at hs h0 h2 h5 h6 h7 h8 h10
    simp only [← ho.read_mem]
    sha1_norm [effect057, leaSpec, hs, h0, h2, h5, h6, h7, h8, h10,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, BitVec.add_zero]
    rw [read32_memStore64_low]
    rw [← BitVec.setWidth_eq_extractLsb' (by decide)]
    exact h10
  case f19 => exact (hmem 48 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM48
  case f20 => exact (hmem 56 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM56
  case f21 => exact (hmem 64 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM64
  case f22 => exact (hmem 72 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM72
  case f23 => exact (hmem 80 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM80
  case f24 => exact (hmem 88 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM88
  case f25 => exact (hmem 96 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM96
  case f26 => exact (hmem 116 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM116
  case f27 => exact (hmem 120 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM120
  case f28 => exact (hmem 124 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM124
  case f29 => exact (hmem 144 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM144
  case f30 => exact (hmem 152 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM152

theorem segment057 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x10312c 0x103155 cut057 cut058 := by
  have hout : ∀ d : Nat, d ≤ bytes057.length →
      0x10312c + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    have hd' : d ≤ 41 := hd
    have hd64 : d < 2 ^ 64 := by omega
    have hsum : 0x10312c + d < 2 ^ 64 := by omega
    have hpc : (0x10312c + BitVec.ofNat 64 d).toNat = 0x10312c + d := by
      change (0x10312c + d % 2 ^ 64) % 2 ^ 64 = 0x10312c + d
      rw [Nat.mod_eq_of_lt hd64, Nat.mod_eq_of_lt hsum]
    exact outsideCompression_ne hOutside (by rw [hpc]; omega) (by rw [hpc]; omega)
  apply Segment.of_block (fun _ _ _ _ ↦ effect057)
    (fun stack input H M ↦ block057 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 0x312c) bytes057,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect057_rip he
  · intro stack input H M s t _ hf _ he
    exact effect057_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect057_words hf hw he

end Sha1.Proofs.Compress.Machine

namespace Sha1.Proofs.Compress.Machine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Spec.Program
open Standards.NIST.SHA1 Standards.NIST.SHA2.SHA256 Sha1.Proofs.Compress.Rounds

attribute [local irreducible] workingAfter scheduleWord messageSchedule

def bytes058 : List UInt8 :=
  [0xc1, 0xc6, 0x1e, 0x89, 0xf1, 0x31, 0xd1, 0x21, 0xc1, 0x89, 0xf7, 0x21, 0xd7, 0x31, 0xcf, 0x44,
    0x1, 0xcf, 0x44, 0x89, 0xc1, 0xc1, 0xc1, 0x5, 0x1, 0xcf, 0x81, 0xc7, 0xdc, 0xbc, 0x1b, 0x8f]

set_option maxHeartbeats 800000 in
def effect058 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq (Effect.seq ((rolR32Effect 0x103155 3 6 30)) (movR32R32Effect 0x103158 2
    1 6)) (xorR32R32Effect 0x10315a 2 1 2)) (andR32R32Effect 0x10315c 2 1 0)) (movR32R32Effect
    0x10315e 2 7 6)) (andR32R32Effect 0x103160 2 7 2)) (xorR32R32Effect 0x103162 2 7 1))
    (addR32R32Effect 0x103164 3 7 9)) (movR32R32Effect 0x103167 3 1 8)) (rolR32Effect 0x10316a 3 1
    5)) (addR32R32Effect 0x10316d 2 7 1)) (addR32Imm32Effect 0x10316f 6 7 0x8f1bbcdc)

set_option maxHeartbeats 1600000 in
theorem block058 [Bindings] (boundary : ReturnBoundary)
    (stack input : BitVec 64) (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes058.length → 0x103155 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x103155 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut058 stack input H M))
      (codeRange 0x103155 bytes058) effect058 := by
  unfold bytes058 at hout ⊢
  sha1_run_begin (rol_r32_imm8_effect_step 0x103155 0xc6 0x1e (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_effect_step 0x103158 0xf1 (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x10315a 0xd1 (by decide +kernel))
  sha1_run_then (and_r32_r32_effect_step 0x10315c 0xc1 (by decide +kernel))
  sha1_run_then (mov_r32_r32_effect_step 0x10315e 0xf7 (by decide +kernel))
  sha1_run_then (and_r32_r32_effect_step 0x103160 0xd7 (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x103162 0xcf (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x103164 0x44 0xcf (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x103167 0x44 0xc1 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x10316a 0xc1 0x5 (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x10316d 0xcf (by decide +kernel))
  sha1_run_then (add_r32_imm32_effect_step 0x10316f 0xc7 0x8f1bbcdc (by decide +kernel) (by decide +kernel))
  sha1_run_finish [effect058]

private def genericCut058 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), (A 54)⟩,
    ⟨(.reg 2 : Operand 32), ((A 52)).rotateLeft 30⟩,
    ⟨(.reg 5 : Operand 32), (W 53)⟩,
    ⟨(.reg 6 : Operand 32), (A 53)⟩,
    ⟨(.reg 8 : Operand 32), (A 55)⟩,
    ⟨(.reg 9 : Operand 32), ((W 55) + ((A 51)).rotateLeft 30)⟩,
    ⟨(.reg 11 : Operand 32), (W 50)⟩,
    ⟨(.reg 12 : Operand 32), (W 44)⟩,
    ⟨(.reg 13 : Operand 32), (W 55)⟩,
    ⟨(.reg 14 : Operand 32), (W 40)⟩,
    ⟨(.reg 15 : Operand 32), (W 49)⟩,
    ⟨(.mem (stack + 0) : Operand 32), (W 41)⟩,
    ⟨(.mem (stack + 4) : Operand 32), (W 53)⟩,
    ⟨(.mem (stack + 8) : Operand 32), (W 52)⟩,
    ⟨(.mem (stack + 12) : Operand 32), (W 48)⟩,
    ⟨(.mem (stack + 16) : Operand 32), (W 45)⟩,
    ⟨(.mem (stack + 24) : Operand 32), (W 42)⟩,
    ⟨(.mem (stack + 32) : Operand 32), (W 54)⟩,
    ⟨(.mem (stack + 40) : Operand 32), (W 55)⟩,
    ⟨(.mem (stack + 48) : Operand 32), (W 47)⟩,
    ⟨(.mem (stack + 56) : Operand 32), (W 51)⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), (W 46)⟩,
    ⟨(.mem (stack + 80) : Operand 32), (W 43)⟩,
    ⟨(.mem (stack + 88) : Operand 32), (W 50)⟩,
    ⟨(.mem (stack + 96) : Operand 32), (W 49)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

private def genericCut059 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), (A 54)⟩,
    ⟨(.reg 2 : Operand 32), ((A 52)).rotateLeft 30⟩,
    ⟨(.reg 5 : Operand 32), (W 53)⟩,
    ⟨(.reg 6 : Operand 32), ((A 53)).rotateLeft 30⟩,
    ⟨(.reg 7 : Operand 32), (A 56)⟩,
    ⟨(.reg 8 : Operand 32), (A 55)⟩,
    ⟨(.reg 11 : Operand 32), (W 50)⟩,
    ⟨(.reg 12 : Operand 32), (W 44)⟩,
    ⟨(.reg 13 : Operand 32), (W 55)⟩,
    ⟨(.reg 14 : Operand 32), (W 40)⟩,
    ⟨(.reg 15 : Operand 32), (W 49)⟩,
    ⟨(.mem (stack + 0) : Operand 32), (W 41)⟩,
    ⟨(.mem (stack + 4) : Operand 32), (W 53)⟩,
    ⟨(.mem (stack + 8) : Operand 32), (W 52)⟩,
    ⟨(.mem (stack + 12) : Operand 32), (W 48)⟩,
    ⟨(.mem (stack + 16) : Operand 32), (W 45)⟩,
    ⟨(.mem (stack + 24) : Operand 32), (W 42)⟩,
    ⟨(.mem (stack + 32) : Operand 32), (W 54)⟩,
    ⟨(.mem (stack + 40) : Operand 32), (W 55)⟩,
    ⟨(.mem (stack + 48) : Operand 32), (W 47)⟩,
    ⟨(.mem (stack + 56) : Operand 32), (W 51)⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), (W 46)⟩,
    ⟨(.mem (stack + 80) : Operand 32), (W 43)⟩,
    ⟨(.mem (stack + 88) : Operand 32), (W 50)⟩,
    ⟨(.mem (stack + 96) : Operand 32), (W 49)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

theorem effect058_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (_hf : FrameData stack input M s)
    (he : (effect058 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hfoot : ∀ c ∈ (effect058 s).components, c ∈ [.reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect058
    iterate 11 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [addR32Imm32Effect_components, addR32R32Effect_components, andR32R32Effect_components,
        movR32R32Effect_components, rolR32Effect_components, xorR32R32Effect_components,
        List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and, forall_eq]
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose]
  have ha := he.agrees.mono hfoot
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all (config := {decide := true, implicitDefEqProofs := false}) only [scratchComponents, x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hCov.elim

theorem effect058_rip {s t : RamState}
    (he : (effect058 s).Holds s t) :
    t.RIP = 0x103175 := by
  exact he.rip.trans (by rfl)

section Words058
theorem effect058_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16}
    {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut058 stack input H M))
    (he : (effect058 s).Holds s t) :
    Write.AllHold t (cut059 stack input H M) := by
  have hWork : (workingAfter M H 56).a =
      ((workingAfter M H 55).a).rotateLeft 5 +
        ((((workingAfter M H 53).a).rotateLeft 30 &&&
            ((workingAfter M H 52).a).rotateLeft 30) ^^^
          ((((workingAfter M H 53).a).rotateLeft 30 ^^^
              ((workingAfter M H 52).a).rotateLeft 30) &&&
            (workingAfter M H 54).a)) +
        ((workingAfter M H 51).a).rotateLeft 30 + K ⟨55, by decide⟩ +
        scheduleWord M 55 := by
    rw [workingAfter_step_a_values M H 51 (by decide)]
    rw [sha1_f_majority (t := ⟨55, by decide⟩) (by decide) (by decide)]
    have hMaj (x y z : BitVec 32) :
        Standards.NIST.SHA2.SHA256.Maj x y z =
          (y &&& z) ^^^ ((y ^^^ z) &&& x) := by
      rw [sha1Maj_eq_xor]
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and]
      cases x.getLsbD i <;> cases y.getLsbD i <;> cases z.getLsbD i <;> decide
    rw [hMaj]
    have hK : K ⟨55, by decide⟩ = (0x8f1bbcdc : BitVec 32) := by decide +kernel
    rw [hK]
    ac_rfl
  have hpre : Write.AllHold s
      (genericCut058 stack input H (fun n ↦ (workingAfter M H n).a) (scheduleWord M)) := by
    change Write.AllHold s (cut058 stack input H M)
    exact hw
  have hfull : ∀ wr ∈ (effect058 s).writes, wr.Full := by
    apply Effect.Local.full
    unfold effect058
    repeat' first
      | (solve | x86_local)
      | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  have hfoot : ∀ c ∈ (effect058 s).components,
      c ∈ [.reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9,
        .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect058
    iterate 11 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [addR32Imm32Effect_components, addR32R32Effect_components,
       andR32R32Effect_components, movR32R32Effect_components,
       rolR32Effect_components, xorR32R32Effect_components,
       List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and, forall_eq]
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose]
  have ha := he.agrees.mono hfoot
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  simp only [genericCut058, Write.AllHold] at hpre
  obtain ⟨h0,h2,h5,h6,h8,h9,h11,h12,h13,h14,h15,
    hM0,hM4,hM8,hM12,hM16,hM24,hM32,hM40,hM48,hM56,hM64,hM72,hM80,hM88,hM96,
    hM116,hM120,hM124,hM144,hM152⟩ := hpre
  have hMem : t.external = s.external := ha.external (by
    intro c hc x
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    all_goals simp [Component.Covers])
  have hM0after : (Operand.mem (stack + 0) : Operand 32).read t =
      scheduleWord M 41 := by simpa only [Operand.read, hMem] using hM0
  sha1_norm at hs
  sha1_norm at h0 h2 h5 h6 h8 h9 h11 h12 h13 h14 h15
  sha1_norm at hM0 hM4 hM8 hM12 hM16 hM24 hM32 hM40 hM48 hM56 hM64 hM72 hM80 hM88 hM96
  sha1_norm at hM116 hM120 hM124 hM144 hM152
  change Write.AllHold t
    (genericCut059 stack input H (fun n ↦ (workingAfter M H n).a) (scheduleWord M))
  simp only [genericCut059, Write.AllHold, hM0after, ← ho.read_reg, ← ho.read_mem]
  sha1_norm [effect058, hs, h0,h2,h5,h6,h8,h9,h11,h12,h13,h14,h15,
    hM0,hM4,hM8,hM12,hM16,hM24,hM32,hM40,hM48,hM56,hM64,hM72,hM80,hM88,hM96,
    hM116,hM120,hM124,hM144,hM152,hWork]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
  all_goals ac_rfl
end Words058

theorem segment058 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x103155 0x103175
      cut058 cut059 := by
  have hout : ∀ d : Nat, d ≤ bytes058.length →
      0x103155 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    have hd' : d ≤ 32 := hd
    have hd64 : d < 2 ^ 64 := by omega
    have hsum : 0x103155 + d < 2 ^ 64 := by omega
    have hpc : (0x103155 + BitVec.ofNat 64 d).toNat = 0x103155 + d := by
      change (0x103155 + d % 2 ^ 64) % 2 ^ 64 = 0x103155 + d
      rw [Nat.mod_eq_of_lt hd64, Nat.mod_eq_of_lt hsum]
    exact outsideCompression_ne hOutside (by rw [hpc]; omega) (by rw [hpc]; omega)
  apply Segment.of_block (fun _ _ _ _ => effect058)
    (fun stack input H M => block058 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64
      0x3155) bytes058,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect058_rip he
  · intro stack input H M s t _ hf _ he
    exact effect058_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect058_words hf hw he

end Sha1.Proofs.Compress.Machine

namespace Sha1.Proofs.Compress.Machine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Spec.Program
open Standards.NIST.SHA1 Standards.NIST.SHA2.SHA256 Sha1.Proofs.Compress.Rounds

attribute [local irreducible] workingAfter scheduleWord messageSchedule

def bytes059 : List UInt8 :=
  [0xc1, 0xc0, 0x1e, 0x89, 0xc1, 0x31, 0xf1, 0x44, 0x21, 0xc1, 0x41, 0x89, 0xc1, 0x41, 0x21, 0xf1,
    0x41, 0x31, 0xc9, 0x4c, 0x8b, 0x54, 0x24, 0x18, 0x45, 0x31, 0xd6, 0x8b, 0x5c, 0x24, 0xc, 0x41,
    0x31, 0xde, 0x41, 0x31, 0xee, 0x41, 0xd1, 0xc6, 0x44, 0x1, 0xf2, 0x44, 0x1, 0xca, 0x89, 0xf9,
    0xc1, 0xc1, 0x5, 0x1, 0xd1, 0x81, 0xc1, 0xdc, 0xbc, 0x1b, 0x8f]

set_option maxHeartbeats 800000 in
def effect059 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq ((rolR32Effect 0x103175 3 0 30)) (movR32R32Effect 0x103178 2 1 0))
    (xorR32R32Effect 0x10317a 2 1 6)) (andR32R32Effect 0x10317c 3 1 8)) (movR32R32Effect 0x10317f 3
    9 0)) (andR32R32Effect 0x103182 3 9 6)) (xorR32R32Effect 0x103185 3 9 1)) (movR64M64Effect
    0x103188 10 (.sib 4 none 0 (.d8 0x18)))) (xorR32R32Effect 0x10318d 3 14 10)) (movR32M32LowEffect
    0x103190 3 (.sib 4 none 0 (.d8 0xc)))) (xorR32R32Effect 0x103194 3 14 3)) (xorR32R32Effect
    0x103197 3 14 5)) (rolR32Effect 0x10319a 3 14 1)) (addR32R32Effect 0x10319d 3 2 14))
    (addR32R32Effect 0x1031a0 3 2 9)) (movR32R32Effect 0x1031a3 2 1 7)) (rolR32Effect 0x1031a5 3 1
    5)) (addR32R32Effect 0x1031a8 2 1 2)) (addR32Imm32Effect 0x1031aa 6 1 0x8f1bbcdc)

set_option maxHeartbeats 1600000 in
theorem block059 [Bindings] (boundary : ReturnBoundary)
    (stack input : BitVec 64) (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes059.length → 0x103175 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x103175 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut059 stack input H M))
      (codeRange 0x103175 bytes059) effect059 := by
  unfold bytes059 at hout ⊢
  sha1_run_begin (rol_r32_imm8_effect_step 0x103175 0xc0 0x1e (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_effect_step 0x103178 0xc1 (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x10317a 0xf1 (by decide +kernel))
  sha1_run_then (and_r32_r32_rex_effect_step 0x10317c 0x44 0xc1 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x10317f 0x41 0xc1 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (and_r32_r32_rex_effect_step 0x103182 0x41 0xf1 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x103185 0x41 0xc9 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_m64_effect_step 0x103188 0x4c (by unfold RexWPrefix; decide +kernel) 2 (.sib 4 none 0 (.d8 0x18)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x10318d 0x45 0xd6 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_m32_low_effect_step 0x103190 3 (.sib 4 none 0 (.d8 0xc)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x103194 0x41 0xde (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x103197 0x41 0xee (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_one_rex_effect_step 0x10319a 0x41 0xc6 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x10319d 0x44 0xf2 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x1031a0 0x44 0xca (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_effect_step 0x1031a3 0xf9 (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x1031a5 0xc1 0x5 (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x1031a8 0xd1 (by decide +kernel))
  sha1_run_then (add_r32_imm32_effect_step 0x1031aa 0xc1 0x8f1bbcdc (by decide +kernel) (by decide +kernel))
  sha1_run_finish [effect059]

private def genericCut060 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), ((A 54)).rotateLeft 30⟩,
    ⟨(.reg 1 : Operand 32), (A 57)⟩,
    ⟨(.reg 3 : Operand 32), (W 48)⟩,
    ⟨(.reg 6 : Operand 32), ((A 53)).rotateLeft 30⟩,
    ⟨(.reg 7 : Operand 32), (A 56)⟩,
    ⟨(.reg 8 : Operand 32), (A 55)⟩,
    ⟨(.reg 10 : Operand 32), (W 42)⟩,
    ⟨(.reg 11 : Operand 32), (W 50)⟩,
    ⟨(.reg 12 : Operand 32), (W 44)⟩,
    ⟨(.reg 13 : Operand 32), (W 55)⟩,
    ⟨(.reg 14 : Operand 32), (W 56)⟩,
    ⟨(.reg 15 : Operand 32), (W 49)⟩,
    ⟨(.mem (stack + 0) : Operand 32), (W 41)⟩,
    ⟨(.mem (stack + 4) : Operand 32), (W 53)⟩,
    ⟨(.mem (stack + 8) : Operand 32), (W 52)⟩,
    ⟨(.mem (stack + 12) : Operand 32), (W 48)⟩,
    ⟨(.mem (stack + 16) : Operand 32), (W 45)⟩,
    ⟨(.mem (stack + 32) : Operand 32), (W 54)⟩,
    ⟨(.mem (stack + 40) : Operand 32), (W 55)⟩,
    ⟨(.mem (stack + 48) : Operand 32), (W 47)⟩,
    ⟨(.mem (stack + 56) : Operand 32), (W 51)⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), (W 46)⟩,
    ⟨(.mem (stack + 80) : Operand 32), (W 43)⟩,
    ⟨(.mem (stack + 88) : Operand 32), (W 50)⟩,
    ⟨(.mem (stack + 96) : Operand 32), (W 49)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

theorem effect059_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (_hf : FrameData stack input M s)
    (he : (effect059 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hfoot : ∀ c ∈ (effect059 s).components, c ∈ [.reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect059
    iterate 18 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [addR32Imm32Effect_components, addR32R32Effect_components, andR32R32Effect_components,
        movR32M32LowEffect_components, movR32R32Effect_components, movR64M64Effect_components,
        rolR32Effect_components, xorR32R32Effect_components, List.mem_cons, List.not_mem_nil,
        or_false, or_imp, forall_and, forall_eq]
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose]
  have ha := he.agrees.mono hfoot
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all (config := {decide := true, implicitDefEqProofs := false}) only [scratchComponents, x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hCov.elim

theorem effect059_rip {s t : RamState}
    (he : (effect059 s).Holds s t) :
    t.RIP = 0x1031b0 := by
  exact he.rip.trans (by rfl)

section Words059
theorem effect059_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16}
    {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut059 stack input H M))
    (he : (effect059 s).Holds s t) :
    Write.AllHold t (cut060 stack input H M) := by
  have hK56 : K ⟨56, by decide⟩ = (0x8f1bbcdc : BitVec 32) := by decide +kernel
  have hWork : (workingAfter M H 57).a =
      ((workingAfter M H 56).a).rotateLeft 5 +
        (((workingAfter M H 52).a).rotateLeft 30 +
          (scheduleWord M 56 +
            ((((workingAfter M H 54).a).rotateLeft 30 &&&
                ((workingAfter M H 53).a).rotateLeft 30) ^^^
              ((((workingAfter M H 54).a).rotateLeft 30 ^^^
                  ((workingAfter M H 53).a).rotateLeft 30) &&&
                (workingAfter M H 55).a)))) + K ⟨56, by decide⟩ := by
    rw [workingAfter_step_a_values M H 52 (by decide)]
    rw [sha1_f_majority (t := ⟨56, by decide⟩) (by decide) (by decide)]
    have hMaj (x y z : BitVec 32) :
        Standards.NIST.SHA2.SHA256.Maj x y z =
          (y &&& z) ^^^ ((y ^^^ z) &&& x) := by
      rw [sha1Maj_eq_xor]
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and]
      cases x.getLsbD i <;> cases y.getLsbD i <;> cases z.getLsbD i <;> decide
    rw [hMaj]
    rw [hK56]
    ac_rfl
  have hSchedule : scheduleWord M 56 =
      (scheduleWord M 53 ^^^ scheduleWord M 48 ^^^ scheduleWord M 42 ^^^
        scheduleWord M 40).rotateLeft 1 := by
    change scheduleWord M (⟨56, by decide⟩ : Fin 80) = _
    rw [scheduleWord_recurrence M ⟨56, by decide⟩ (by decide),
      sha1Rotl_eq_rotateLeft 1 _ (by decide)]
    have h53 : (⟨53, by decide⟩ : Fin 80) = 53 := by decide
    have h48 : (⟨48, by decide⟩ : Fin 80) = 48 := by decide
    have h42 : (⟨42, by decide⟩ : Fin 80) = 42 := by decide
    have h40 : (⟨40, by decide⟩ : Fin 80) = 40 := by decide
    simp only [h53,h48,h42,h40]
  have hpre : Write.AllHold s
      (genericCut059 stack input H (fun n ↦ (workingAfter M H n).a) (scheduleWord M)) := by
    change Write.AllHold s (cut059 stack input H M)
    exact hw
  have hfull : ∀ wr ∈ (effect059 s).writes, wr.Full := by
    apply Effect.Local.full
    unfold effect059
    repeat' first
      | (solve | x86_local)
      | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  have hfoot : ∀ c ∈ (effect059 s).components,
      c ∈ [.reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9,
        .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect059
    iterate 18 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [addR32Imm32Effect_components, addR32R32Effect_components,
       andR32R32Effect_components, movR32M32LowEffect_components,
       movR32R32Effect_components, movR64M64Effect_components,
       rolR32Effect_components, xorR32R32Effect_components,
       List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and, forall_eq]
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose]
  have ha := he.agrees.mono hfoot
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  simp only [genericCut059, Write.AllHold] at hpre
  obtain ⟨h0,h2,h5,h6,h7,h8,h11,h12,h13,h14,h15,
    hM0,hM4,hM8,hM12,hM16,hM24,hM32,hM40,hM48,hM56,hM64,hM72,hM80,hM88,hM96,
    hM116,hM120,hM124,hM144,hM152⟩ := hpre
  have hMem : t.external = s.external := ha.external (by
    intro c hc x
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    all_goals simp [Component.Covers])
  have hM0after : (Operand.mem (stack + 0) : Operand 32).read t =
      scheduleWord M 41 := by simpa only [Operand.read, hMem] using hM0
  have hM24low : BitVec.setWidth 32
      (memLoad s.external (stack + BitVec.ofNat 64 24) 64) =
      scheduleWord M 42 := by
    have hload := memLoad_extractLsb'
      s.external (stack + BitVec.ofNat 64 24) 64 32 0
      (by decide) (by decide)
    simp only [BitVec.add_zero] at hload
    change memLoad s.external (stack + BitVec.ofNat 64 24) 32 =
      scheduleWord M 42 at hM24
    rw [hM24] at hload
    change BitVec.extractLsb' 0 32
      (memLoad s.external (stack + BitVec.ofNat 64 24) 64) = _
    simpa only [Nat.mul_zero] using hload.symm
  sha1_norm at hs
  sha1_norm at h0 h2 h5 h6 h7 h8 h11 h12 h13 h14 h15
  sha1_norm at hM0 hM4 hM8 hM12 hM16 hM24 hM32 hM40 hM48 hM56 hM64 hM72 hM80 hM88 hM96
  sha1_norm at hM116 hM120 hM124 hM144 hM152
  simp (config := {decide := true, implicitDefEqProofs := false}) only [Operand.read]
    at h0 h2 h5 h6 h7 h8 h11 h12 h13 h14 h15
  simp (config := {decide := true, implicitDefEqProofs := false}) only [Operand.read]
    at hM0 hM4 hM8 hM12 hM16 hM24 hM32 hM40 hM48 hM56 hM64 hM72 hM80 hM88 hM96
  simp (config := {decide := true, implicitDefEqProofs := false}) only [Operand.read]
    at hM116 hM120 hM124 hM144 hM152
  change Write.AllHold t
    (genericCut060 stack input H (fun n ↦ (workingAfter M H n).a) (scheduleWord M))
  simp only [genericCut060, Write.AllHold, hM0after, ← ho.read_reg, ← ho.read_mem]
  sha1_norm [effect059, hs, h0,h2,h5,h6,h7,h8,h11,h12,h13,h14,h15,
    hM0,hM4,hM8,hM12,hM16,hM24low,hM32,hM40,hM48,hM56,hM64,hM72,hM80,hM88,hM96,
    hM116,hM120,hM124,hM144,hM152,hWork,hSchedule,hK56]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [Operand.read, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
  simp only [h0,h2,h5,h6,h7,h8,h11,h12,h13,h14,h15,
    hM4,hM8,hM12,hM16,hM24low,hM32,hM40,hM48,hM56,hM64,hM72,hM80,hM88,hM96,
    hM116,hM120,hM124,hM144,hM152]
  simp only [true_and]
  generalize hR : (workingAfter M H 56).a.rotateLeft 5 = r at ⊢
  generalize hE : (workingAfter M H 52).a.rotateLeft 30 = e at ⊢
  generalize h40 : scheduleWord M 40 = w40 at ⊢
  generalize h42 : scheduleWord M 42 = w42 at ⊢
  generalize h48 : scheduleWord M 48 = w48 at ⊢
  generalize h53 : scheduleWord M 53 = w53 at ⊢
  generalize hB :
    (((workingAfter M H 54).a).rotateLeft 30 &&&
        ((workingAfter M H 53).a).rotateLeft 30) ^^^
      ((((workingAfter M H 54).a).rotateLeft 30 ^^^
          ((workingAfter M H 53).a).rotateLeft 30) &&&
        (workingAfter M H 55).a) = b at ⊢
  repeat' apply And.intro
  · have hW : (w40 ^^^ w42 ^^^ w48 ^^^ w53).rotateLeft 1 =
        (w53 ^^^ w48 ^^^ w42 ^^^ w40).rotateLeft 1 := by ac_rfl
    rw [hW]
    simp only [BitVec.add_assoc]
  · congr 1
    ac_rfl
  · trivial
end Words059

theorem segment059 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x103175 0x1031b0
      cut059 cut060 := by
  have hout : ∀ d : Nat, d ≤ bytes059.length →
      0x103175 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    have hd' : d ≤ 59 := hd
    have hd64 : d < 2 ^ 64 := by omega
    have hsum : 0x103175 + d < 2 ^ 64 := by omega
    have hpc : (0x103175 + BitVec.ofNat 64 d).toNat = 0x103175 + d := by
      change (0x103175 + d % 2 ^ 64) % 2 ^ 64 = 0x103175 + d
      rw [Nat.mod_eq_of_lt hd64, Nat.mod_eq_of_lt hsum]
    exact outsideCompression_ne hOutside (by rw [hpc]; omega) (by rw [hpc]; omega)
  apply Segment.of_block (fun _ _ _ _ => effect059)
    (fun stack input H M => block059 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64
      0x3175) bytes059,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect059_rip he
  · intro stack input H M s t _ hf _ he
    exact effect059_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect059_words hf hw he

end Sha1.Proofs.Compress.Machine

namespace Sha1.Proofs.Compress.Machine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Spec.Program
open Standards.NIST.SHA1 Standards.NIST.SHA2.SHA256 Sha1.Proofs.Compress.Rounds

attribute [local irreducible] workingAfter scheduleWord messageSchedule

def bytes060 : List UInt8 :=
  [0x44, 0x89, 0xc2, 0x4d, 0x89, 0xd0, 0x45, 0x31, 0xe0, 0x45, 0x31, 0xd8, 0x45, 0x31, 0xe8, 0x41,
    0xd1, 0xc0, 0x4c, 0x89, 0x44, 0x24, 0x18, 0xc1, 0xc2, 0x1e, 0x41, 0x89, 0xd1]

set_option maxHeartbeats 800000 in
def effect060 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    ((movR32R32Effect 0x1031b0 3 2 8)) (movR64R64Effect 0x1031b3 8 10)) (xorR32R32Effect 0x1031b6 3
    8 12)) (xorR32R32Effect 0x1031b9 3 8 11)) (xorR32R32Effect 0x1031bc 3 8 13)) (rolR32Effect
    0x1031bf 3 8 1)) (movM64R64Effect 0x1031c2 8 (.sib 4 none 0 (.d8 0x18)))) (rolR32Effect 0x1031c7
    3 2 30)) (movR32R32Effect 0x1031ca 3 9 2)

set_option maxHeartbeats 1600000 in
theorem block060 [Bindings] (boundary : ReturnBoundary)
    (stack input : BitVec 64) (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes060.length → 0x1031b0 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x1031b0 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut060 stack input H M))
      (codeRange 0x1031b0 bytes060) effect060 := by
  unfold bytes060 at hout ⊢
  sha1_run_begin (mov_r32_r32_rex_effect_step 0x1031b0 0x44 0xc2 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_r64_effect_step 0x1031b3 0x4d 0xd0 (by unfold RexWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x1031b6 0x45 0xe0 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x1031b9 0x45 0xd8 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x1031bc 0x45 0xe8 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_one_rex_effect_step 0x1031bf 0x41 0xc0 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step 0x1031c2 0x4c (by unfold RexWPrefix; decide +kernel) 0 (.sib 4 none 0 (.d8 0x18)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x1031c7 0xc2 0x1e (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x1031ca 0x41 0xd1 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_finish [effect060]

private def genericCut061 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), ((A 54)).rotateLeft 30⟩,
    ⟨(.reg 1 : Operand 32), (A 57)⟩,
    ⟨(.reg 2 : Operand 32), ((A 55)).rotateLeft 30⟩,
    ⟨(.reg 3 : Operand 32), (W 48)⟩,
    ⟨(.reg 6 : Operand 32), ((A 53)).rotateLeft 30⟩,
    ⟨(.reg 7 : Operand 32), (A 56)⟩,
    ⟨(.reg 8 : Operand 32), (W 58)⟩,
    ⟨(.reg 9 : Operand 32), ((A 55)).rotateLeft 30⟩,
    ⟨(.reg 12 : Operand 32), (W 44)⟩,
    ⟨(.reg 14 : Operand 32), (W 56)⟩,
    ⟨(.reg 15 : Operand 32), (W 49)⟩,
    ⟨(.mem (stack + 0) : Operand 32), (W 41)⟩,
    ⟨(.mem (stack + 4) : Operand 32), (W 53)⟩,
    ⟨(.mem (stack + 8) : Operand 32), (W 52)⟩,
    ⟨(.mem (stack + 12) : Operand 32), (W 48)⟩,
    ⟨(.mem (stack + 16) : Operand 32), (W 45)⟩,
    ⟨(.mem (stack + 24) : Operand 32), (W 58)⟩,
    ⟨(.mem (stack + 32) : Operand 32), (W 54)⟩,
    ⟨(.mem (stack + 40) : Operand 32), (W 55)⟩,
    ⟨(.mem (stack + 48) : Operand 32), (W 47)⟩,
    ⟨(.mem (stack + 56) : Operand 32), (W 51)⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), (W 46)⟩,
    ⟨(.mem (stack + 80) : Operand 32), (W 43)⟩,
    ⟨(.mem (stack + 88) : Operand 32), (W 50)⟩,
    ⟨(.mem (stack + 96) : Operand 32), (W 49)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

theorem effect060_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (he : (effect060 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hfoot : ∀ c ∈ (effect060 s).components, c ∈ [.mem ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 24) 8, .reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect060
    iterate 8 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [movM64R64Effect_components, movR32R32Effect_components, movR64R64Effect_components,
        rolR32Effect_components, xorR32R32Effect_components, List.mem_cons, List.not_mem_nil,
        or_false, or_imp, forall_and, forall_eq, or_true]
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose]
  have ha := he.agrees.mono hfoot
  rw [hs] at ha
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all (config := {decide := true, implicitDefEqProofs := false}) only [Component.isMem, scratchComponents, x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hCov.elim
      | exact scratchComponents_stack (Or.inl (by decide +kernel)) hCov

theorem effect060_rip {s t : RamState}
    (he : (effect060 s).Holds s t) :
    t.RIP = 0x1031cd := by
  exact he.rip.trans (by rfl)

section Words060

private theorem full060 (s : RamState) : ∀ w ∈ (effect060 s).writes, w.Full := by
  apply Effect.Local.full
  unfold effect060
  repeat' first | (solve | x86_local) | apply Effect.Local.seq

set_option maxRecDepth 4096 in
private theorem rawR2_060 {s t : RamState} (v8 : BitVec 32)
    (h8 : (Operand.reg 8 : Operand 32).read s = v8)
    (he : (effect060 s).Holds s t) :
    (Operand.reg 2 : Operand 32).read t = v8.rotateLeft 30 := by
  have ho := he.obsAfter (full060 s) true
  sha1_norm at h8
  simp only [← ho.read_reg]
  sha1_norm [effect060, h8, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]

set_option maxRecDepth 4096 in
private theorem rawR9_060 {s t : RamState} (v8 : BitVec 32)
    (h8 : (Operand.reg 8 : Operand 32).read s = v8)
    (he : (effect060 s).Holds s t) :
    (Operand.reg 9 : Operand 32).read t = v8.rotateLeft 30 := by
  have ho := he.obsAfter (full060 s) true
  sha1_norm at h8
  simp only [← ho.read_reg]
  sha1_norm [effect060, h8, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]

set_option maxRecDepth 4096 in
private theorem rawR8_060 {s t : RamState} (v10 v11 v12 v13 : BitVec 32)
    (h10 : (Operand.reg 10 : Operand 32).read s = v10)
    (h11 : (Operand.reg 11 : Operand 32).read s = v11)
    (h12 : (Operand.reg 12 : Operand 32).read s = v12)
    (h13 : (Operand.reg 13 : Operand 32).read s = v13)
    (he : (effect060 s).Holds s t) :
    (Operand.reg 8 : Operand 32).read t = (v10 ^^^ v12 ^^^ v11 ^^^ v13).rotateLeft 1 := by
  have ho := he.obsAfter (full060 s) true
  sha1_norm at h10 h11 h12 h13
  simp only [← ho.read_reg]
  sha1_norm [effect060, h10,h11,h12,h13,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]

set_option maxRecDepth 4096 in
private theorem rawM24_060 {s t : RamState} (stack : BitVec 64)
    (v10 v11 v12 v13 : BitVec 32)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (h10 : (Operand.reg 10 : Operand 32).read s = v10)
    (h11 : (Operand.reg 11 : Operand 32).read s = v11)
    (h12 : (Operand.reg 12 : Operand 32).read s = v12)
    (h13 : (Operand.reg 13 : Operand 32).read s = v13)
    (he : (effect060 s).Holds s t) :
    (Operand.mem (stack + 24) : Operand 32).read t =
      (v10 ^^^ v12 ^^^ v11 ^^^ v13).rotateLeft 1 := by
  have ho := he.obsAfter (full060 s) true
  sha1_norm at hs h10 h11 h12 h13
  simp only [← ho.read_mem]
  sha1_norm [effect060, hs]
  rw [read32_memStore64_low]
  sha1_norm [effect060, h10,h11,h12,h13,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    BitVec.extractLsb'_setWidth_of_le, BitVec.extractLsb'_eq_self]

set_option maxRecDepth 4096 in
private theorem genericWords060 {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) {s t : RamState}
    (hW58 : W 58 = (W 55 ^^^ W 50 ^^^ W 44 ^^^ W 42).rotateLeft 1)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hw : Write.AllHold s (genericCut060 stack input H A W))
    (he : (effect060 s).Holds s t) :
    Write.AllHold t (genericCut061 stack input H A W) := by
  simp only [genericCut060, Write.AllHold] at hw
  obtain ⟨h0,h1,h3,h6,h7,h8,h10,h11,h12,h13,h14,h15,hM0,hM4,hM8,hM12,hM16,hM32,hM40,hM48,hM56,hM64,hM72,hM80,hM88,hM96,hM116,hM120,hM124,hM144,hM152⟩ := hw
  have hW : (W 42 ^^^ W 44 ^^^ W 50 ^^^ W 55).rotateLeft 1 = W 58 := by
    rw [hW58]
    congr 1
    ac_rfl
  have hR2 := rawR2_060 (A 55) h8 he
  have hR9 := rawR9_060 (A 55) h8 he
  have hR8 := (rawR8_060 (W 42) (W 50) (W 44) (W 55) h10 h11 h12 h13 he).trans hW
  have hM24 := (rawM24_060 stack (W 42) (W 50) (W 44) (W 55)
    hs h10 h11 h12 h13 he).trans hW
  have hfoot : ∀ c ∈ (effect060 s).components,
      c ∈ [.mem ((Operand.reg 4 : Operand 64).read s + 24) 8,
        .reg 2, .reg 8, .reg 9, .flags, .rip] := by
    unfold effect060
    iterate 8 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [movM64R64Effect_components, movR32R32Effect_components,
        movR64R64Effect_components, rolR32Effect_components, xorR32R32Effect_components,
        List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and, forall_eq, or_true]
    all_goals sha1_norm
  have ha := he.agrees.mono hfoot
  rw [hs] at ha
  have hmem {n : Nat} (off : BitVec 64) (hb : OffsetsApart 24 8 off (n / 8))
      (hsize : 8 + n / 8 < 2 ^ 64) :
      (Operand.mem (stack + off) : Operand n).read t =
      (Operand.mem (stack + off) : Operand n).read s := by
    apply memLoad_congr
    intro i hi
    apply congrArg (fun b : Option UInt8 ↦ b.getD 0)
    apply ha.byte
    intro c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨j,hj,heq⟩ := hCov
      exact hb.ne stack hj hi hsize heq.symm
    all_goals exact hCov.elim
  simp only [genericCut061, Write.AllHold]
  refine ⟨?f0, ?f1, ?f2, ?f3, ?f4, ?f5, ?f6, ?f7, ?f8, ?f9, ?f10, ?f11, ?f12, ?f13, ?f14, ?f15, ?f16, ?f17, ?f18, ?f19, ?f20, ?f21, ?f22, ?f23, ?f24, ?f25, ?f26, ?f27, ?f28, ?f29, ?f30⟩
  case f0 => exact (ha.read (by simp)).trans h0
  case f1 => exact (ha.read (by simp)).trans h1
  case f2 => exact hR2
  case f3 => exact (ha.read (by simp)).trans h3
  case f4 => exact (ha.read (by simp)).trans h6
  case f5 => exact (ha.read (by simp)).trans h7
  case f6 => exact hR8
  case f7 => exact hR9
  case f8 => exact (ha.read (by simp)).trans h12
  case f9 => exact (ha.read (by simp)).trans h14
  case f10 => exact (ha.read (by simp)).trans h15
  case f11 => exact (hmem 0 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM0
  case f12 => exact (hmem 4 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM4
  case f13 => exact (hmem 8 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM8
  case f14 => exact (hmem 12 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM12
  case f15 => exact (hmem 16 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM16
  case f16 => exact hM24
  case f17 => exact (hmem 32 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM32
  case f18 => exact (hmem 40 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM40
  case f19 => exact (hmem 48 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM48
  case f20 => exact (hmem 56 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM56
  case f21 => exact (hmem 64 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM64
  case f22 => exact (hmem 72 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM72
  case f23 => exact (hmem 80 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM80
  case f24 => exact (hmem 88 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM88
  case f25 => exact (hmem 96 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM96
  case f26 => exact (hmem 116 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM116
  case f27 => exact (hmem 120 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM120
  case f28 => exact (hmem 124 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM124
  case f29 => exact (hmem 144 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM144
  case f30 => exact (hmem 152 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM152

theorem effect060_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16}
    {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut060 stack input H M))
    (he : (effect060 s).Holds s t) :
    Write.AllHold t (cut061 stack input H M) := by
  have hW58 : scheduleWord M 58 =
      (scheduleWord M 55 ^^^ scheduleWord M 50 ^^^ scheduleWord M 44 ^^^
        scheduleWord M 42).rotateLeft 1 := by
    change scheduleWord M (⟨58, by decide⟩ : Fin 80) = _
    rw [scheduleWord_recurrence M ⟨58, by decide⟩ (by decide),
      sha1Rotl_eq_rotateLeft 1 _ (by decide)]
    simp only [Nat.reduceSub]
    rfl
  exact genericWords060 (fun n ↦ (workingAfter M H n).a) (scheduleWord M)
    hW58 hf.stackPointer hw he
end Words060

theorem segment060 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x1031b0 0x1031cd
      cut060 cut061 := by
  have hout : ∀ d : Nat, d ≤ bytes060.length →
      0x1031b0 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    have hd' : d ≤ 29 := hd
    have hd64 : d < 2 ^ 64 := by omega
    have hsum : 0x1031b0 + d < 2 ^ 64 := by omega
    have hpc : (0x1031b0 + BitVec.ofNat 64 d).toNat = 0x1031b0 + d := by
      change (0x1031b0 + d % 2 ^ 64) % 2 ^ 64 = 0x1031b0 + d
      rw [Nat.mod_eq_of_lt hd64, Nat.mod_eq_of_lt hsum]
    exact outsideCompression_ne hOutside (by rw [hpc]; omega) (by rw [hpc]; omega)
  apply Segment.of_block (fun _ _ _ _ => effect060)
    (fun stack input H M => block060 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64
      0x31b0) bytes060,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect060_rip he
  · intro stack input H M s t _ hf _ he
    exact effect060_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect060_words hf hw he

end Sha1.Proofs.Compress.Machine

namespace Sha1.Proofs.Compress.Machine

open X86.Machine X86.UserProcess

theorem segments051_060 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x102fc0 0x1031cd cut051 cut061 := by
  have h0 := segment051 boundary hOutside
  have h1 := h0.seq (segment052 boundary hOutside)
  have h2 := h1.seq (segment053 boundary hOutside)
  have h3 := h2.seq (segment054 boundary hOutside)
  have h4 := h3.seq (segment055 boundary hOutside)
  have h5 := h4.seq (segment056 boundary hOutside)
  have h6 := h5.seq (segment057 boundary hOutside)
  have h7 := h6.seq (segment058 boundary hOutside)
  have h8 := h7.seq (segment059 boundary hOutside)
  have h9 := h8.seq (segment060 boundary hOutside)
  exact h9

end Sha1.Proofs.Compress.Machine
