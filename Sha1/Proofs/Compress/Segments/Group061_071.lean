import Sha1.Proofs.Compress.Machine.Run
import Sha1.Proofs.Compress.Rounds.Scalar
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Mov.Generated.RM.Triple
import Sha1.Proofs.Common.Instructions.MovStore.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RM.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import X86Proofs.Instructions.Add.Generated.AccImm32.Triple
import X86Proofs.Instructions.Bswap.Generated.R.Triple
import X86Proofs.Instructions.Lea.Generated.RM.Triple

import X86Proofs.Instructions.Or.Generated.RR.Triple

namespace Sha1.Proofs.Compress.Machine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Spec.Program
open Standards.NIST.SHA1 Sha1.Proofs.Compress.Rounds

attribute [local irreducible] workingAfter scheduleWord messageSchedule

namespace Block061

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Spec.Program
open Standards.NIST.SHA1 Sha1.Proofs.Compress.Rounds


def bytes061 : List UInt8 :=
  [0x41, 0x31, 0xc1, 0x41, 0x21, 0xf9, 0x41, 0x1, 0xc0, 0x21, 0xd0, 0x44, 0x31, 0xc8, 0x44, 0x8b, 0xc, 0x24, 0x4c, 0x8b, 0x6c, 0x24, 0x50, 0x45, 0x31, 0xe9, 0x45, 0x31, 0xf9, 0x4c, 0x8b, 0x5c, 0x24, 0x20, 0x45, 0x31, 0xd9, 0x41, 0xd1, 0xc1, 0x44, 0x1, 0xce, 0x45, 0x89, 0xca, 0x44, 0x89, 0xc, 0x24, 0x1, 0xc6, 0x89, 0xc8, 0xc1, 0xc0, 0x5, 0x1, 0xf0, 0x5, 0xdc, 0xbc, 0x1b, 0x8f]

set_option maxHeartbeats 800000 in
def effect061 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq ((xorR32R32Effect 0x1031cd 3 9 0)) (andR32R32Effect 0x1031d0 3 9 7)) (addR32R32Effect 0x1031d3 3 8 0)) (andR32R32Effect 0x1031d6 2 0 2)) (xorR32R32Effect 0x1031d8 3 0 9)) (movR32M32Effect 0x1031db 9 (.sib 4 none 0 .none))) (movR64M64Effect 0x1031df 13 (.sib 4 none 0 (.d8 0x50)))) (xorR32R32Effect 0x1031e4 3 9 13)) (xorR32R32Effect 0x1031e7 3 9 15)) (movR64M64Effect 0x1031ea 11 (.sib 4 none 0 (.d8 0x20)))) (xorR32R32Effect 0x1031ef 3 9 11)) (rolR32Effect 0x1031f2 3 9 1)) (addR32R32Effect 0x1031f5 3 6 9)) (movR32R32Effect 0x1031f8 3 10 9)) (movM32R32Effect 0x1031fb 9 (.sib 4 none 0 .none))) (addR32R32Effect 0x1031ff 2 6 0)) (movR32R32Effect 0x103201 2 0 1)) (rolR32Effect 0x103203 3 0 5)) (addR32R32Effect 0x103206 2 0 6)) (addEaxImm32Effect 0x103208 0x8f1bbcdc)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
theorem block061 [Bindings] (boundary : ReturnBoundary)
    (stack input : BitVec 64) (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes061.length → 0x1031cd + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x1031cd ∧ FrameData stack input M s ∧
        Write.AllHold s (cut061 stack input H M))
      (codeRange 0x1031cd bytes061) effect061 := by
  unfold bytes061 at hout ⊢
  sha1_run_begin (xor_r32_r32_rex_effect_step 0x1031cd 0x41 0xc1 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (and_r32_r32_rex_effect_step 0x1031d0 0x41 0xf9 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x1031d3 0x41 0xc0 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (and_r32_r32_effect_step 0x1031d6 0xd0 (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x1031d8 0x44 0xc8 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_m32_effect_step 0x1031db 0x44 (by unfold RexNoWPrefix; decide +kernel) 1 (.sib 4 none 0 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_m64_effect_step 0x1031df 0x4c (by unfold RexWPrefix; decide +kernel) 5 (.sib 4 none 0 (.d8 0x50)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x1031e4 0x45 0xe9 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x1031e7 0x45 0xf9 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_m64_effect_step 0x1031ea 0x4c (by unfold RexWPrefix; decide +kernel) 3 (.sib 4 none 0 (.d8 0x20)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x1031ef 0x45 0xd9 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_one_rex_effect_step 0x1031f2 0x41 0xc1 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x1031f5 0x44 0xce (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x1031f8 0x45 0xca (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m32_r32_effect_step 0x1031fb 0x44 (by unfold RexNoWPrefix; decide +kernel) 1 (.sib 4 none 0 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x1031ff 0xc6 (by decide +kernel))
  sha1_run_then (mov_r32_r32_effect_step 0x103201 0xc8 (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x103203 0xc0 0x5 (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x103206 0xf0 (by decide +kernel))
  sha1_run_then (add_eax_imm32_effect_step 0x103208 0x8f1bbcdc)
  sha1_run_finish [effect061]

set_option maxRecDepth 10000 in
private theorem components061 (s : RamState) :
    ∀ c ∈ (effect061 s).components, c ∈ [.mem ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 0) 4, .reg 0, .reg 6, .reg 8, .reg 9, .reg 10, .reg 11, .reg 13, .flags, .rip] := by
  unfold effect061
  iterate 19 apply components_seq_of
  all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
    [addEaxImm32Effect_components, addR32R32Effect_components, andR32R32Effect_components, movM32R32Effect_components, movR32M32Effect_components, movR32R32Effect_components, movR64M64Effect_components, rolR32Effect_components, xorR32R32Effect_components, List.mem_cons, List.not_mem_nil,
      or_false, or_imp, forall_and, forall_eq, or_true]
  all_goals sha1_norm

set_option maxRecDepth 10000 in
theorem effect061_agrees {stack input : BitVec 64} {M : Vector (BitVec 32) 16}
    {s t : RamState} (hf : FrameData stack input M s) (he : (effect061 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have ha := he.agrees.mono (components061 s)
  rw [hs] at ha
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all (config := {decide := true, implicitDefEqProofs := false}) only
      [Component.isMem, scratchComponents, x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hCov.elim
      | exact scratchComponents_stack (Or.inl (by decide +kernel)) hCov

set_option maxRecDepth 10000 in
private theorem full061 (s : RamState) : ∀ w ∈ (effect061 s).writes, w.Full := by
  apply Effect.Local.full
  unfold effect061
  repeat' first | (solve | x86_local) | apply Effect.Local.seq

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
theorem effect061_words {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (hw : Write.AllHold s (cut061 stack input H M))
    (he : (effect061 s).Holds s t) : Write.AllHold t (cut062 stack input H M) := by
  have ho := he.obsAfter (full061 s) true
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have ha := he.agrees.mono (components061 s)
  rw [hs] at ha
  simp only [cut061, Write.AllHold] at hw
  obtain ⟨h0, h1, h2, h3, h6, h7, h8, h9, h12, h14, h15, hM0, hM4, hM8, hM12, hM16, hM24, hM32, hM40, hM48, hM56, hM64, hM72, hM80, hM88, hM96, hM116, hM120, hM124, hM144, hM152⟩ := hw
  have hM80wide : ((Operand.mem (stack + 80) : Operand 64).read s).setWidth 32 =
      scheduleWord M 43 :=
    (read32_of_read64_low (s := s) (a := stack + 80)
      (v := (Operand.mem (stack + 80) : Operand 64).read s) rfl).symm.trans hM80
  have hM32wide : ((Operand.mem (stack + 32) : Operand 64).read s).setWidth 32 =
      scheduleWord M 54 :=
    (read32_of_read64_low (s := s) (a := stack + 32)
      (v := (Operand.mem (stack + 32) : Operand 64).read s) rfl).symm.trans hM32
  have hmem {width : Nat} (off : BitVec 64)
      (hb : OffsetsApart 0 4 off (width / 8)) (hz : 4 + width / 8 < 2 ^ 64) :
      (Operand.mem (stack + off) : Operand width).read t =
      (Operand.mem (stack + off) : Operand width).read s := by
    apply memLoad_congr
    intro i hi
    apply congrArg (fun b : Option UInt8 ↦ b.getD 0)
    apply ha.byte
    intro c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨j, hj, heq⟩ := hCov
      exact hb.ne stack hj hi hz heq.symm
    all_goals exact hCov.elim
  have hMaj (x y z : BitVec 32) :
      Standards.NIST.SHA2.SHA256.Maj x y z =
        (z &&& y) ^^^ ((y ^^^ z) &&& x) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [Standards.NIST.SHA2.SHA256.Maj, BitVec.getLsbD_xor, BitVec.getLsbD_and]
    cases x.getLsbD i <;> cases y.getLsbD i <;> cases z.getLsbD i <;> decide
  have hA58 := workingAfter_step_a_values M H 53 (by decide +kernel)
  simp (config := {decide := true}) only [Nat.reduceAdd, f, K, ite_false, ite_true, hMaj] at hA58
  have hT57 : (⟨57, by decide +kernel⟩ : Fin 80) = 57 := by decide +kernel
  simp only [hT57] at hA58
  sha1_norm at hA58
  have hW57 : scheduleWord M 57 =
      (scheduleWord M 54 ^^^ scheduleWord M 49 ^^^
        scheduleWord M 43 ^^^ scheduleWord M 41).rotateLeft 1 := by
    change scheduleWord M (⟨57, by decide +kernel⟩ : Fin 80) = _
    rw [scheduleWord_recurrence M ⟨57, by decide +kernel⟩ (by decide +kernel),
      sha1Rotl_eq_rotateLeft 1 _ (by decide +kernel)]
    simp only [Nat.reduceSub]
    all_goals rfl
  simp only [cut062, Write.AllHold]
  refine ⟨?f0, ?f1, ?f2, ?f3, ?f4, ?f5, ?f6, ?f7, ?f8, ?f9, ?f10, ?f11, ?f12, ?f13, ?f14, ?f15, ?f16, ?f17, ?f18, ?f19, ?f20, ?f21, ?f22, ?f23, ?f24, ?f25, ?f26, ?f27, ?f28, ?f29⟩
  case f0 =>
    sha1_norm at hM80wide hM32wide hs h0 h1 h2 h3 h6 h7 h8 h9 h12 h14 h15 hM0 hM4 hM8 hM12 hM16 hM24 hM32 hM40 hM48 hM56 hM64 hM72 hM80 hM88 hM96 hM116 hM120 hM124 hM144 hM152
    simp only [← ho.read_reg]
    sha1_norm [effect061, hM32wide, hM80wide, hs, h0, h1, h2, h3, h6, h7, h8, h9, h12, h14, h15, hM0, hM4, hM8, hM12, hM16, hM24, hM32, hM40, hM48, hM56, hM64, hM72, hM80, hM88, hM96, hM116, hM120, hM124, hM144, hM152, leaSpec,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, read32_memStore64_low,
      extractLsb'_zero_eq_setWidth, memLoad_memStore]
    all_goals simp only [hA58, hW57]
    all_goals ac_rfl
  case f1 =>
    exact (ha.read (by simp)).trans h1
  case f2 =>
    exact (ha.read (by simp)).trans h2
  case f3 =>
    exact (ha.read (by simp)).trans h3
  case f4 =>
    exact (ha.read (by simp)).trans h7
  case f5 =>
    sha1_norm at hM80wide hM32wide hs h0 h1 h2 h3 h6 h7 h8 h9 h12 h14 h15 hM0 hM4 hM8 hM12 hM16 hM24 hM32 hM40 hM48 hM56 hM64 hM72 hM80 hM88 hM96 hM116 hM120 hM124 hM144 hM152
    simp only [← ho.read_reg]
    sha1_norm [effect061, hM32wide, hM80wide, hs, h0, h1, h2, h3, h6, h7, h8, h9, h12, h14, h15, hM0, hM4, hM8, hM12, hM16, hM24, hM32, hM40, hM48, hM56, hM64, hM72, hM80, hM88, hM96, hM116, hM120, hM124, hM144, hM152, leaSpec,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, read32_memStore64_low,
      extractLsb'_zero_eq_setWidth, memLoad_memStore]
    all_goals ac_rfl
  case f6 =>
    sha1_norm at hM80wide hM32wide hs h0 h1 h2 h3 h6 h7 h8 h9 h12 h14 h15 hM0 hM4 hM8 hM12 hM16 hM24 hM32 hM40 hM48 hM56 hM64 hM72 hM80 hM88 hM96 hM116 hM120 hM124 hM144 hM152
    simp only [← ho.read_reg]
    sha1_norm [effect061, hM32wide, hM80wide, hs, h0, h1, h2, h3, h6, h7, h8, h9, h12, h14, h15, hM0, hM4, hM8, hM12, hM16, hM24, hM32, hM40, hM48, hM56, hM64, hM72, hM80, hM88, hM96, hM116, hM120, hM124, hM144, hM152, leaSpec,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, read32_memStore64_low,
      extractLsb'_zero_eq_setWidth, memLoad_memStore]
    all_goals simp only [hW57]
    all_goals ac_rfl
  case f7 =>
    sha1_norm at hM80wide hM32wide hs h0 h1 h2 h3 h6 h7 h8 h9 h12 h14 h15 hM0 hM4 hM8 hM12 hM16 hM24 hM32 hM40 hM48 hM56 hM64 hM72 hM80 hM88 hM96 hM116 hM120 hM124 hM144 hM152
    simp only [← ho.read_reg]
    sha1_norm [effect061, hM32wide, hM80wide, hs, h0, h1, h2, h3, h6, h7, h8, h9, h12, h14, h15, hM0, hM4, hM8, hM12, hM16, hM24, hM32, hM40, hM48, hM56, hM64, hM72, hM80, hM88, hM96, hM116, hM120, hM124, hM144, hM152, leaSpec,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, read32_memStore64_low,
      extractLsb'_zero_eq_setWidth, memLoad_memStore]
    all_goals ac_rfl
  case f8 =>
    exact (ha.read (by simp)).trans h12
  case f9 =>
    sha1_norm at hM80wide hM32wide hs h0 h1 h2 h3 h6 h7 h8 h9 h12 h14 h15 hM0 hM4 hM8 hM12 hM16 hM24 hM32 hM40 hM48 hM56 hM64 hM72 hM80 hM88 hM96 hM116 hM120 hM124 hM144 hM152
    simp only [← ho.read_reg]
    sha1_norm [effect061, hM32wide, hM80wide, hs, h0, h1, h2, h3, h6, h7, h8, h9, h12, h14, h15, hM0, hM4, hM8, hM12, hM16, hM24, hM32, hM40, hM48, hM56, hM64, hM72, hM80, hM88, hM96, hM116, hM120, hM124, hM144, hM152, leaSpec,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, read32_memStore64_low,
      extractLsb'_zero_eq_setWidth, memLoad_memStore]
    all_goals ac_rfl
  case f10 =>
    exact (ha.read (by simp)).trans h14
  case f11 =>
    sha1_norm at hM80wide hM32wide hs h0 h1 h2 h3 h6 h7 h8 h9 h12 h14 h15 hM0 hM4 hM8 hM12 hM16 hM24 hM32 hM40 hM48 hM56 hM64 hM72 hM80 hM88 hM96 hM116 hM120 hM124 hM144 hM152
    simp only [← ho.read_mem]
    sha1_norm [effect061, hM32wide, hM80wide, hs, h0, h1, h2, h3, h6, h7, h8, h9, h12, h14, h15, hM0, hM4, hM8, hM12, hM16, hM24, hM32, hM40, hM48, hM56, hM64, hM72, hM80, hM88, hM96, hM116, hM120, hM124, hM144, hM152, leaSpec,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, read32_memStore64_low,
      extractLsb'_zero_eq_setWidth, memLoad_memStore]
    all_goals simp only [hW57]
    all_goals ac_rfl
  case f12 =>
    exact (hmem 4 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM4
  case f13 =>
    exact (hmem 8 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM8
  case f14 =>
    exact (hmem 12 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM12
  case f15 =>
    exact (hmem 16 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM16
  case f16 =>
    exact (hmem 24 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM24
  case f17 =>
    exact (hmem 32 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM32
  case f18 =>
    exact (hmem 40 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM40
  case f19 =>
    exact (hmem 48 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM48
  case f20 =>
    exact (hmem 56 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM56
  case f21 =>
    exact (hmem 64 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM64
  case f22 =>
    exact (hmem 72 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM72
  case f23 =>
    exact (hmem 88 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM88
  case f24 =>
    exact (hmem 96 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM96
  case f25 =>
    exact (hmem 116 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM116
  case f26 =>
    exact (hmem 120 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM120
  case f27 =>
    exact (hmem 124 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM124
  case f28 =>
    exact (hmem 144 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM144
  case f29 =>
    exact (hmem 152 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM152

end Block061

open Block061 in
set_option maxRecDepth 10000 in
theorem segment061 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x1031cd 0x10320d cut061 cut062 := by
  have hout : ∀ d : Nat, d ≤ bytes061.length →
      0x1031cd + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      simp only [bytes061, List.length_cons, List.length_nil] at hd <;>
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  apply Segment.of_block (fun _ _ _ _ ↦ effect061)
    (fun stack input H M ↦ block061 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64
      0x31cd) bytes061, x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact he.rip.trans (by rfl)
  · intro stack input H M s t _ hf _ he
    exact effect061_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect061_words hf hw he

namespace Block062

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Spec.Program
open Standards.NIST.SHA1
open Sha1.Proofs.Compress.Rounds



def bytes062 : List UInt8 :=
  [0x44, 0x33, 0x6c, 0x24, 0x10, 0x44, 0x33, 0x6c, 0x24, 0x38, 0x45, 0x31, 0xf5, 0x41, 0xd1, 0xc5, 0xc1, 0xc7, 0x1e, 0x89, 0xfe, 0x31, 0xd6, 0x21, 0xce, 0x46, 0x8d, 0x0c, 0x2a, 0x4c, 0x89, 0x6c, 0x24, 0x50, 0x21, 0xfa, 0x31, 0xf2, 0x44, 0x01, 0xc2, 0x89, 0xc6, 0xc1, 0xc6, 0x05, 0xc1, 0xc1, 0x1e, 0x01, 0xf2, 0x81, 0xc2, 0xdc, 0xbc, 0x1b, 0x8f]

def effect062 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (xorR32M32Effect 0x10320d 13 (.sib 4 none 0 (.d8 0x10))) (xorR32M32Effect 0x103212 13 (.sib 4 none 0 (.d8 0x38)))) (xorR32R32Effect 0x103217 3 13 14)) (rolR32Effect 0x10321a 3 13 1)) (rolR32Effect 0x10321d 3 7 30)) (movR32R32Effect 0x103220 2 6 7)) (xorR32R32Effect 0x103222 2 6 2)) (andR32R32Effect 0x103224 2 6 1)) (leaR32Effect 0x103226 4 9 (.sib 2 (some 13) 0 .none))) (movM64R64Effect 0x10322a 13 (.sib 4 none 0 (.d8 0x50)))) (andR32R32Effect 0x10322f 2 2 7)) (xorR32R32Effect 0x103231 2 2 6)) (addR32R32Effect 0x103233 3 2 8)) (movR32R32Effect 0x103236 2 6 0)) (rolR32Effect 0x103238 3 6 5)) (rolR32Effect 0x10323b 3 1 30)) (addR32R32Effect 0x10323e 2 2 6)) (addR32Imm32Effect 0x103240 6 2 0x8f1bbcdc)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
theorem block062 [Bindings] (boundary : ReturnBoundary) (stack input : BitVec 64)
    (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes062.length →
      0x10320d + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x10320d ∧ FrameData stack input M s ∧
        Write.AllHold s (cut062 stack input H M))
      (codeRange 0x10320d bytes062) effect062 := by
  unfold bytes062 at hout ⊢
  have hRaw : AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x10320d ∧ FrameData stack input M s)
      (codeRange 0x10320d bytes062) effect062 := by
    unfold bytes062 at ⊢

    sha1_run_begin (xor_r32_m32_effect_step 0x10320d 0x44 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) 13 (.sib 4 none 0 (.d8 0x10)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))

    sha1_run_then (xor_r32_m32_effect_step 0x103212 0x44 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) 13 (.sib 4 none 0 (.d8 0x38)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))

    sha1_run_then (xor_r32_r32_rex_effect_step 0x103217 0x45 0xf5 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))

    sha1_run_then (rol_r32_one_rex_effect_step 0x10321a 0x41 0xc5 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))

    sha1_run_then (rol_r32_imm8_effect_step 0x10321d 0xc7 0x1e (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))

    sha1_run_then (mov_r32_r32_effect_step 0x103220 0xfe (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))

    sha1_run_then (xor_r32_r32_effect_step 0x103222 0xd6 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))

    sha1_run_then (and_r32_r32_effect_step 0x103224 0xce (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))

    sha1_run_then (lea_r32_rex_effect_step 0x103226 0x46 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) 9 (.sib 2 (some 13) 0 .none) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))

    sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step 0x10322a 0x4c (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) 13 (.sib 4 none 0 (.d8 0x50)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))

    sha1_run_then (and_r32_r32_effect_step 0x10322f 0xfa (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))

    sha1_run_then (xor_r32_r32_effect_step 0x103231 0xf2 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))

    sha1_run_then (add_r32_r32_rex_effect_step 0x103233 0x44 0xc2 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))

    sha1_run_then (mov_r32_r32_effect_step 0x103236 0xc6 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))

    sha1_run_then (rol_r32_imm8_effect_step 0x103238 0xc6 0x5 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))

    sha1_run_then (rol_r32_imm8_effect_step 0x10323b 0xc1 0x1e (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))

    sha1_run_then (add_r32_r32_effect_step 0x10323e 0xf2 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))

    sha1_run_then (add_r32_imm32_effect_step 0x103240 0xc2 0x8f1bbcdc (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))

    sha1_run_finish [effect062]
  intro s hr hc hp
  exact hRaw s hr hc ⟨hp.1, hp.2.1⟩

private def genericCut062 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), (A 58)⟩,
    ⟨(.reg 1 : Operand 32), (A 57)⟩,
    ⟨(.reg 2 : Operand 32), ((A 55)).rotateLeft 30⟩,
    ⟨(.reg 3 : Operand 32), (W 48)⟩,
    ⟨(.reg 7 : Operand 32), (A 56)⟩,
    ⟨(.reg 8 : Operand 32), ((W 58) + ((A 54)).rotateLeft 30)⟩,
    ⟨(.reg 10 : Operand 32), (W 57)⟩,
    ⟨(.reg 11 : Operand 32), (W 54)⟩,
    ⟨(.reg 12 : Operand 32), (W 44)⟩,
    ⟨(.reg 13 : Operand 32), (W 43)⟩,
    ⟨(.reg 14 : Operand 32), (W 56)⟩,
    ⟨(.mem (stack + 0) : Operand 32), (W 57)⟩,
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
    ⟨(.mem (stack + 88) : Operand 32), (W 50)⟩,
    ⟨(.mem (stack + 96) : Operand 32), (W 49)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

private def genericCut063 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), (A 58)⟩,
    ⟨(.reg 1 : Operand 32), ((A 57)).rotateLeft 30⟩,
    ⟨(.reg 2 : Operand 32), (A 59)⟩,
    ⟨(.reg 3 : Operand 32), (W 48)⟩,
    ⟨(.reg 7 : Operand 32), ((A 56)).rotateLeft 30⟩,
    ⟨(.reg 9 : Operand 32), ((W 59) + ((A 55)).rotateLeft 30)⟩,
    ⟨(.reg 10 : Operand 32), (W 57)⟩,
    ⟨(.reg 11 : Operand 32), (W 54)⟩,
    ⟨(.reg 12 : Operand 32), (W 44)⟩,
    ⟨(.reg 13 : Operand 32), (W 59)⟩,
    ⟨(.reg 14 : Operand 32), (W 56)⟩,
    ⟨(.mem (stack + 0) : Operand 32), (W 57)⟩,
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
    ⟨(.mem (stack + 80) : Operand 32), (W 59)⟩,
    ⟨(.mem (stack + 88) : Operand 32), (W 50)⟩,
    ⟨(.mem (stack + 96) : Operand 32), (W 49)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

theorem effect062_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (he : (effect062 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hfoot : ∀ c ∈ (effect062 s).components, c ∈ [.mem ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 80) 8, .reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect062
    iterate 17 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [leaR32Effect_components, addR32Imm32Effect_components, addR32R32Effect_components, andR32R32Effect_components, movM64R64Effect_components, movR32R32Effect_components, rolR32Effect_components, xorR32M32Effect_components, xorR32R32Effect_components, List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and, forall_eq, or_true]
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

theorem effect062_rip {s t : RamState}
    (he : (effect062 s).Holds s t) :
    t.RIP = 0x103246 := by
  exact he.rip.trans (by rfl)

section Words062

private theorem full062 (s : RamState) : ∀ w ∈ (effect062 s).writes, w.Full := by
  apply Effect.Local.full
  unfold effect062
  repeat' first | (solve | x86_local) | apply Effect.Local.seq

set_option maxRecDepth 4096 in
private theorem rawR1_062 {s t : RamState} (v1 : BitVec 32)
    (h1 : (Operand.reg 1 : Operand 32).read s = v1)
    (he : (effect062 s).Holds s t) :
    (Operand.reg 1 : Operand 32).read t = v1.rotateLeft 30 := by
  have ho := he.obsAfter (full062 s) true
  sha1_norm at h1
  simp only [← ho.read_reg]
  sha1_norm [leaSpec, effect062, h1]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]

set_option maxRecDepth 4096 in
private theorem rawR7_062 {s t : RamState} (v7 : BitVec 32)
    (h7 : (Operand.reg 7 : Operand 32).read s = v7)
    (he : (effect062 s).Holds s t) :
    (Operand.reg 7 : Operand 32).read t = v7.rotateLeft 30 := by
  have ho := he.obsAfter (full062 s) true
  sha1_norm at h7
  simp only [← ho.read_reg]
  sha1_norm [leaSpec, effect062, h7]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]

set_option maxRecDepth 4096 in
private theorem rawR13_062 {stack : BitVec 64} {s t : RamState}
    (v13 v14 m16 m56 : BitVec 32)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (h13 : (Operand.reg 13 : Operand 32).read s = v13)
    (h14 : (Operand.reg 14 : Operand 32).read s = v14)
    (hM16 : (Operand.mem (stack + 16) : Operand 32).read s = m16)
    (hM56 : (Operand.mem (stack + 56) : Operand 32).read s = m56)
    (he : (effect062 s).Holds s t) :
    (Operand.reg 13 : Operand 32).read t =
      (v13 ^^^ m16 ^^^ m56 ^^^ v14).rotateLeft 1 := by
  have ho := he.obsAfter (full062 s) true
  sha1_norm at hs h13 h14 hM16 hM56
  simp only [← ho.read_reg]
  sha1_norm [leaSpec, effect062, hs, h13, h14, hM16, hM56]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]

set_option maxRecDepth 4096 in
private theorem rawR9_062 {stack : BitVec 64} {s t : RamState}
    (v2 v13 v14 m16 m56 : BitVec 32)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (h2 : (Operand.reg 2 : Operand 32).read s = v2)
    (h13 : (Operand.reg 13 : Operand 32).read s = v13)
    (h14 : (Operand.reg 14 : Operand 32).read s = v14)
    (hM16 : (Operand.mem (stack + 16) : Operand 32).read s = m16)
    (hM56 : (Operand.mem (stack + 56) : Operand 32).read s = m56)
    (he : (effect062 s).Holds s t) :
    (Operand.reg 9 : Operand 32).read t =
      v2 + (v13 ^^^ m16 ^^^ m56 ^^^ v14).rotateLeft 1 := by
  have ho := he.obsAfter (full062 s) true
  sha1_norm at hs h2 h13 h14 hM16 hM56
  have h2' := h2
  change BitVec.setWidth 32 s.GPR[gprIndex 2] = v2 at h2'
  simp only [← ho.read_reg]
  sha1_norm [leaSpec, effect062, hs, h2, h13, h14, hM16, hM56]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
  rw [BitVec.setWidth_add (i := 32) _ _ (by decide : 32 ≤ 64)]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [Operand.read, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
      BitVec.shiftLeft_zero, BitVec.add_zero]
  exact congrArg (fun x : BitVec 32 ↦ x + (v13 ^^^ m16 ^^^ m56 ^^^ v14).rotateLeft 1) h2'

set_option maxRecDepth 4096 in
private theorem rawM80_062 {stack : BitVec 64} {s t : RamState}
    (v13 v14 m16 m56 : BitVec 32)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (h13 : (Operand.reg 13 : Operand 32).read s = v13)
    (h14 : (Operand.reg 14 : Operand 32).read s = v14)
    (hM16 : (Operand.mem (stack + 16) : Operand 32).read s = m16)
    (hM56 : (Operand.mem (stack + 56) : Operand 32).read s = m56)
    (he : (effect062 s).Holds s t) :
    (Operand.mem (stack + 80) : Operand 32).read t =
      (v13 ^^^ m16 ^^^ m56 ^^^ v14).rotateLeft 1 := by
  have ho := he.obsAfter (full062 s) true
  sha1_norm at hs h13 h14 hM16 hM56
  simp only [← ho.read_mem]
  sha1_norm [leaSpec, effect062, hs]
  rw [read32_memStore64_low]
  sha1_norm [leaSpec, effect062, h13,h14,hM16,hM56,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    BitVec.extractLsb'_setWidth_of_le, BitVec.extractLsb'_eq_self]

private def prefix062 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (xorR32M32Effect 0x10320d 13 (.sib 4 none 0 (.d8 0x10))) (xorR32M32Effect 0x103212 13 (.sib 4 none 0 (.d8 0x38)))) (xorR32R32Effect 0x103217 3 13 14)) (rolR32Effect 0x10321a 3 13 1)) (rolR32Effect 0x10321d 3 7 30)) (movR32R32Effect 0x103220 2 6 7)) (xorR32R32Effect 0x103222 2 6 2)) (andR32R32Effect 0x103224 2 6 1)) (leaR32Effect 0x103226 4 9 (.sib 2 (some 13) 0 .none))) (movM64R64Effect 0x10322a 13 (.sib 4 none 0 (.d8 0x50)))) (andR32R32Effect 0x10322f 2 2 7)) (xorR32R32Effect 0x103231 2 2 6)) (addR32R32Effect 0x103233 3 2 8)) (movR32R32Effect 0x103236 2 6 0)) (rolR32Effect 0x103238 3 6 5)) (rolR32Effect 0x10323b 3 1 30)) (addR32R32Effect 0x10323e 2 2 6)

private theorem effect062_split : effect062 =
    Effect.seq prefix062 (addR32Imm32Effect 0x103240 6 2 0x8f1bbcdc) := by
  rfl

private theorem seqLastWrites062 {E F : RamState → Effect} {s t : RamState}
    (h : (Effect.seq E F s).Holds s t) :
    Write.AllHold t (F ((E s).after s true)).writes := by
  apply Write.allHold_iff.mpr
  intro w hw
  apply Write.allHold_iff.mp h.writes w
  exact List.mem_append_right _ hw

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem rawR2_062 {s t : RamState}
    (v0 v1 v2 v7 v8 : BitVec 32)
    (h0 : (Operand.reg 0 : Operand 32).read s = v0)
    (h1 : (Operand.reg 1 : Operand 32).read s = v1)
    (h2 : (Operand.reg 2 : Operand 32).read s = v2)
    (h7 : (Operand.reg 7 : Operand 32).read s = v7)
    (h8 : (Operand.reg 8 : Operand 32).read s = v8)
    (he : (effect062 s).Holds s t) :
    (Operand.reg 2 : Operand 32).read t =
      ((v2 &&& v7.rotateLeft 30) ^^^ ((v7.rotateLeft 30 ^^^ v2) &&& v1)) +
        v8 + v0.rotateLeft 5 + 0x8f1bbcdc := by
  sha1_norm at h0 h1 h2 h7 h8
  rw [effect062_split] at he
  have hl := seqLastWrites062 he
  change (Operand.reg 2 : Operand 64).read t =
    ((Operand.reg 2 : Operand 32).read ((prefix062 s).after s true) +
      (0x8f1bbcdc : BitVec 32).signExtend 32).setWidth 64 at hl
  have hr := congrArg (fun x : BitVec 64 ↦ x.setWidth 32) hl
  simp (config := { decide := true, implicitDefEqProofs := false }) only [Operand.read,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq] at hr
  change (Operand.reg 2 : Operand 32).read t =
    (Operand.reg 2 : Operand 32).read ((prefix062 s).after s true) +
      (0x8f1bbcdc : BitVec 32).signExtend 32 at hr
  rw [hr]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [x86_compose, prefix062, h0,h1,h2,h7,h8]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
  ac_rfl

set_option maxRecDepth 4096 in
private theorem genericWords062 {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) {s t : RamState}
    (hA59 : A 59 = (A 58).rotateLeft 5 +
      (((A 55).rotateLeft 30 &&& (A 56).rotateLeft 30) ^^^
        (((A 56).rotateLeft 30 ^^^ (A 55).rotateLeft 30) &&& A 57)) +
      (W 58 + (A 54).rotateLeft 30) + 0x8f1bbcdc)
    (hW59 : W 59 = (W 56 ^^^ W 51 ^^^ W 45 ^^^ W 43).rotateLeft 1)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hw : Write.AllHold s (genericCut062 stack input H A W))
    (he : (effect062 s).Holds s t) :
    Write.AllHold t (genericCut063 stack input H A W) := by
  simp only [genericCut062, Write.AllHold] at hw
  obtain ⟨h0,h1,h2,h3,h7,h8,h10,h11,h12,h13,h14,hM0,hM4,hM8,hM12,hM16,hM24,hM32,hM40,hM48,hM56,hM64,hM72,hM88,hM96,hM116,hM120,hM124,hM144,hM152⟩ := hw
  have hW : (W 43 ^^^ W 45 ^^^ W 51 ^^^ W 56).rotateLeft 1 = W 59 := by
    rw [hW59]
    congr 1
    ac_rfl
  have hR1 := rawR1_062 (A 57) h1 he
  have hR7 := rawR7_062 (A 56) h7 he
  have hR13 := (rawR13_062 (W 43) (W 56) (W 45) (W 51)
    hs h13 h14 hM16 hM56 he).trans hW
  have hR9 := rawR9_062 ((A 55).rotateLeft 30) (W 43) (W 56) (W 45) (W 51)
    hs h2 h13 h14 hM16 hM56 he
  have hV9 : (Operand.reg 9 : Operand 32).read t = W 59 + (A 55).rotateLeft 30 := by
    rw [hR9, hW]
    exact BitVec.add_comm _ _
  have hM80 := (rawM80_062 (W 43) (W 56) (W 45) (W 51)
    hs h13 h14 hM16 hM56 he).trans hW
  have hR2 := rawR2_062 (A 58) (A 57) ((A 55).rotateLeft 30) (A 56)
    (W 58 + (A 54).rotateLeft 30) h0 h1 h2 h7 h8 he
  have hV2 : (Operand.reg 2 : Operand 32).read t = A 59 := by
    rw [hR2, hA59]
    ac_rfl
  have hfoot : ∀ c ∈ (effect062 s).components,
      c ∈ [.mem ((Operand.reg 4 : Operand 64).read s + 80) 8,
        .reg 1, .reg 2, .reg 6, .reg 7, .reg 9, .reg 13, .flags, .rip] := by
    unfold effect062
    iterate 17 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [movM64R64Effect_components, movR32R32Effect_components,
        xorR32M32Effect_components, xorR32R32Effect_components,
        rolR32Effect_components, andR32R32Effect_components,
        leaR32Effect_components,
        addR32R32Effect_components, addR32Imm32Effect_components,
        List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and, forall_eq, or_true]
    all_goals sha1_norm
  have ha := he.agrees.mono hfoot
  rw [hs] at ha
  have hmem {n : Nat} (off : BitVec 64) (hb : OffsetsApart 80 8 off (n / 8))
      (hsize : 8 + n / 8 < 2 ^ 64) :
      (Operand.mem (stack + off) : Operand n).read t =
      (Operand.mem (stack + off) : Operand n).read s := by
    apply memLoad_congr
    intro i hi
    apply congrArg (fun b : Option UInt8 ↦ b.getD 0)
    apply ha.byte
    intro c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨j,hj,heq⟩ := hCov
      exact hb.ne stack hj hi hsize heq.symm
    all_goals exact hCov.elim
  simp only [genericCut063, Write.AllHold]
  refine ⟨?f0, ?f1, ?f2, ?f3, ?f4, ?f5, ?f6, ?f7, ?f8, ?f9, ?f10, ?f11, ?f12, ?f13, ?f14, ?f15, ?f16, ?f17, ?f18, ?f19, ?f20, ?f21, ?f22, ?f23, ?f24, ?f25, ?f26, ?f27, ?f28, ?f29, ?f30⟩
  case f0 => exact (ha.read (by simp)).trans h0
  case f1 => exact hR1
  case f2 => exact hV2
  case f3 => exact (ha.read (by simp)).trans h3
  case f4 => exact hR7
  case f5 => exact hV9
  case f6 => exact (ha.read (by simp)).trans h10
  case f7 => exact (ha.read (by simp)).trans h11
  case f8 => exact (ha.read (by simp)).trans h12
  case f9 => exact hR13
  case f10 => exact (ha.read (by simp)).trans h14
  case f11 => exact (hmem 0 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM0
  case f12 => exact (hmem 4 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM4
  case f13 => exact (hmem 8 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM8
  case f14 => exact (hmem 12 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM12
  case f15 => exact (hmem 16 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM16
  case f16 => exact (hmem 24 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM24
  case f17 => exact (hmem 32 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM32
  case f18 => exact (hmem 40 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM40
  case f19 => exact (hmem 48 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM48
  case f20 => exact (hmem 56 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM56
  case f21 => exact (hmem 64 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM64
  case f22 => exact (hmem 72 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM72
  case f23 => exact hM80
  case f24 => exact (hmem 88 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM88
  case f25 => exact (hmem 96 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM96
  case f26 => exact (hmem 116 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM116
  case f27 => exact (hmem 120 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM120
  case f28 => exact (hmem 124 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM124
  case f29 => exact (hmem 144 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM144
  case f30 => exact (hmem 152 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM152

private theorem workingAfter59 (M : Vector (BitVec 32) 16) (H : Vector (BitVec 32) 5) :
    (workingAfter M H 59).a = ((workingAfter M H 58).a).rotateLeft 5 +
      ((((workingAfter M H 55).a).rotateLeft 30 &&&
        ((workingAfter M H 56).a).rotateLeft 30) ^^^
        ((((workingAfter M H 56).a).rotateLeft 30 ^^^
          ((workingAfter M H 55).a).rotateLeft 30) &&& (workingAfter M H 57).a)) +
      (scheduleWord M 58 + ((workingAfter M H 54).a).rotateLeft 30) + 0x8f1bbcdc := by
  have hMaj (x y z : BitVec 32) :
      Standards.NIST.SHA2.SHA256.Maj x y z =
        (z &&& y) ^^^ ((y ^^^ z) &&& x) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [Standards.NIST.SHA2.SHA256.Maj, BitVec.getLsbD_xor, BitVec.getLsbD_and]
    cases x.getLsbD i <;> cases y.getLsbD i <;> cases z.getLsbD i <;> decide
  have h := workingAfter_step_a_values M H 54 (by decide)
  rw [sha1_f_majority (t := ⟨58, by decide⟩) (by decide) (by decide)] at h
  simp only [Nat.reduceAdd] at h
  rw [show K (⟨58, by decide⟩ : Fin 80) = 0x8f1bbcdc by decide, hMaj] at h
  calc
    _ = _ := h
    _ = _ := by ac_rfl

private theorem schedule59 (M : Vector (BitVec 32) 16) :
    scheduleWord M 59 =
      (scheduleWord M 56 ^^^ scheduleWord M 51 ^^^ scheduleWord M 45 ^^^
        scheduleWord M 43).rotateLeft 1 := by
  change scheduleWord M (⟨59, by decide⟩ : Fin 80) = _
  rw [scheduleWord_recurrence M ⟨59, by decide⟩ (by decide),
    sha1Rotl_eq_rotateLeft 1 _ (by decide)]
  simp only [Nat.reduceSub]
  rfl

theorem effect062_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16}
    {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut062 stack input H M))
    (he : (effect062 s).Holds s t) :
    Write.AllHold t (cut063 stack input H M) := by
  exact genericWords062 (fun n ↦ (workingAfter M H n).a) (scheduleWord M)
    (workingAfter59 M H) (schedule59 M) hf.stackPointer hw he
end Words062

end Block062

open Block062 in
theorem segment062 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x10320d 0x103246
      cut062 cut063 := by
  have hout : ∀ d : Nat, d ≤ bytes062.length →
      0x10320d + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      simp only [bytes062, List.length_cons, List.length_nil] at hd <;>
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  apply Segment.of_block (fun _ _ _ _ => effect062)
    (fun stack input H M => block062 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64
      0x320d) bytes062,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect062_rip he
  · intro stack input H M s t _ hf _ he
    exact effect062_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect062_words hf hw he

namespace Block063

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Spec.Program
open Standards.NIST.SHA1
open Sha1.Proofs.Compress.Rounds



def bytes063 : List UInt8 :=
  [0x89, 0xce, 0x31, 0xfe, 0x21, 0xc6, 0x41, 0x89, 0xc8, 0x41, 0x21, 0xf8, 0x41, 0x31, 0xf0, 0x45, 0x01, 0xc8, 0xc1, 0xc0, 0x1e, 0x48, 0x8b, 0x74, 0x24, 0x48, 0x41, 0x31, 0xf4, 0x31, 0xde, 0x44, 0x31, 0xde, 0x44, 0x31, 0xee, 0xd1, 0xc6, 0x49, 0x89, 0xf1, 0x48, 0x89, 0x74, 0x24, 0x48, 0x89, 0xd6, 0xc1, 0xc6, 0x1e]

def effect063 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq ((movR32R32Effect 0x103246 2 6 1)) (xorR32R32Effect 0x103248 2 6 7)) (andR32R32Effect 0x10324a 2 6 0)) (movR32R32Effect 0x10324c 3 8 1)) (andR32R32Effect 0x10324f 3 8 7)) (xorR32R32Effect 0x103252 3 8 6)) (addR32R32Effect 0x103255 3 8 9)) (rolR32Effect 0x103258 3 0 30)) (movR64M64Effect 0x10325b 6 (.sib 4 none 0 (.d8 0x48)))) (xorR32R32Effect 0x103260 3 12 6)) (xorR32R32Effect 0x103263 2 6 3)) (xorR32R32Effect 0x103265 3 6 11)) (xorR32R32Effect 0x103268 3 6 13)) (rolR32Effect 0x10326b 2 6 1)) (movR64R64Effect 0x10326d 9 6)) (movM64R64Effect 0x103270 6 (.sib 4 none 0 (.d8 0x48)))) (movR32R32Effect 0x103275 2 6 2)) (rolR32Effect 0x103277 3 6 30)

set_option maxHeartbeats 800000 in
theorem block063 [Bindings] (boundary : ReturnBoundary) (stack input : BitVec 64)
    (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes063.length →
      0x103246 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x103246 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut063 stack input H M))
      (codeRange 0x103246 bytes063) effect063 := by
  have hRaw : AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x103246 ∧ FrameData stack input M s)
      (codeRange 0x103246 bytes063) effect063 := by
    unfold bytes063 at hout ⊢
    sha1_run_begin (mov_r32_r32_effect_step 0x103246 0xce (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (xor_r32_r32_effect_step 0x103248 0xfe (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (and_r32_r32_effect_step 0x10324a 0xc6 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (mov_r32_r32_rex_effect_step 0x10324c 0x41 0xc8 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (and_r32_r32_rex_effect_step 0x10324f 0x41 0xf8 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (xor_r32_r32_rex_effect_step 0x103252 0x41 0xf0 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (add_r32_r32_rex_effect_step 0x103255 0x45 0xc8 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (rol_r32_imm8_effect_step 0x103258 0xc0 0x1e (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (mov_r64_m64_effect_step 0x10325b 0x48 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) 6 (.sib 4 none 0 (.d8 0x48)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (xor_r32_r32_rex_effect_step 0x103260 0x41 0xf4 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (xor_r32_r32_effect_step 0x103263 0xde (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (xor_r32_r32_rex_effect_step 0x103265 0x44 0xde (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (xor_r32_r32_rex_effect_step 0x103268 0x44 0xee (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (rol_r32_one_effect_step 0x10326b 0xc6 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (mov_r64_r64_effect_step 0x10326d 0x49 0xf1 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step 0x103270 0x48 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) 6 (.sib 4 none 0 (.d8 0x48)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (mov_r32_r32_effect_step 0x103275 0xd6 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (rol_r32_imm8_effect_step 0x103277 0xc6 0x1e (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_finish [effect063]
  intro s hr hc hp
  exact hRaw s hr hc ⟨hp.1, hp.2.1⟩

private def genericCut063 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), (A 58)⟩,
    ⟨(.reg 1 : Operand 32), ((A 57)).rotateLeft 30⟩,
    ⟨(.reg 2 : Operand 32), (A 59)⟩,
    ⟨(.reg 3 : Operand 32), (W 48)⟩,
    ⟨(.reg 7 : Operand 32), ((A 56)).rotateLeft 30⟩,
    ⟨(.reg 9 : Operand 32), ((W 59) + ((A 55)).rotateLeft 30)⟩,
    ⟨(.reg 10 : Operand 32), (W 57)⟩,
    ⟨(.reg 11 : Operand 32), (W 54)⟩,
    ⟨(.reg 12 : Operand 32), (W 44)⟩,
    ⟨(.reg 13 : Operand 32), (W 59)⟩,
    ⟨(.reg 14 : Operand 32), (W 56)⟩,
    ⟨(.mem (stack + 0) : Operand 32), (W 57)⟩,
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
    ⟨(.mem (stack + 80) : Operand 32), (W 59)⟩,
    ⟨(.mem (stack + 88) : Operand 32), (W 50)⟩,
    ⟨(.mem (stack + 96) : Operand 32), (W 49)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

private def genericCut064 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), ((A 58)).rotateLeft 30⟩,
    ⟨(.reg 1 : Operand 32), ((A 57)).rotateLeft 30⟩,
    ⟨(.reg 2 : Operand 32), (A 59)⟩,
    ⟨(.reg 6 : Operand 32), ((A 59)).rotateLeft 30⟩,
    ⟨(.reg 7 : Operand 32), ((A 56)).rotateLeft 30⟩,
    ⟨(.reg 8 : Operand 32), ((W 59) + ((A 55)).rotateLeft 30 + (((A 58) &&& ((A 56)).rotateLeft 30) ^^^ ((A 58) &&& ((A 57)).rotateLeft 30) ^^^ (((A 56)).rotateLeft 30 &&& ((A 57)).rotateLeft 30)))⟩,
    ⟨(.reg 9 : Operand 32), (W 62)⟩,
    ⟨(.reg 10 : Operand 32), (W 57)⟩,
    ⟨(.reg 12 : Operand 32), ((W 44) ^^^ (W 46))⟩,
    ⟨(.reg 14 : Operand 32), (W 56)⟩,
    ⟨(.mem (stack + 0) : Operand 32), (W 57)⟩,
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
    ⟨(.mem (stack + 72) : Operand 32), (W 62)⟩,
    ⟨(.mem (stack + 80) : Operand 32), (W 59)⟩,
    ⟨(.mem (stack + 88) : Operand 32), (W 50)⟩,
    ⟨(.mem (stack + 96) : Operand 32), (W 49)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

theorem effect063_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (he : (effect063 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hfoot : ∀ c ∈ (effect063 s).components, c ∈ [.mem ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 72) 8, .reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect063
    iterate 17 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [addR32R32Effect_components, andR32R32Effect_components, movM64R64Effect_components, movR32R32Effect_components, movR64M64Effect_components, movR64R64Effect_components, rolR32Effect_components, xorR32R32Effect_components, List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and, forall_eq, or_true]
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

theorem effect063_rip {s t : RamState}
    (he : (effect063 s).Holds s t) :
    t.RIP = 0x10327a := by
  exact he.rip.trans (by rfl)

section Words063
set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem genericWords063 {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    (M : Vector (BitVec 32) 16) (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32)
    (hW62 : W 62 = Standards.NIST.SHA1.ROTL 1 (W 59 ^^^ W 54 ^^^ W 48 ^^^ W 46))
    {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (genericCut063 stack input H A W))
    (he : (effect063 s).Holds s t) :
    Write.AllHold t (genericCut064 stack input H A W) := by
  have hfull : ∀ w ∈ (effect063 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect063
    repeat' first
      | solve | x86_local
      | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  sha1_norm at hs
  simp only [genericCut063, Write.AllHold] at hw
  obtain ⟨h0, h1, h2, h3, h7, h9, h10, h11, h12, h13, h14,
    hM0, hM4, hM8, hM12, hM16, hM24, hM32, hM40, hM48, hM56,
    hM64, hM72, hM80, hM88, hM96, hM116, hM120, hM124, hM144, hM152⟩ := hw
  sha1_norm at h0 h1 h2 h3 h7 h9 h10 h11 h12 h13 h14
  sha1_norm at hM0 hM4 hM8 hM12 hM16 hM24 hM32 hM40 hM48 hM56
  sha1_norm at hM64 hM72 hM80 hM88 hM96 hM116 hM120 hM124 hM144 hM152
  simp only [genericCut064, Write.AllHold, ← ho.read_reg, ← ho.read_mem]
  sha1_norm [leaSpec, effect063, hs, h0, h1, h2, h3, h7, h9, h10, h11, h12, h13, h14,
    hM0, hM4, hM8, hM12, hM16, hM24, hM32, hM40, hM48, hM56,
    hM64, hM72, hM80, hM88, hM96, hM116, hM120, hM124, hM144, hM152]
  simp (config := {decide := true, implicitDefEqProofs := false}) only [Operand.read,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
  have hMaj (a b c : BitVec 32) :
      (b &&& c) ^^^ ((b ^^^ c) &&& a) =
        (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and]
    cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.getLsbD i <;> decide
  simp only [hW62, sha1Rotl_eq_rotateLeft 1 _ (by decide)]
  rw [hMaj]
  have hread72 : memLoad s.external (stack + BitVec.ofNat 64 72) 32 = W 46 := by
    change (Operand.mem (stack + BitVec.ofNat 64 72) : Operand 32).read s = W 46
    exact hM72
  have hload72 := memLoad_extractLsb'
    s.external (stack + BitVec.ofNat 64 72) 64 32 0 (by decide) (by decide)
  have hload72' : memLoad s.external (stack + BitVec.ofNat 64 72) 32 =
      BitVec.extractLsb' 0 32 (memLoad s.external (stack + BitVec.ofNat 64 72) 64) := by
    simpa only [BitVec.add_zero] using hload72
  have hM72' : BitVec.setWidth 32 (memLoad s.external (stack + BitVec.ofNat 64 72) 64) =
      W 46 := by
    rw [BitVec.setWidth_eq_extractLsb' (by decide)]
    exact hload72'.symm.trans hread72
  simp only [hM72']
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | rfl
    | ac_rfl
    | (rw [read32_memStore64_low];
       rw [extractLsb'_zero_eq_setWidth _ 32 (by decide)];
       rw [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)];
       ac_rfl)

theorem effect063_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16}
    {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut063 stack input H M))
    (he : (effect063 s).Holds s t) :
    Write.AllHold t (cut064 stack input H M) := by
  have hW62 : scheduleWord M 62 =
      Standards.NIST.SHA1.ROTL 1 (scheduleWord M 59 ^^^ scheduleWord M 54 ^^^
        scheduleWord M 48 ^^^ scheduleWord M 46) := by
    exact scheduleWord_recurrence M ⟨62, by decide⟩ (by decide)
  have hpre : Write.AllHold s
      (genericCut063 stack input H (fun n ↦ (workingAfter M H n).a) (scheduleWord M)) := by
    change Write.AllHold s (cut063 stack input H M)
    exact hw
  have hmodel := genericWords063 M (fun n ↦ (workingAfter M H n).a) (scheduleWord M)
    hW62 hf hpre he
  change Write.AllHold t (cut064 stack input H M) at hmodel
  exact hmodel
end Words063

end Block063

open Block063 in
theorem segment063 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x103246 0x10327a
      cut063 cut064 := by
  have hout : ∀ d : Nat, d ≤ bytes063.length →
      0x103246 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      simp only [bytes063, List.length_cons, List.length_nil] at hd <;>
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  apply Segment.of_block (fun _ _ _ _ => effect063)
    (fun stack input H M => block063 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64
      0x3246) bytes063,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect063_rip he
  · intro stack input H M s t _ hf _ he
    exact effect063_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect063_words hf hw he

namespace Block064

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Spec.Program
open Standards.NIST.SHA1 Sha1.Proofs.Compress.Rounds


def bytes064 : List UInt8 :=
  [0x89, 0xf5, 0x31, 0xc5, 0x41, 0x1, 0xc1, 0x44, 0x89, 0x4c, 0x24, 0x68, 0x31, 0xc8, 0x31, 0xd0, 0xc1, 0xc2, 0x5, 0x44, 0x1, 0xc2, 0x81, 0xc2, 0xdc, 0xbc, 0x1b, 0x8f, 0x8b, 0x5c, 0x24, 0x8, 0x4d, 0x89, 0xe7, 0x41, 0x31, 0xdf, 0x45, 0x31, 0xd7, 0x41, 0xd1, 0xc7, 0x41, 0x89, 0xd0, 0x41, 0xc1, 0xc0, 0x5, 0x44, 0x1, 0xff, 0x1, 0xc7, 0x41, 0x8d, 0x4, 0x38, 0x5, 0xd6, 0xc1, 0x62, 0xca]

set_option maxHeartbeats 800000 in
def effect064 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq ((movR32R32Effect 0x10327a 2 5 6)) (xorR32R32Effect 0x10327c 2 5 0)) (addR32R32Effect 0x10327e 3 9 0)) (movM32R32Effect 0x103281 9 (.sib 4 none 0 (.d8 0x68)))) (xorR32R32Effect 0x103286 2 0 1)) (xorR32R32Effect 0x103288 2 0 2)) (rolR32Effect 0x10328a 3 2 5)) (addR32R32Effect 0x10328d 3 2 8)) (addR32Imm32Effect 0x103290 6 2 0x8f1bbcdc)) (movR32M32LowEffect 0x103296 3 (.sib 4 none 0 (.d8 0x8)))) (movR64R64Effect 0x10329a 15 12)) (xorR32R32Effect 0x10329d 3 15 3)) (xorR32R32Effect 0x1032a0 3 15 10)) (rolR32Effect 0x1032a3 3 15 1)) (movR32R32Effect 0x1032a6 3 8 2)) (rolR32Effect 0x1032a9 4 8 5)) (addR32R32Effect 0x1032ad 3 7 15)) (addR32R32Effect 0x1032b0 2 7 0)) (leaR32Effect 0x1032b2 4 0 (.sib 8 (some 7) 0 .none))) (addEaxImm32Effect 0x1032b6 0xca62c1d6)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
theorem block064 [Bindings] (boundary : ReturnBoundary)
    (stack input : BitVec 64) (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes064.length → 0x10327a + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x10327a ∧ FrameData stack input M s ∧
        Write.AllHold s (cut064 stack input H M))
      (codeRange 0x10327a bytes064) effect064 := by
  unfold bytes064 at hout ⊢
  sha1_run_begin (mov_r32_r32_effect_step 0x10327a 0xf5 (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x10327c 0xc5 (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x10327e 0x41 0xc1 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m32_r32_effect_step 0x103281 0x44 (by unfold RexNoWPrefix; decide +kernel) 1 (.sib 4 none 0 (.d8 0x68)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x103286 0xc8 (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x103288 0xd0 (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x10328a 0xc2 0x5 (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x10328d 0x44 0xc2 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_imm32_effect_step 0x103290 0xc2 0x8f1bbcdc (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_m32_low_effect_step 0x103296 3 (.sib 4 none 0 (.d8 0x8)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_r64_effect_step 0x10329a 0x4d 0xe7 (by unfold RexWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x10329d 0x41 0xdf (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x1032a0 0x45 0xd7 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_one_rex_effect_step 0x1032a3 0x41 0xc7 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x1032a6 0x41 0xd0 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_imm8_rex_effect_step 0x1032a9 0x41 0xc0 0x5 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x1032ad 0x44 0xff (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x1032b0 0xc7 (by decide +kernel))
  sha1_run_then (lea_r32_rex_effect_step 0x1032b2 0x41 (by unfold RexNoWPrefix; decide +kernel) 0 (.sib 8 (some 7) 0 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_eax_imm32_effect_step 0x1032b6 0xca62c1d6)
  sha1_run_finish [effect064]

set_option maxRecDepth 10000 in
private theorem components064 (s : RamState) :
    ∀ c ∈ (effect064 s).components, c ∈ [.mem ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 104) 4, .reg 0, .reg 2, .reg 3, .reg 5, .reg 7, .reg 8, .reg 9, .reg 15, .flags, .rip] := by
  unfold effect064
  iterate 19 apply components_seq_of
  all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
    [addEaxImm32Effect_components, addR32Imm32Effect_components, addR32R32Effect_components, leaR32Effect_components, movM32R32Effect_components, movR32M32LowEffect_components, movR32R32Effect_components, movR64R64Effect_components, rolR32Effect_components, xorR32R32Effect_components, List.mem_cons, List.not_mem_nil,
      or_false, or_imp, forall_and, forall_eq, or_true]
  all_goals sha1_norm

set_option maxRecDepth 10000 in
theorem effect064_agrees {stack input : BitVec 64} {M : Vector (BitVec 32) 16}
    {s t : RamState} (hf : FrameData stack input M s) (he : (effect064 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have ha := he.agrees.mono (components064 s)
  rw [hs] at ha
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all (config := {decide := true, implicitDefEqProofs := false}) only
      [Component.isMem, scratchComponents, x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hCov.elim
      | exact scratchComponents_stack (Or.inl (by decide +kernel)) hCov

set_option maxRecDepth 10000 in
private theorem full064 (s : RamState) : ∀ w ∈ (effect064 s).writes, w.Full := by
  apply Effect.Local.full
  unfold effect064
  repeat' first | (solve | x86_local) | apply Effect.Local.seq

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
theorem effect064_words {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (hw : Write.AllHold s (cut064 stack input H M))
    (he : (effect064 s).Holds s t) : Write.AllHold t (cut065 stack input H M) := by
  have ho := he.obsAfter (full064 s) true
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have ha := he.agrees.mono (components064 s)
  rw [hs] at ha
  simp only [cut064, Write.AllHold] at hw
  obtain ⟨h0, h1, h2, h6, h7, h8, h9, h10, h12, h14, hM0, hM4, hM8, hM12, hM16, hM24, hM32, hM40, hM48, hM56, hM64, hM72, hM80, hM88, hM96, hM116, hM120, hM124, hM144, hM152⟩ := hw
  have hmem {width : Nat} (off : BitVec 64)
      (hb : OffsetsApart 104 4 off (width / 8)) (hz : 4 + width / 8 < 2 ^ 64) :
      (Operand.mem (stack + off) : Operand width).read t =
      (Operand.mem (stack + off) : Operand width).read s := by
    apply memLoad_congr
    intro i hi
    apply congrArg (fun b : Option UInt8 ↦ b.getD 0)
    apply ha.byte
    intro c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨j, hj, heq⟩ := hCov
      exact hb.ne stack hj hi hz heq.symm
    all_goals exact hCov.elim
  have hA61 := workingAfter_step_a_values M H 56 (by decide +kernel)
  simp (config := {decide := true}) only [Nat.reduceAdd, f, K, Parity, ite_false] at hA61
  have hT60 : (⟨60, by decide +kernel⟩ : Fin 80) = 60 := by decide +kernel
  simp only [hT60] at hA61
  sha1_norm at hA61
  have hA60 := workingAfter_step_a_values M H 55 (by decide +kernel)
  simp (config := {decide := true}) only [Nat.reduceAdd, f, K, ite_false, ite_true, Standards.NIST.SHA2.SHA256.Maj] at hA60
  have hT59 : (⟨59, by decide +kernel⟩ : Fin 80) = 59 := by decide +kernel
  simp only [hT59] at hA60
  sha1_norm at hA60
  have hW60 : scheduleWord M 60 =
      (scheduleWord M 57 ^^^ scheduleWord M 52 ^^^
        scheduleWord M 46 ^^^ scheduleWord M 44).rotateLeft 1 := by
    change scheduleWord M (⟨60, by decide +kernel⟩ : Fin 80) = _
    rw [scheduleWord_recurrence M ⟨60, by decide +kernel⟩ (by decide +kernel),
      sha1Rotl_eq_rotateLeft 1 _ (by decide +kernel)]
    simp only [Nat.reduceSub]
    all_goals rfl
  simp only [cut065, Write.AllHold]
  refine ⟨?f0, ?f1, ?f2, ?f3, ?f4, ?f5, ?f6, ?f7, ?f8, ?f9, ?f10, ?f11, ?f12, ?f13, ?f14, ?f15, ?f16, ?f17, ?f18, ?f19, ?f20, ?f21, ?f22, ?f23, ?f24, ?f25, ?f26, ?f27, ?f28⟩
  case f0 =>
    sha1_norm at hs h0 h1 h2 h6 h7 h8 h9 h10 h12 h14 hM0 hM4 hM8 hM12 hM16 hM24 hM32 hM40 hM48 hM56 hM64 hM72 hM80 hM88 hM96 hM116 hM120 hM124 hM144 hM152
    simp only [← ho.read_reg]
    sha1_norm [effect064, hs, h0, h1, h2, h6, h7, h8, h9, h10, h12, h14, hM0, hM4, hM8, hM12, hM16, hM24, hM32, hM40, hM48, hM56, hM64, hM72, hM80, hM88, hM96, hM116, hM120, hM124, hM144, hM152, leaSpec,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, read32_memStore64_low,
      extractLsb'_zero_eq_setWidth, memLoad_memStore]
    all_goals simp only [hA61, hA60, hW60]
    all_goals ac_rfl
  case f1 =>
    exact (ha.read (by simp)).trans h1
  case f2 =>
    sha1_norm at hs h0 h1 h2 h6 h7 h8 h9 h10 h12 h14 hM0 hM4 hM8 hM12 hM16 hM24 hM32 hM40 hM48 hM56 hM64 hM72 hM80 hM88 hM96 hM116 hM120 hM124 hM144 hM152
    simp only [← ho.read_reg]
    sha1_norm [effect064, hs, h0, h1, h2, h6, h7, h8, h9, h10, h12, h14, hM0, hM4, hM8, hM12, hM16, hM24, hM32, hM40, hM48, hM56, hM64, hM72, hM80, hM88, hM96, hM116, hM120, hM124, hM144, hM152, leaSpec,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, read32_memStore64_low,
      extractLsb'_zero_eq_setWidth, memLoad_memStore]
    all_goals simp only [hA60]
    all_goals ac_rfl
  case f3 =>
    sha1_norm at hs h0 h1 h2 h6 h7 h8 h9 h10 h12 h14 hM0 hM4 hM8 hM12 hM16 hM24 hM32 hM40 hM48 hM56 hM64 hM72 hM80 hM88 hM96 hM116 hM120 hM124 hM144 hM152
    simp only [← ho.read_reg]
    sha1_norm [effect064, hs, h0, h1, h2, h6, h7, h8, h9, h10, h12, h14, hM0, hM4, hM8, hM12, hM16, hM24, hM32, hM40, hM48, hM56, hM64, hM72, hM80, hM88, hM96, hM116, hM120, hM124, hM144, hM152, leaSpec,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, read32_memStore64_low,
      extractLsb'_zero_eq_setWidth, memLoad_memStore]
    all_goals ac_rfl
  case f4 =>
    sha1_norm at hs h0 h1 h2 h6 h7 h8 h9 h10 h12 h14 hM0 hM4 hM8 hM12 hM16 hM24 hM32 hM40 hM48 hM56 hM64 hM72 hM80 hM88 hM96 hM116 hM120 hM124 hM144 hM152
    simp only [← ho.read_reg]
    sha1_norm [effect064, hs, h0, h1, h2, h6, h7, h8, h9, h10, h12, h14, hM0, hM4, hM8, hM12, hM16, hM24, hM32, hM40, hM48, hM56, hM64, hM72, hM80, hM88, hM96, hM116, hM120, hM124, hM144, hM152, leaSpec,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, read32_memStore64_low,
      extractLsb'_zero_eq_setWidth, memLoad_memStore]
    all_goals ac_rfl
  case f5 =>
    exact (ha.read (by simp)).trans h6
  case f6 =>
    exact (ha.read (by simp)).trans h14
  case f7 =>
    sha1_norm at hs h0 h1 h2 h6 h7 h8 h9 h10 h12 h14 hM0 hM4 hM8 hM12 hM16 hM24 hM32 hM40 hM48 hM56 hM64 hM72 hM80 hM88 hM96 hM116 hM120 hM124 hM144 hM152
    simp only [← ho.read_reg]
    sha1_norm [effect064, hs, h0, h1, h2, h6, h7, h8, h9, h10, h12, h14, hM0, hM4, hM8, hM12, hM16, hM24, hM32, hM40, hM48, hM56, hM64, hM72, hM80, hM88, hM96, hM116, hM120, hM124, hM144, hM152, leaSpec,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, read32_memStore64_low,
      extractLsb'_zero_eq_setWidth, memLoad_memStore]
    all_goals simp only [hW60]
    all_goals ac_rfl
  case f8 =>
    exact (hmem 0 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM0
  case f9 =>
    exact (hmem 4 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM4
  case f10 =>
    exact (hmem 8 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM8
  case f11 =>
    exact (hmem 12 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM12
  case f12 =>
    exact (hmem 16 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM16
  case f13 =>
    exact (hmem 24 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM24
  case f14 =>
    exact (hmem 32 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM32
  case f15 =>
    exact (hmem 40 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM40
  case f16 =>
    exact (hmem 48 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM48
  case f17 =>
    exact (hmem 56 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM56
  case f18 =>
    exact (hmem 64 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM64
  case f19 =>
    exact (hmem 72 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM72
  case f20 =>
    exact (hmem 80 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM80
  case f21 =>
    exact (hmem 88 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM88
  case f22 =>
    exact (hmem 96 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM96
  case f23 =>
    sha1_norm at hs h0 h1 h2 h6 h7 h8 h9 h10 h12 h14 hM0 hM4 hM8 hM12 hM16 hM24 hM32 hM40 hM48 hM56 hM64 hM72 hM80 hM88 hM96 hM116 hM120 hM124 hM144 hM152
    simp only [← ho.read_mem]
    sha1_norm [effect064, hs, h0, h1, h2, h6, h7, h8, h9, h10, h12, h14, hM0, hM4, hM8, hM12, hM16, hM24, hM32, hM40, hM48, hM56, hM64, hM72, hM80, hM88, hM96, hM116, hM120, hM124, hM144, hM152, leaSpec,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, read32_memStore64_low,
      extractLsb'_zero_eq_setWidth, memLoad_memStore]
    all_goals ac_rfl
  case f24 =>
    exact (hmem 116 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM116
  case f25 =>
    exact (hmem 120 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM120
  case f26 =>
    exact (hmem 124 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM124
  case f27 =>
    exact (hmem 144 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM144
  case f28 =>
    exact (hmem 152 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM152

end Block064

open Block064 in
set_option maxRecDepth 10000 in
theorem segment064 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x10327a 0x1032bb cut064 cut065 := by
  have hout : ∀ d : Nat, d ≤ bytes064.length →
      0x10327a + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      simp only [bytes064, List.length_cons, List.length_nil] at hd <;>
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  apply Segment.of_block (fun _ _ _ _ ↦ effect064)
    (fun stack input H M ↦ block064 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64
      0x327a) bytes064, x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact he.rip.trans (by rfl)
  · intro stack input H M s t _ hf _ he
    exact effect064_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect064_words hf hw he

namespace Block065

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Spec.Program
open Standards.NIST.SHA1 Sha1.Proofs.Compress.Rounds


def bytes065 : List UInt8 :=
  [0x48, 0x8b, 0x7c, 0x24, 0x30, 0x4c, 0x8b, 0x6c, 0x24, 0x10, 0x41, 0x31, 0xfd, 0x44, 0x33, 0x6c, 0x24, 0x4, 0x4c, 0x8b, 0x4c, 0x24, 0x18, 0x45, 0x31, 0xcd, 0x41, 0xd1, 0xc5, 0x31, 0xd5, 0x44, 0x1, 0xe9, 0x1, 0xe9, 0x4c, 0x8b, 0x5c, 0x24, 0x60, 0x44, 0x31, 0xdf, 0x33, 0x7c, 0x24, 0x28, 0x44, 0x31, 0xff, 0xd1, 0xc7]

set_option maxHeartbeats 800000 in
def effect065 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq ((movR64M64Effect 0x1032bb 7 (.sib 4 none 0 (.d8 0x30)))) (movR64M64Effect 0x1032c0 13 (.sib 4 none 0 (.d8 0x10)))) (xorR32R32Effect 0x1032c5 3 13 7)) (xorR32M32Effect 0x1032c8 13 (.sib 4 none 0 (.d8 0x4)))) (movR64M64Effect 0x1032cd 9 (.sib 4 none 0 (.d8 0x18)))) (xorR32R32Effect 0x1032d2 3 13 9)) (rolR32Effect 0x1032d5 3 13 1)) (xorR32R32Effect 0x1032d8 2 5 2)) (addR32R32Effect 0x1032da 3 1 13)) (addR32R32Effect 0x1032dd 2 1 5)) (movR64M64Effect 0x1032df 11 (.sib 4 none 0 (.d8 0x60)))) (xorR32R32Effect 0x1032e4 3 7 11)) (xorR32M32LowEffect 0x1032e7 7 (.sib 4 none 0 (.d8 0x28)))) (xorR32R32Effect 0x1032eb 3 7 15)) (rolR32Effect 0x1032ee 2 7 1)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
theorem block065 [Bindings] (boundary : ReturnBoundary)
    (stack input : BitVec 64) (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes065.length → 0x1032bb + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x1032bb ∧ FrameData stack input M s ∧
        Write.AllHold s (cut065 stack input H M))
      (codeRange 0x1032bb bytes065) effect065 := by
  unfold bytes065 at hout ⊢
  sha1_run_begin (mov_r64_m64_effect_step 0x1032bb 0x48 (by unfold RexWPrefix; decide +kernel) 7 (.sib 4 none 0 (.d8 0x30)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_m64_effect_step 0x1032c0 0x4c (by unfold RexWPrefix; decide +kernel) 5 (.sib 4 none 0 (.d8 0x10)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x1032c5 0x41 0xfd (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_m32_effect_step 0x1032c8 0x44 (by unfold RexNoWPrefix; decide +kernel) 5 (.sib 4 none 0 (.d8 0x4)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_m64_effect_step 0x1032cd 0x4c (by unfold RexWPrefix; decide +kernel) 1 (.sib 4 none 0 (.d8 0x18)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x1032d2 0x45 0xcd (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_one_rex_effect_step 0x1032d5 0x41 0xc5 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x1032d8 0xd5 (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x1032da 0x44 0xe9 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x1032dd 0xe9 (by decide +kernel))
  sha1_run_then (mov_r64_m64_effect_step 0x1032df 0x4c (by unfold RexWPrefix; decide +kernel) 3 (.sib 4 none 0 (.d8 0x60)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x1032e4 0x44 0xdf (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_m32_low_effect_step 0x1032e7 7 (.sib 4 none 0 (.d8 0x28)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x1032eb 0x44 0xff (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_one_effect_step 0x1032ee 0xc7 (by decide +kernel) (by decide +kernel))
  sha1_run_finish [effect065]

set_option maxRecDepth 10000 in
private theorem components065 (s : RamState) :
    ∀ c ∈ (effect065 s).components, c ∈ [.reg 1, .reg 5, .reg 7, .reg 9, .reg 11, .reg 13, .flags, .rip] := by
  unfold effect065
  iterate 14 apply components_seq_of
  all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
    [addR32R32Effect_components, movR64M64Effect_components, rolR32Effect_components, xorR32M32Effect_components, xorR32M32LowEffect_components, xorR32R32Effect_components, List.mem_cons, List.not_mem_nil,
      or_false, or_imp, forall_and, forall_eq]
  all_goals sha1_norm

set_option maxRecDepth 10000 in
theorem effect065_agrees {stack input : BitVec 64} {M : Vector (BitVec 32) 16}
    {s t : RamState} (hf : FrameData stack input M s) (he : (effect065 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have ha := he.agrees.mono (components065 s)
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all (config := {decide := true, implicitDefEqProofs := false}) only
      [scratchComponents, x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hCov.elim
      | exact scratchComponents_stack (Or.inl (by decide +kernel)) hCov

set_option maxRecDepth 10000 in
private theorem full065 (s : RamState) : ∀ w ∈ (effect065 s).writes, w.Full := by
  apply Effect.Local.full
  unfold effect065
  repeat' first | (solve | x86_local) | apply Effect.Local.seq

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
theorem effect065_words {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (hw : Write.AllHold s (cut065 stack input H M))
    (he : (effect065 s).Holds s t) : Write.AllHold t (cut066 stack input H M) := by
  have ho := he.obsAfter (full065 s) true
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have ha := he.agrees.mono (components065 s)
  simp only [cut065, Write.AllHold] at hw
  obtain ⟨h0, h1, h2, h3, h5, h6, h14, h15, hM0, hM4, hM8, hM12, hM16, hM24, hM32, hM40, hM48, hM56, hM64, hM72, hM80, hM88, hM96, hM104, hM116, hM120, hM124, hM144, hM152⟩ := hw
  have hM48wide : ((Operand.mem (stack + 48) : Operand 64).read s).setWidth 32 =
      scheduleWord M 47 :=
    (read32_of_read64_low (s := s) (a := stack + 48)
      (v := (Operand.mem (stack + 48) : Operand 64).read s) rfl).symm.trans hM48
  have hM16wide : ((Operand.mem (stack + 16) : Operand 64).read s).setWidth 32 =
      scheduleWord M 45 :=
    (read32_of_read64_low (s := s) (a := stack + 16)
      (v := (Operand.mem (stack + 16) : Operand 64).read s) rfl).symm.trans hM16
  have hM24wide : ((Operand.mem (stack + 24) : Operand 64).read s).setWidth 32 =
      scheduleWord M 58 :=
    (read32_of_read64_low (s := s) (a := stack + 24)
      (v := (Operand.mem (stack + 24) : Operand 64).read s) rfl).symm.trans hM24
  have hM96wide : ((Operand.mem (stack + 96) : Operand 64).read s).setWidth 32 =
      scheduleWord M 49 :=
    (read32_of_read64_low (s := s) (a := stack + 96)
      (v := (Operand.mem (stack + 96) : Operand 64).read s) rfl).symm.trans hM96
  have hW63 : scheduleWord M 63 =
      (scheduleWord M 60 ^^^ scheduleWord M 55 ^^^
        scheduleWord M 49 ^^^ scheduleWord M 47).rotateLeft 1 := by
    change scheduleWord M (⟨63, by decide +kernel⟩ : Fin 80) = _
    rw [scheduleWord_recurrence M ⟨63, by decide +kernel⟩ (by decide +kernel),
      sha1Rotl_eq_rotateLeft 1 _ (by decide +kernel)]
    simp only [Nat.reduceSub]
    all_goals rfl
  have hW61 : scheduleWord M 61 =
      (scheduleWord M 58 ^^^ scheduleWord M 53 ^^^
        scheduleWord M 47 ^^^ scheduleWord M 45).rotateLeft 1 := by
    change scheduleWord M (⟨61, by decide +kernel⟩ : Fin 80) = _
    rw [scheduleWord_recurrence M ⟨61, by decide +kernel⟩ (by decide +kernel),
      sha1Rotl_eq_rotateLeft 1 _ (by decide +kernel)]
    simp only [Nat.reduceSub]
    all_goals rfl
  simp only [cut066, Write.AllHold]
  refine ⟨?f0, ?f1, ?f2, ?f3, ?f4, ?f5, ?f6, ?f7, ?f8, ?f9, ?f10, ?f11, ?f12, ?f13, ?f14, ?f15, ?f16, ?f17, ?f18, ?f19, ?f20, ?f21, ?f22, ?f23, ?f24, ?f25, ?f26, ?f27, ?f28⟩
  case f0 =>
    exact (ha.read (by simp)).trans h0
  case f1 =>
    sha1_norm at hM48wide hM16wide hM24wide hM96wide hs h0 h1 h2 h3 h5 h6 h14 h15 hM0 hM4 hM8 hM12 hM16 hM24 hM32 hM40 hM48 hM56 hM64 hM72 hM80 hM88 hM96 hM104 hM116 hM120 hM124 hM144 hM152
    simp only [← ho.read_reg]
    sha1_norm [effect065, hM96wide, hM24wide, hM16wide, hM48wide, hs, h0, h1, h2, h3, h5, h6, h14, h15, hM0, hM4, hM8, hM12, hM16, hM24, hM32, hM40, hM48, hM56, hM64, hM72, hM80, hM88, hM96, hM104, hM116, hM120, hM124, hM144, hM152, leaSpec,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, read32_memStore64_low,
      extractLsb'_zero_eq_setWidth, memLoad_memStore]
    all_goals simp only [hW61]
    all_goals ac_rfl
  case f2 =>
    exact (ha.read (by simp)).trans h2
  case f3 =>
    exact (ha.read (by simp)).trans h3
  case f4 =>
    exact (ha.read (by simp)).trans h6
  case f5 =>
    sha1_norm at hM48wide hM16wide hM24wide hM96wide hs h0 h1 h2 h3 h5 h6 h14 h15 hM0 hM4 hM8 hM12 hM16 hM24 hM32 hM40 hM48 hM56 hM64 hM72 hM80 hM88 hM96 hM104 hM116 hM120 hM124 hM144 hM152
    simp only [← ho.read_reg]
    sha1_norm [effect065, hM96wide, hM24wide, hM16wide, hM48wide, hs, h0, h1, h2, h3, h5, h6, h14, h15, hM0, hM4, hM8, hM12, hM16, hM24, hM32, hM40, hM48, hM56, hM64, hM72, hM80, hM88, hM96, hM104, hM116, hM120, hM124, hM144, hM152, leaSpec,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, read32_memStore64_low,
      extractLsb'_zero_eq_setWidth, memLoad_memStore]
    all_goals simp only [hW63]
    all_goals ac_rfl
  case f6 =>
    sha1_norm at hM48wide hM16wide hM24wide hM96wide hs h0 h1 h2 h3 h5 h6 h14 h15 hM0 hM4 hM8 hM12 hM16 hM24 hM32 hM40 hM48 hM56 hM64 hM72 hM80 hM88 hM96 hM104 hM116 hM120 hM124 hM144 hM152
    simp only [← ho.read_reg]
    sha1_norm [effect065, hM96wide, hM24wide, hM16wide, hM48wide, hs, h0, h1, h2, h3, h5, h6, h14, h15, hM0, hM4, hM8, hM12, hM16, hM24, hM32, hM40, hM48, hM56, hM64, hM72, hM80, hM88, hM96, hM104, hM116, hM120, hM124, hM144, hM152, leaSpec,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, read32_memStore64_low,
      extractLsb'_zero_eq_setWidth, memLoad_memStore]
    all_goals ac_rfl
  case f7 =>
    sha1_norm at hM48wide hM16wide hM24wide hM96wide hs h0 h1 h2 h3 h5 h6 h14 h15 hM0 hM4 hM8 hM12 hM16 hM24 hM32 hM40 hM48 hM56 hM64 hM72 hM80 hM88 hM96 hM104 hM116 hM120 hM124 hM144 hM152
    simp only [← ho.read_reg]
    sha1_norm [effect065, hM96wide, hM24wide, hM16wide, hM48wide, hs, h0, h1, h2, h3, h5, h6, h14, h15, hM0, hM4, hM8, hM12, hM16, hM24, hM32, hM40, hM48, hM56, hM64, hM72, hM80, hM88, hM96, hM104, hM116, hM120, hM124, hM144, hM152, leaSpec,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, read32_memStore64_low,
      extractLsb'_zero_eq_setWidth, memLoad_memStore]
    all_goals ac_rfl
  case f8 =>
    sha1_norm at hM48wide hM16wide hM24wide hM96wide hs h0 h1 h2 h3 h5 h6 h14 h15 hM0 hM4 hM8 hM12 hM16 hM24 hM32 hM40 hM48 hM56 hM64 hM72 hM80 hM88 hM96 hM104 hM116 hM120 hM124 hM144 hM152
    simp only [← ho.read_reg]
    sha1_norm [effect065, hM96wide, hM24wide, hM16wide, hM48wide, hs, h0, h1, h2, h3, h5, h6, h14, h15, hM0, hM4, hM8, hM12, hM16, hM24, hM32, hM40, hM48, hM56, hM64, hM72, hM80, hM88, hM96, hM104, hM116, hM120, hM124, hM144, hM152, leaSpec,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, read32_memStore64_low,
      extractLsb'_zero_eq_setWidth, memLoad_memStore]
    all_goals simp only [hW61]
    all_goals ac_rfl
  case f9 =>
    exact (ha.read (by simp)).trans h14
  case f10 =>
    exact (ha.read (by simp)).trans h15
  case f11 =>
    apply Eq.trans _ hM0
    apply memLoad_congr
    intro i hi
    apply congrArg (fun b : Option UInt8 ↦ b.getD 0)
    apply ha.byte
    intro c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact hCov.elim
  case f12 =>
    apply Eq.trans _ hM4
    apply memLoad_congr
    intro i hi
    apply congrArg (fun b : Option UInt8 ↦ b.getD 0)
    apply ha.byte
    intro c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact hCov.elim
  case f13 =>
    apply Eq.trans _ hM8
    apply memLoad_congr
    intro i hi
    apply congrArg (fun b : Option UInt8 ↦ b.getD 0)
    apply ha.byte
    intro c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact hCov.elim
  case f14 =>
    apply Eq.trans _ hM12
    apply memLoad_congr
    intro i hi
    apply congrArg (fun b : Option UInt8 ↦ b.getD 0)
    apply ha.byte
    intro c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact hCov.elim
  case f15 =>
    apply Eq.trans _ hM24
    apply memLoad_congr
    intro i hi
    apply congrArg (fun b : Option UInt8 ↦ b.getD 0)
    apply ha.byte
    intro c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact hCov.elim
  case f16 =>
    apply Eq.trans _ hM32
    apply memLoad_congr
    intro i hi
    apply congrArg (fun b : Option UInt8 ↦ b.getD 0)
    apply ha.byte
    intro c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact hCov.elim
  case f17 =>
    apply Eq.trans _ hM40
    apply memLoad_congr
    intro i hi
    apply congrArg (fun b : Option UInt8 ↦ b.getD 0)
    apply ha.byte
    intro c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact hCov.elim
  case f18 =>
    apply Eq.trans _ hM56
    apply memLoad_congr
    intro i hi
    apply congrArg (fun b : Option UInt8 ↦ b.getD 0)
    apply ha.byte
    intro c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact hCov.elim
  case f19 =>
    apply Eq.trans _ hM64
    apply memLoad_congr
    intro i hi
    apply congrArg (fun b : Option UInt8 ↦ b.getD 0)
    apply ha.byte
    intro c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact hCov.elim
  case f20 =>
    apply Eq.trans _ hM72
    apply memLoad_congr
    intro i hi
    apply congrArg (fun b : Option UInt8 ↦ b.getD 0)
    apply ha.byte
    intro c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact hCov.elim
  case f21 =>
    apply Eq.trans _ hM80
    apply memLoad_congr
    intro i hi
    apply congrArg (fun b : Option UInt8 ↦ b.getD 0)
    apply ha.byte
    intro c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact hCov.elim
  case f22 =>
    apply Eq.trans _ hM88
    apply memLoad_congr
    intro i hi
    apply congrArg (fun b : Option UInt8 ↦ b.getD 0)
    apply ha.byte
    intro c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact hCov.elim
  case f23 =>
    apply Eq.trans _ hM104
    apply memLoad_congr
    intro i hi
    apply congrArg (fun b : Option UInt8 ↦ b.getD 0)
    apply ha.byte
    intro c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact hCov.elim
  case f24 =>
    apply Eq.trans _ hM116
    apply memLoad_congr
    intro i hi
    apply congrArg (fun b : Option UInt8 ↦ b.getD 0)
    apply ha.byte
    intro c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact hCov.elim
  case f25 =>
    apply Eq.trans _ hM120
    apply memLoad_congr
    intro i hi
    apply congrArg (fun b : Option UInt8 ↦ b.getD 0)
    apply ha.byte
    intro c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact hCov.elim
  case f26 =>
    apply Eq.trans _ hM124
    apply memLoad_congr
    intro i hi
    apply congrArg (fun b : Option UInt8 ↦ b.getD 0)
    apply ha.byte
    intro c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact hCov.elim
  case f27 =>
    apply Eq.trans _ hM144
    apply memLoad_congr
    intro i hi
    apply congrArg (fun b : Option UInt8 ↦ b.getD 0)
    apply ha.byte
    intro c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact hCov.elim
  case f28 =>
    apply Eq.trans _ hM152
    apply memLoad_congr
    intro i hi
    apply congrArg (fun b : Option UInt8 ↦ b.getD 0)
    apply ha.byte
    intro c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact hCov.elim

end Block065

open Block065 in
set_option maxRecDepth 10000 in
theorem segment065 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x1032bb 0x1032f0 cut065 cut066 := by
  have hout : ∀ d : Nat, d ≤ bytes065.length →
      0x1032bb + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      simp only [bytes065, List.length_cons, List.length_nil] at hd <;>
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  apply Segment.of_block (fun _ _ _ _ ↦ effect065)
    (fun stack input H M ↦ block065 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64
      0x32bb) bytes065, x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact he.rip.trans (by rfl)
  · intro stack input H M s t _ hf _ he
    exact effect065_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect065_words hf hw he

namespace Block066

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Spec.Program
open Standards.NIST.SHA1 Sha1.Proofs.Compress.Rounds


def bytes066 : List UInt8 :=
  [0x49, 0x89, 0xf8, 0x89, 0xc7, 0xc1, 0xc7, 0x5, 0xc1, 0xc2, 0x1e, 0x1, 0xf9, 0x81, 0xc1, 0xd6, 0xc1, 0x62, 0xca, 0x89, 0xcf, 0xc1, 0xc7, 0x5, 0x45, 0x8d, 0x14, 0x30, 0x4c, 0x89, 0xc5, 0x4c, 0x89, 0x44, 0x24, 0x30, 0x31, 0xd6, 0x31, 0xc6, 0x3, 0x74, 0x24, 0x68, 0x1, 0xfe, 0x81, 0xc6, 0xd6, 0xc1, 0x62, 0xca]

set_option maxHeartbeats 800000 in
def effect066 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq ((movR64R64Effect 0x1032f0 8 7)) (movR32R32Effect 0x1032f3 2 7 0)) (rolR32Effect 0x1032f5 3 7 5)) (rolR32Effect 0x1032f8 3 2 30)) (addR32R32Effect 0x1032fb 2 1 7)) (addR32Imm32Effect 0x1032fd 6 1 0xca62c1d6)) (movR32R32Effect 0x103303 2 7 1)) (rolR32Effect 0x103305 3 7 5)) (leaR32Effect 0x103308 4 10 (.sib 8 (some 6) 0 .none))) (movR64R64Effect 0x10330c 5 8)) (movM64R64Effect 0x10330f 8 (.sib 4 none 0 (.d8 0x30)))) (xorR32R32Effect 0x103314 2 6 2)) (xorR32R32Effect 0x103316 2 6 0)) (addR32M32Effect 0x103318 4 6 (.sib 4 none 0 (.d8 0x68)))) (addR32R32Effect 0x10331c 2 6 7)) (addR32Imm32Effect 0x10331e 6 6 0xca62c1d6)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
theorem block066 [Bindings] (boundary : ReturnBoundary)
    (stack input : BitVec 64) (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes066.length → 0x1032f0 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x1032f0 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut066 stack input H M))
      (codeRange 0x1032f0 bytes066) effect066 := by
  unfold bytes066 at hout ⊢
  sha1_run_begin (mov_r64_r64_effect_step 0x1032f0 0x49 0xf8 (by unfold RexWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_effect_step 0x1032f3 0xc7 (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x1032f5 0xc7 0x5 (by decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x1032f8 0xc2 0x1e (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x1032fb 0xf9 (by decide +kernel))
  sha1_run_then (add_r32_imm32_effect_step 0x1032fd 0xc1 0xca62c1d6 (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_effect_step 0x103303 0xcf (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x103305 0xc7 0x5 (by decide +kernel) (by decide +kernel))
  sha1_run_then (lea_r32_rex_effect_step 0x103308 0x45 (by unfold RexNoWPrefix; decide +kernel) 2 (.sib 8 (some 6) 0 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_r64_effect_step 0x10330c 0x4c 0xc5 (by unfold RexWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step 0x10330f 0x4c (by unfold RexWPrefix; decide +kernel) 0 (.sib 4 none 0 (.d8 0x30)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x103314 0xd6 (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x103316 0xc6 (by decide +kernel))
  sha1_run_then (add_r32_m32_effect_step 0x103318 6 (.sib 4 none 0 (.d8 0x68)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x10331c 0xfe (by decide +kernel))
  sha1_run_then (add_r32_imm32_effect_step 0x10331e 0xc6 0xca62c1d6 (by decide +kernel) (by decide +kernel))
  sha1_run_finish [effect066]

set_option maxRecDepth 10000 in
private theorem components066 (s : RamState) :
    ∀ c ∈ (effect066 s).components, c ∈ [.mem ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 48) 8, .reg 1, .reg 2, .reg 5, .reg 6, .reg 7, .reg 8, .reg 10, .flags, .rip] := by
  unfold effect066
  iterate 15 apply components_seq_of
  all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
    [addR32Imm32Effect_components, addR32M32Effect_components, addR32R32Effect_components, leaR32Effect_components, movM64R64Effect_components, movR32R32Effect_components, movR64R64Effect_components, rolR32Effect_components, xorR32R32Effect_components, List.mem_cons, List.not_mem_nil,
      or_false, or_imp, forall_and, forall_eq, or_true]
  all_goals sha1_norm

set_option maxRecDepth 10000 in
theorem effect066_agrees {stack input : BitVec 64} {M : Vector (BitVec 32) 16}
    {s t : RamState} (hf : FrameData stack input M s) (he : (effect066 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have ha := he.agrees.mono (components066 s)
  rw [hs] at ha
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all (config := {decide := true, implicitDefEqProofs := false}) only
      [Component.isMem, scratchComponents, x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hCov.elim
      | exact scratchComponents_stack (Or.inl (by decide +kernel)) hCov

set_option maxRecDepth 10000 in
private theorem full066 (s : RamState) : ∀ w ∈ (effect066 s).writes, w.Full := by
  apply Effect.Local.full
  unfold effect066
  repeat' first | (solve | x86_local) | apply Effect.Local.seq

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
theorem effect066_words {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (hw : Write.AllHold s (cut066 stack input H M))
    (he : (effect066 s).Holds s t) : Write.AllHold t (cut067 stack input H M) := by
  have ho := he.obsAfter (full066 s) true
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have ha := he.agrees.mono (components066 s)
  rw [hs] at ha
  simp only [cut066, Write.AllHold] at hw
  obtain ⟨h0, h1, h2, h3, h6, h7, h9, h11, h13, h14, h15, hM0, hM4, hM8, hM12, hM24, hM32, hM40, hM56, hM64, hM72, hM80, hM88, hM104, hM116, hM120, hM124, hM144, hM152⟩ := hw
  have hmem {width : Nat} (off : BitVec 64)
      (hb : OffsetsApart 48 8 off (width / 8)) (hz : 8 + width / 8 < 2 ^ 64) :
      (Operand.mem (stack + off) : Operand width).read t =
      (Operand.mem (stack + off) : Operand width).read s := by
    apply memLoad_congr
    intro i hi
    apply congrArg (fun b : Option UInt8 ↦ b.getD 0)
    apply ha.byte
    intro c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨j, hj, heq⟩ := hCov
      exact hb.ne stack hj hi hz heq.symm
    all_goals exact hCov.elim
  have hA63 := workingAfter_step_a_values M H 58 (by decide +kernel)
  simp (config := {decide := true}) only [Nat.reduceAdd, f, K, Parity, ite_false] at hA63
  have hT62 : (⟨62, by decide +kernel⟩ : Fin 80) = 62 := by decide +kernel
  simp only [hT62] at hA63
  sha1_norm at hA63
  have hA62 := workingAfter_step_a_values M H 57 (by decide +kernel)
  simp (config := {decide := true}) only [Nat.reduceAdd, f, K, Parity, ite_false] at hA62
  have hT61 : (⟨61, by decide +kernel⟩ : Fin 80) = 61 := by decide +kernel
  simp only [hT61] at hA62
  sha1_norm at hA62
  simp only [cut067, Write.AllHold]
  refine ⟨?f0, ?f1, ?f2, ?f3, ?f4, ?f5, ?f6, ?f7, ?f8, ?f9, ?f10, ?f11, ?f12, ?f13, ?f14, ?f15, ?f16, ?f17, ?f18, ?f19, ?f20, ?f21, ?f22, ?f23, ?f24, ?f25, ?f26, ?f27, ?f28, ?f29⟩
  case f0 =>
    exact (ha.read (by simp)).trans h0
  case f1 =>
    sha1_norm at hs h0 h1 h2 h3 h6 h7 h9 h11 h13 h14 h15 hM0 hM4 hM8 hM12 hM24 hM32 hM40 hM56 hM64 hM72 hM80 hM88 hM104 hM116 hM120 hM124 hM144 hM152
    simp only [← ho.read_reg]
    sha1_norm [effect066, hs, h0, h1, h2, h3, h6, h7, h9, h11, h13, h14, h15, hM0, hM4, hM8, hM12, hM24, hM32, hM40, hM56, hM64, hM72, hM80, hM88, hM104, hM116, hM120, hM124, hM144, hM152, leaSpec,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, read32_memStore64_low,
      extractLsb'_zero_eq_setWidth, memLoad_memStore]
    all_goals simp only [hA62]
    all_goals ac_rfl
  case f2 =>
    sha1_norm at hs h0 h1 h2 h3 h6 h7 h9 h11 h13 h14 h15 hM0 hM4 hM8 hM12 hM24 hM32 hM40 hM56 hM64 hM72 hM80 hM88 hM104 hM116 hM120 hM124 hM144 hM152
    simp only [← ho.read_reg]
    sha1_norm [effect066, hs, h0, h1, h2, h3, h6, h7, h9, h11, h13, h14, h15, hM0, hM4, hM8, hM12, hM24, hM32, hM40, hM56, hM64, hM72, hM80, hM88, hM104, hM116, hM120, hM124, hM144, hM152, leaSpec,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, read32_memStore64_low,
      extractLsb'_zero_eq_setWidth, memLoad_memStore]
    all_goals ac_rfl
  case f3 =>
    exact (ha.read (by simp)).trans h3
  case f4 =>
    sha1_norm at hs h0 h1 h2 h3 h6 h7 h9 h11 h13 h14 h15 hM0 hM4 hM8 hM12 hM24 hM32 hM40 hM56 hM64 hM72 hM80 hM88 hM104 hM116 hM120 hM124 hM144 hM152
    simp only [← ho.read_reg]
    sha1_norm [effect066, hs, h0, h1, h2, h3, h6, h7, h9, h11, h13, h14, h15, hM0, hM4, hM8, hM12, hM24, hM32, hM40, hM56, hM64, hM72, hM80, hM88, hM104, hM116, hM120, hM124, hM144, hM152, leaSpec,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, read32_memStore64_low,
      extractLsb'_zero_eq_setWidth, memLoad_memStore]
    all_goals ac_rfl
  case f5 =>
    sha1_norm at hs h0 h1 h2 h3 h6 h7 h9 h11 h13 h14 h15 hM0 hM4 hM8 hM12 hM24 hM32 hM40 hM56 hM64 hM72 hM80 hM88 hM104 hM116 hM120 hM124 hM144 hM152
    simp only [← ho.read_reg]
    sha1_norm [effect066, hs, h0, h1, h2, h3, h6, h7, h9, h11, h13, h14, h15, hM0, hM4, hM8, hM12, hM24, hM32, hM40, hM56, hM64, hM72, hM80, hM88, hM104, hM116, hM120, hM124, hM144, hM152, leaSpec,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, read32_memStore64_low,
      extractLsb'_zero_eq_setWidth, memLoad_memStore]
    all_goals simp only [hA63, hA62]
    all_goals ac_rfl
  case f6 =>
    exact (ha.read (by simp)).trans h9
  case f7 =>
    sha1_norm at hs h0 h1 h2 h3 h6 h7 h9 h11 h13 h14 h15 hM0 hM4 hM8 hM12 hM24 hM32 hM40 hM56 hM64 hM72 hM80 hM88 hM104 hM116 hM120 hM124 hM144 hM152
    simp only [← ho.read_reg]
    sha1_norm [effect066, hs, h0, h1, h2, h3, h6, h7, h9, h11, h13, h14, h15, hM0, hM4, hM8, hM12, hM24, hM32, hM40, hM56, hM64, hM72, hM80, hM88, hM104, hM116, hM120, hM124, hM144, hM152, leaSpec,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, read32_memStore64_low,
      extractLsb'_zero_eq_setWidth, memLoad_memStore]
    all_goals ac_rfl
  case f8 =>
    exact (ha.read (by simp)).trans h11
  case f9 =>
    exact (ha.read (by simp)).trans h13
  case f10 =>
    exact (ha.read (by simp)).trans h14
  case f11 =>
    exact (ha.read (by simp)).trans h15
  case f12 =>
    exact (hmem 0 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM0
  case f13 =>
    exact (hmem 4 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM4
  case f14 =>
    exact (hmem 8 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM8
  case f15 =>
    exact (hmem 12 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM12
  case f16 =>
    exact (hmem 24 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM24
  case f17 =>
    exact (hmem 32 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM32
  case f18 =>
    exact (hmem 40 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM40
  case f19 =>
    sha1_norm at hs h0 h1 h2 h3 h6 h7 h9 h11 h13 h14 h15 hM0 hM4 hM8 hM12 hM24 hM32 hM40 hM56 hM64 hM72 hM80 hM88 hM104 hM116 hM120 hM124 hM144 hM152
    simp only [← ho.read_mem]
    sha1_norm [effect066, hs, h0, h1, h2, h3, h6, h7, h9, h11, h13, h14, h15, hM0, hM4, hM8, hM12, hM24, hM32, hM40, hM56, hM64, hM72, hM80, hM88, hM104, hM116, hM120, hM124, hM144, hM152, leaSpec,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, read32_memStore64_low,
      extractLsb'_zero_eq_setWidth, memLoad_memStore]
    all_goals ac_rfl
  case f20 =>
    exact (hmem 56 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM56
  case f21 =>
    exact (hmem 64 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM64
  case f22 =>
    exact (hmem 72 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM72
  case f23 =>
    exact (hmem 80 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM80
  case f24 =>
    exact (hmem 88 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM88
  case f25 =>
    exact (hmem 116 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM116
  case f26 =>
    exact (hmem 120 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM120
  case f27 =>
    exact (hmem 124 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM124
  case f28 =>
    exact (hmem 144 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM144
  case f29 =>
    exact (hmem 152 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM152

end Block066

open Block066 in
set_option maxRecDepth 10000 in
theorem segment066 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x1032f0 0x103324 cut066 cut067 := by
  have hout : ∀ d : Nat, d ≤ bytes066.length →
      0x1032f0 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      simp only [bytes066, List.length_cons, List.length_nil] at hd <;>
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  apply Segment.of_block (fun _ _ _ _ ↦ effect066)
    (fun stack input H M ↦ block066 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64
      0x32f0) bytes066, x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact he.rip.trans (by rfl)
  · intro stack input H M s t _ hf _ he
    exact effect066_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect066_words hf hw he

namespace Block067

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Spec.Program
open Standards.NIST.SHA1
open Sha1.Proofs.Compress.Rounds



def bytes067 : List UInt8 :=
  [0xc1, 0xc0, 0x1e, 0x41, 0x89, 0xc0, 0x41, 0x31, 0xd0, 0x41, 0x31, 0xc8, 0x45, 0x01, 0xd0, 0xc1, 0xc1, 0x1e, 0x48, 0x8b, 0x7c, 0x24, 0x58, 0x44, 0x8b, 0x64, 0x24, 0x0c, 0x41, 0x31, 0xfc, 0x31, 0xdf, 0x44, 0x31, 0xcf, 0x31, 0xef, 0xd1, 0xc7, 0x49, 0x89, 0xf9, 0x48, 0x89, 0x7c, 0x24, 0x58, 0x89, 0xf7]

def effect067 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq ((rolR32Effect 0x103324 3 0 30)) (movR32R32Effect 0x103327 3 8 0)) (xorR32R32Effect 0x10332a 3 8 2)) (xorR32R32Effect 0x10332d 3 8 1)) (addR32R32Effect 0x103330 3 8 10)) (rolR32Effect 0x103333 3 1 30)) (movR64M64Effect 0x103336 7 (.sib 4 none 0 (.d8 0x58)))) (movR32M32Effect 0x10333b 12 (.sib 4 none 0 (.d8 0xc)))) (xorR32R32Effect 0x103340 3 12 7)) (xorR32R32Effect 0x103343 2 7 3)) (xorR32R32Effect 0x103345 3 7 9)) (xorR32R32Effect 0x103348 2 7 5)) (rolR32Effect 0x10334a 2 7 1)) (movR64R64Effect 0x10334c 9 7)) (movM64R64Effect 0x10334f 7 (.sib 4 none 0 (.d8 0x58)))) (movR32R32Effect 0x103354 2 7 6)

set_option maxHeartbeats 800000 in
theorem block067 [Bindings] (boundary : ReturnBoundary) (stack input : BitVec 64)
    (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes067.length →
      0x103324 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x103324 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut067 stack input H M))
      (codeRange 0x103324 bytes067) effect067 := by
  have hRaw : AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x103324 ∧ FrameData stack input M s)
      (codeRange 0x103324 bytes067) effect067 := by
    unfold bytes067 at hout ⊢
    sha1_run_begin (rol_r32_imm8_effect_step 0x103324 0xc0 0x1e (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (mov_r32_r32_rex_effect_step 0x103327 0x41 0xc0 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (xor_r32_r32_rex_effect_step 0x10332a 0x41 0xd0 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (xor_r32_r32_rex_effect_step 0x10332d 0x41 0xc8 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (add_r32_r32_rex_effect_step 0x103330 0x45 0xd0 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (rol_r32_imm8_effect_step 0x103333 0xc1 0x1e (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (mov_r64_m64_effect_step 0x103336 0x48 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) 7 (.sib 4 none 0 (.d8 0x58)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (mov_r32_m32_effect_step 0x10333b 0x44 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) 4 (.sib 4 none 0 (.d8 0xc)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (xor_r32_r32_rex_effect_step 0x103340 0x41 0xfc (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (xor_r32_r32_effect_step 0x103343 0xdf (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (xor_r32_r32_rex_effect_step 0x103345 0x44 0xcf (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (xor_r32_r32_effect_step 0x103348 0xef (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (rol_r32_one_effect_step 0x10334a 0xc7 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (mov_r64_r64_effect_step 0x10334c 0x49 0xf9 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step 0x10334f 0x48 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) 7 (.sib 4 none 0 (.d8 0x58)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (mov_r32_r32_effect_step 0x103354 0xf7 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_finish [effect067]
  intro s hr hc hp
  exact hRaw s hr hc ⟨hp.1, hp.2.1⟩

private def genericCut067 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), (A 61)⟩,
    ⟨(.reg 1 : Operand 32), (A 62)⟩,
    ⟨(.reg 2 : Operand 32), ((A 60)).rotateLeft 30⟩,
    ⟨(.reg 3 : Operand 32), (W 52)⟩,
    ⟨(.reg 5 : Operand 32), (W 63)⟩,
    ⟨(.reg 6 : Operand 32), (A 63)⟩,
    ⟨(.reg 9 : Operand 32), (W 58)⟩,
    ⟨(.reg 10 : Operand 32), ((W 63) + ((A 59)).rotateLeft 30)⟩,
    ⟨(.reg 11 : Operand 32), (W 49)⟩,
    ⟨(.reg 13 : Operand 32), (W 61)⟩,
    ⟨(.reg 14 : Operand 32), (W 56)⟩,
    ⟨(.reg 15 : Operand 32), (W 60)⟩,
    ⟨(.mem (stack + 0) : Operand 32), (W 57)⟩,
    ⟨(.mem (stack + 4) : Operand 32), (W 53)⟩,
    ⟨(.mem (stack + 8) : Operand 32), (W 52)⟩,
    ⟨(.mem (stack + 12) : Operand 32), (W 48)⟩,
    ⟨(.mem (stack + 24) : Operand 32), (W 58)⟩,
    ⟨(.mem (stack + 32) : Operand 32), (W 54)⟩,
    ⟨(.mem (stack + 40) : Operand 32), (W 55)⟩,
    ⟨(.mem (stack + 48) : Operand 32), (W 63)⟩,
    ⟨(.mem (stack + 56) : Operand 32), (W 51)⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), (W 62)⟩,
    ⟨(.mem (stack + 80) : Operand 32), (W 59)⟩,
    ⟨(.mem (stack + 88) : Operand 32), (W 50)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

private def genericCut068 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), ((A 61)).rotateLeft 30⟩,
    ⟨(.reg 1 : Operand 32), ((A 62)).rotateLeft 30⟩,
    ⟨(.reg 2 : Operand 32), ((A 60)).rotateLeft 30⟩,
    ⟨(.reg 6 : Operand 32), (A 63)⟩,
    ⟨(.reg 7 : Operand 32), (A 63)⟩,
    ⟨(.reg 8 : Operand 32), ((W 63) + ((A 59)).rotateLeft 30 + ((A 62) ^^^ ((A 60)).rotateLeft 30 ^^^ ((A 61)).rotateLeft 30))⟩,
    ⟨(.reg 9 : Operand 32), (W 66)⟩,
    ⟨(.reg 11 : Operand 32), (W 49)⟩,
    ⟨(.reg 12 : Operand 32), ((W 48) ^^^ (W 50))⟩,
    ⟨(.reg 13 : Operand 32), (W 61)⟩,
    ⟨(.reg 14 : Operand 32), (W 56)⟩,
    ⟨(.reg 15 : Operand 32), (W 60)⟩,
    ⟨(.mem (stack + 0) : Operand 32), (W 57)⟩,
    ⟨(.mem (stack + 4) : Operand 32), (W 53)⟩,
    ⟨(.mem (stack + 8) : Operand 32), (W 52)⟩,
    ⟨(.mem (stack + 24) : Operand 32), (W 58)⟩,
    ⟨(.mem (stack + 32) : Operand 32), (W 54)⟩,
    ⟨(.mem (stack + 40) : Operand 32), (W 55)⟩,
    ⟨(.mem (stack + 48) : Operand 32), (W 63)⟩,
    ⟨(.mem (stack + 56) : Operand 32), (W 51)⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), (W 62)⟩,
    ⟨(.mem (stack + 80) : Operand 32), (W 59)⟩,
    ⟨(.mem (stack + 88) : Operand 32), (W 66)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

theorem effect067_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (he : (effect067 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hfoot : ∀ c ∈ (effect067 s).components, c ∈ [.mem ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 88) 8, .reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect067
    iterate 15 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [addR32R32Effect_components, movM64R64Effect_components, movR32M32Effect_components, movR32R32Effect_components, movR64M64Effect_components, movR64R64Effect_components, rolR32Effect_components, xorR32R32Effect_components, List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and, forall_eq, or_true]
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

theorem effect067_rip {s t : RamState}
    (he : (effect067 s).Holds s t) :
    t.RIP = 0x103356 := by
  exact he.rip.trans (by rfl)

section Words067
theorem effect067_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16}
    {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut067 stack input H M))
    (he : (effect067 s).Holds s t) :
    Write.AllHold t (cut068 stack input H M) := by
  have hfull : ∀ w ∈ (effect067 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect067
    repeat' first
      | solve | x86_local
      | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  sha1_norm at hs
  change Write.AllHold s
    (genericCut067 stack input H (fun n ↦ (workingAfter M H n).a) (scheduleWord M)) at hw
  simp only [genericCut067, Write.AllHold] at hw
  obtain ⟨h0, h1, h2, h3, h5, h6, h9, h10, h11, h13, h14, h15,
    hM0, hM4, hM8, hM12, hM24, hM32, hM40, hM48, hM56, hM64, hM72,
    hM80, hM88, hM116, hM120, hM124, hM144, hM152⟩ := hw
  sha1_norm at h0 h1 h2 h3 h5 h6 h9 h10 h11 h13 h14 h15
  sha1_norm at hM0 hM4 hM8 hM12 hM24 hM32 hM40 hM48 hM56 hM64 hM72 hM80 hM88
  sha1_norm at hM116 hM120 hM124 hM144 hM152
  simp only [Operand.read] at hM88
  change Write.AllHold t
    (genericCut068 stack input H (fun n ↦ (workingAfter M H n).a) (scheduleWord M))
  simp only [genericCut068, Write.AllHold, ← ho.read_reg, ← ho.read_mem]
  sha1_norm [leaSpec, effect067, hs, h0, h1, h2, h3, h5, h6, h9, h10, h11, h13, h14, h15,
    hM0, hM4, hM8, hM12, hM24, hM32, hM40, hM48, hM56, hM64, hM72, hM80, hM88,
    hM116, hM120, hM124, hM144, hM152]
  have hW66 : scheduleWord M 66 =
      (scheduleWord M 63 ^^^ scheduleWord M 58 ^^^ scheduleWord M 52 ^^^
        scheduleWord M 50).rotateLeft 1 := by
    change scheduleWord M (⟨66, by decide +kernel⟩ : Fin 80) = _
    rw [scheduleWord_recurrence M ⟨66, by decide +kernel⟩ (by decide +kernel),
      sha1Rotl_eq_rotateLeft 1 _ (by decide +kernel)]
    simp only [Nat.reduceSub]
    have h63 : (⟨63, by decide +kernel⟩ : Fin 80) = 63 := by decide +kernel
    have h58 : (⟨58, by decide +kernel⟩ : Fin 80) = 58 := by decide +kernel
    have h52 : (⟨52, by decide +kernel⟩ : Fin 80) = 52 := by decide +kernel
    have h50 : (⟨50, by decide +kernel⟩ : Fin 80) = 50 := by decide +kernel
    simp only [h63, h58, h52, h50]
  rw [hW66]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [Operand.read, memLoad_low32,
      read32_memStore64_low,
      X86Proofs.extractLsb'_zero_eq_setWidth,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
      BitVec.xor_assoc, BitVec.xor_comm, hM88]
  all_goals ac_rfl
end Words067

end Block067

open Block067 in
theorem segment067 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x103324 0x103356
      cut067 cut068 := by
  have hout : ∀ d : Nat, d ≤ bytes067.length →
      0x103324 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      simp only [bytes067, List.length_cons, List.length_nil] at hd <;>
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  apply Segment.of_block (fun _ _ _ _ => effect067)
    (fun stack input H M => block067 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64
      0x3324) bytes067,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect067_rip he
  · intro stack input H M s t _ hf _ he
    exact effect067_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect067_words hf hw he

namespace Block068

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Spec.Program
open Standards.NIST.SHA1
open Sha1.Proofs.Compress.Rounds



def bytes068 : List UInt8 :=
  [0xc1, 0xc7, 0x1e, 0x89, 0xfd, 0x31, 0xcd, 0x41, 0x01, 0xc9, 0x44, 0x89, 0x4c, 0x24, 0x10, 0x31, 0xc1, 0x31, 0xf1, 0xc1, 0xc6, 0x05, 0x44, 0x01, 0xc6, 0x81, 0xc6, 0xd6, 0xc1, 0x62, 0xca, 0x45, 0x31, 0xf4, 0x45, 0x31, 0xec, 0x41, 0xd1, 0xc4, 0x41, 0x89, 0xf0, 0x41, 0xc1, 0xc0, 0x05, 0x44, 0x01, 0xe2, 0x01, 0xca, 0x41, 0x8d, 0x0c, 0x10, 0x81, 0xc1, 0xd6, 0xc1, 0x62, 0xca]

def effect068 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq ((rolR32Effect 0x103356 3 7 30)) (movR32R32Effect 0x103359 2 5 7)) (xorR32R32Effect 0x10335b 2 5 1)) (addR32R32Effect 0x10335d 3 9 1)) (movM32R32Effect 0x103360 9 (.sib 4 none 0 (.d8 0x10)))) (xorR32R32Effect 0x103365 2 1 0)) (xorR32R32Effect 0x103367 2 1 6)) (rolR32Effect 0x103369 3 6 5)) (addR32R32Effect 0x10336c 3 6 8)) (addR32Imm32Effect 0x10336f 6 6 0xca62c1d6)) (xorR32R32Effect 0x103375 3 12 14)) (xorR32R32Effect 0x103378 3 12 13)) (rolR32Effect 0x10337b 3 12 1)) (movR32R32Effect 0x10337e 3 8 6)) (rolR32Effect 0x103381 4 8 5)) (addR32R32Effect 0x103385 3 2 12)) (addR32R32Effect 0x103388 2 2 1)) (leaR32Effect 0x10338a 4 1 (.sib 8 (some 2) 0 .none))) (addR32Imm32Effect 0x10338e 6 1 0xca62c1d6)

set_option maxHeartbeats 800000 in
theorem block068 [Bindings] (boundary : ReturnBoundary) (stack input : BitVec 64)
    (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes068.length →
      0x103356 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x103356 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut068 stack input H M))
      (codeRange 0x103356 bytes068) effect068 := by
  have hRaw : AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x103356 ∧ FrameData stack input M s)
      (codeRange 0x103356 bytes068) effect068 := by
    unfold bytes068 at hout ⊢
    sha1_run_begin (rol_r32_imm8_effect_step 0x103356 0xc7 0x1e (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (mov_r32_r32_effect_step 0x103359 0xfd (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (xor_r32_r32_effect_step 0x10335b 0xcd (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (add_r32_r32_rex_effect_step 0x10335d 0x41 0xc9 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m32_r32_effect_step 0x103360 0x44 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) 1 (.sib 4 none 0 (.d8 0x10)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (xor_r32_r32_effect_step 0x103365 0xc1 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (xor_r32_r32_effect_step 0x103367 0xf1 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (rol_r32_imm8_effect_step 0x103369 0xc6 0x5 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (add_r32_r32_rex_effect_step 0x10336c 0x44 0xc6 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (add_r32_imm32_effect_step 0x10336f 0xc6 0xca62c1d6 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (xor_r32_r32_rex_effect_step 0x103375 0x45 0xf4 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (xor_r32_r32_rex_effect_step 0x103378 0x45 0xec (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (rol_r32_one_rex_effect_step 0x10337b 0x41 0xc4 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (mov_r32_r32_rex_effect_step 0x10337e 0x41 0xf0 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (rol_r32_imm8_rex_effect_step 0x103381 0x41 0xc0 0x5 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (add_r32_r32_rex_effect_step 0x103385 0x44 0xe2 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (add_r32_r32_effect_step 0x103388 0xca (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (lea_r32_rex_effect_step 0x10338a 0x41 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) 1 (.sib 8 (some 2) 0 .none) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (add_r32_imm32_effect_step 0x10338e 0xc1 0xca62c1d6 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_finish [effect068]
  intro s hr hc hp
  exact hRaw s hr hc ⟨hp.1, hp.2.1⟩

private def genericCut068 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), ((A 61)).rotateLeft 30⟩,
    ⟨(.reg 1 : Operand 32), ((A 62)).rotateLeft 30⟩,
    ⟨(.reg 2 : Operand 32), ((A 60)).rotateLeft 30⟩,
    ⟨(.reg 6 : Operand 32), (A 63)⟩,
    ⟨(.reg 7 : Operand 32), (A 63)⟩,
    ⟨(.reg 8 : Operand 32), ((W 63) + ((A 59)).rotateLeft 30 + ((A 62) ^^^ ((A 60)).rotateLeft 30 ^^^ ((A 61)).rotateLeft 30))⟩,
    ⟨(.reg 9 : Operand 32), (W 66)⟩,
    ⟨(.reg 11 : Operand 32), (W 49)⟩,
    ⟨(.reg 12 : Operand 32), ((W 48) ^^^ (W 50))⟩,
    ⟨(.reg 13 : Operand 32), (W 61)⟩,
    ⟨(.reg 14 : Operand 32), (W 56)⟩,
    ⟨(.reg 15 : Operand 32), (W 60)⟩,
    ⟨(.mem (stack + 0) : Operand 32), (W 57)⟩,
    ⟨(.mem (stack + 4) : Operand 32), (W 53)⟩,
    ⟨(.mem (stack + 8) : Operand 32), (W 52)⟩,
    ⟨(.mem (stack + 24) : Operand 32), (W 58)⟩,
    ⟨(.mem (stack + 32) : Operand 32), (W 54)⟩,
    ⟨(.mem (stack + 40) : Operand 32), (W 55)⟩,
    ⟨(.mem (stack + 48) : Operand 32), (W 63)⟩,
    ⟨(.mem (stack + 56) : Operand 32), (W 51)⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), (W 62)⟩,
    ⟨(.mem (stack + 80) : Operand 32), (W 59)⟩,
    ⟨(.mem (stack + 88) : Operand 32), (W 66)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

private def genericCut069 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), ((A 61)).rotateLeft 30⟩,
    ⟨(.reg 1 : Operand 32), (A 65)⟩,
    ⟨(.reg 5 : Operand 32), (((A 62)).rotateLeft 30 ^^^ ((A 63)).rotateLeft 30)⟩,
    ⟨(.reg 6 : Operand 32), (A 64)⟩,
    ⟨(.reg 7 : Operand 32), ((A 63)).rotateLeft 30⟩,
    ⟨(.reg 11 : Operand 32), (W 49)⟩,
    ⟨(.reg 12 : Operand 32), (W 64)⟩,
    ⟨(.reg 13 : Operand 32), (W 61)⟩,
    ⟨(.reg 14 : Operand 32), (W 56)⟩,
    ⟨(.reg 15 : Operand 32), (W 60)⟩,
    ⟨(.mem (stack + 0) : Operand 32), (W 57)⟩,
    ⟨(.mem (stack + 4) : Operand 32), (W 53)⟩,
    ⟨(.mem (stack + 8) : Operand 32), (W 52)⟩,
    ⟨(.mem (stack + 16) : Operand 32), ((W 66) + ((A 62)).rotateLeft 30)⟩,
    ⟨(.mem (stack + 24) : Operand 32), (W 58)⟩,
    ⟨(.mem (stack + 32) : Operand 32), (W 54)⟩,
    ⟨(.mem (stack + 40) : Operand 32), (W 55)⟩,
    ⟨(.mem (stack + 48) : Operand 32), (W 63)⟩,
    ⟨(.mem (stack + 56) : Operand 32), (W 51)⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), (W 62)⟩,
    ⟨(.mem (stack + 80) : Operand 32), (W 59)⟩,
    ⟨(.mem (stack + 88) : Operand 32), (W 66)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

theorem effect068_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (he : (effect068 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hfoot : ∀ c ∈ (effect068 s).components, c ∈ [.mem ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 16) 4, .reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect068
    iterate 18 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [leaR32Effect_components, addR32Imm32Effect_components, addR32R32Effect_components, movM32R32Effect_components, movR32R32Effect_components, rolR32Effect_components, xorR32R32Effect_components, List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and, forall_eq, or_true]
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

theorem effect068_rip {s t : RamState}
    (he : (effect068 s).Holds s t) :
    t.RIP = 0x103394 := by
  exact he.rip.trans (by rfl)

section Words068

private theorem full068 (s : RamState) : ∀ w ∈ (effect068 s).writes, w.Full := by
  apply Effect.Local.full
  unfold effect068
  repeat' first | (solve | x86_local) | apply Effect.Local.seq

private theorem rawR1_068 {s t : RamState}
    (v0 v1 v2 v6 v8 v12 v13 v14 : BitVec 32)
    (h0 : (Operand.reg 0 : Operand 32).read s = v0)
    (h1 : (Operand.reg 1 : Operand 32).read s = v1)
    (h2 : (Operand.reg 2 : Operand 32).read s = v2)
    (h6 : (Operand.reg 6 : Operand 32).read s = v6)
    (h8 : (Operand.reg 8 : Operand 32).read s = v8)
    (h12 : (Operand.reg 12 : Operand 32).read s = v12)
    (h13 : (Operand.reg 13 : Operand 32).read s = v13)
    (h14 : (Operand.reg 14 : Operand 32).read s = v14)
    (he : (effect068 s).Holds s t) :
    (Operand.reg 1 : Operand 32).read t =
      (v6.rotateLeft 5 + v8 + 0xca62c1d6).rotateLeft 5 +
        (v2 + (v12 ^^^ v14 ^^^ v13).rotateLeft 1 + (v1 ^^^ v0 ^^^ v6)) +
        0xca62c1d6 := by
  have ho := he.obsAfter (full068 s) true
  sha1_norm at h0 h1 h2 h6 h8 h12 h13 h14
  simp only [← ho.read_reg]
  sha1_norm [leaSpec, effect068, h0,h1,h2,h6,h8,h12,h13,h14,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
    BitVec.shiftLeft_zero]
  all_goals ac_rfl

private theorem rawR5_068 {s t : RamState} (v1 v7 : BitVec 32)
    (h1 : (Operand.reg 1 : Operand 32).read s = v1)
    (h7 : (Operand.reg 7 : Operand 32).read s = v7)
    (he : (effect068 s).Holds s t) :
    (Operand.reg 5 : Operand 32).read t = v7.rotateLeft 30 ^^^ v1 := by
  have ho := he.obsAfter (full068 s) true
  sha1_norm at h1 h7
  simp only [← ho.read_reg]
  sha1_norm [leaSpec, effect068, h1,h7, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]

private theorem rawR6_068 {s t : RamState} (v6 v8 : BitVec 32)
    (h6 : (Operand.reg 6 : Operand 32).read s = v6)
    (h8 : (Operand.reg 8 : Operand 32).read s = v8)
    (he : (effect068 s).Holds s t) :
    (Operand.reg 6 : Operand 32).read t = v6.rotateLeft 5 + v8 + 0xca62c1d6 := by
  have ho := he.obsAfter (full068 s) true
  sha1_norm at h6 h8
  simp only [← ho.read_reg]
  sha1_norm [leaSpec, effect068, h6,h8, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
  all_goals ac_rfl

private theorem rawR7_068 {s t : RamState} (v7 : BitVec 32)
    (h7 : (Operand.reg 7 : Operand 32).read s = v7)
    (he : (effect068 s).Holds s t) :
    (Operand.reg 7 : Operand 32).read t = v7.rotateLeft 30 := by
  have ho := he.obsAfter (full068 s) true
  sha1_norm at h7
  simp only [← ho.read_reg]
  sha1_norm [leaSpec, effect068, h7, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]

private theorem rawR12_068 {s t : RamState} (v12 v13 v14 : BitVec 32)
    (h12 : (Operand.reg 12 : Operand 32).read s = v12)
    (h13 : (Operand.reg 13 : Operand 32).read s = v13)
    (h14 : (Operand.reg 14 : Operand 32).read s = v14)
    (he : (effect068 s).Holds s t) :
    (Operand.reg 12 : Operand 32).read t = (v12 ^^^ v14 ^^^ v13).rotateLeft 1 := by
  have ho := he.obsAfter (full068 s) true
  sha1_norm at h12 h13 h14
  simp only [← ho.read_reg]
  sha1_norm [leaSpec, effect068, h12,h13,h14,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]

private theorem rawM16_068 {s t : RamState} (stack : BitVec 64) (v1 v9 : BitVec 32)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (h1 : (Operand.reg 1 : Operand 32).read s = v1)
    (h9 : (Operand.reg 9 : Operand 32).read s = v9)
    (he : (effect068 s).Holds s t) :
    (Operand.mem (stack + 16) : Operand 32).read t = v9 + v1 := by
  have ho := he.obsAfter (full068 s) true
  sha1_norm at hs h1 h9
  simp only [← ho.read_mem]
  sha1_norm [leaSpec, effect068, hs,h1,h9,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]

private theorem cutTransport068 {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) {s t : RamState}
    (hWork64 : A 64 = (A 63).rotateLeft 5 +
      (A 62 ^^^ (A 61).rotateLeft 30 ^^^ (A 60).rotateLeft 30) +
      (A 59).rotateLeft 30 + 0xca62c1d6 + W 63)
    (hWork65 : A 65 = (A 64).rotateLeft 5 +
      (A 63 ^^^ (A 62).rotateLeft 30 ^^^ (A 61).rotateLeft 30) +
      (A 60).rotateLeft 30 + 0xca62c1d6 + W 64)
    (hW64 : W 64 = (W 61 ^^^ W 56 ^^^ W 50 ^^^ W 48).rotateLeft 1)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hw : Write.AllHold s (genericCut068 stack input H A W))
    (he : (effect068 s).Holds s t) :
    Write.AllHold t (genericCut069 stack input H A W) := by
  simp only [genericCut068, Write.AllHold] at hw
  obtain ⟨h0,h1,h2,h6,h7,h8,h9,h11,h12,h13,h14,h15,
    hM0,hM4,hM8,hM24,hM32,hM40,hM48,hM56,hM64,hM72,
    hM80,hM88,hM116,hM120,hM124,hM144,hM152⟩ := hw
  have hT : (A 63).rotateLeft 5 +
      (W 63 + (A 59).rotateLeft 30 +
        (A 62 ^^^ (A 60).rotateLeft 30 ^^^ (A 61).rotateLeft 30)) +
      0xca62c1d6 = A 64 := by
    rw [hWork64]
    ac_rfl
  have hW : ((W 48 ^^^ W 50) ^^^ W 56 ^^^ W 61).rotateLeft 1 = W 64 := by
    rw [hW64]
    apply congrArg (fun x : BitVec 32 ↦ x.rotateLeft 1)
    ac_rfl
  have hR1 := rawR1_068 ((A 61).rotateLeft 30) ((A 62).rotateLeft 30)
    ((A 60).rotateLeft 30) (A 63)
    (W 63 + (A 59).rotateLeft 30 +
      (A 62 ^^^ (A 60).rotateLeft 30 ^^^ (A 61).rotateLeft 30))
    (W 48 ^^^ W 50) (W 61) (W 56) h0 h1 h2 h6 h8 h12 h13 h14 he
  rw [hT, hW] at hR1
  have hR1' : (Operand.reg 1 : Operand 32).read t = A 65 := by
    rw [hR1, hWork65]
    ac_rfl
  have hR5 := rawR5_068 ((A 62).rotateLeft 30) (A 63) h1 h7 he
  have hR5' : (Operand.reg 5 : Operand 32).read t =
      (A 62).rotateLeft 30 ^^^ (A 63).rotateLeft 30 :=
    hR5.trans (BitVec.xor_comm _ _)
  have hR6 := (rawR6_068 (A 63)
    (W 63 + (A 59).rotateLeft 30 +
      (A 62 ^^^ (A 60).rotateLeft 30 ^^^ (A 61).rotateLeft 30)) h6 h8 he).trans hT
  have hR7 := rawR7_068 (A 63) h7 he
  have hR12 := (rawR12_068 (W 48 ^^^ W 50) (W 61) (W 56)
    h12 h13 h14 he).trans hW
  have hM16 := rawM16_068 stack ((A 62).rotateLeft 30) (W 66) hs h1 h9 he
  have hfoot : ∀ c ∈ (effect068 s).components,
      c ∈ [.mem ((Operand.reg 4 : Operand 64).read s + 16) 4,
        .reg 1, .reg 2, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 12, .flags, .rip] := by
    unfold effect068
    iterate 18 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [leaR32Effect_components,
        addR32Imm32Effect_components, addR32R32Effect_components,
        movM32R32Effect_components, movR32R32Effect_components,
        rolR32Effect_components, xorR32R32Effect_components,
        List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and, forall_eq, or_true]
    all_goals sha1_norm
  have ha := he.agrees.mono hfoot
  rw [hs] at ha
  have hmem {n : Nat} (off : BitVec 64) (hb : OffsetsApart 16 4 off (n / 8))
      (hsize : 4 + n / 8 < 2 ^ 64) :
      (Operand.mem (stack + off) : Operand n).read t =
      (Operand.mem (stack + off) : Operand n).read s := by
    apply memLoad_congr
    intro i hi
    apply congrArg (fun b : Option UInt8 ↦ b.getD 0)
    apply ha.byte
    intro c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨j,hj,heq⟩ := hCov
      exact hb.ne stack hj hi hsize heq.symm
    all_goals exact hCov.elim
  simp only [genericCut069, Write.AllHold]
  refine ⟨?f0, ?f1, ?f2, ?f3, ?f4, ?f5, ?f6, ?f7, ?f8, ?f9, ?f10,
    ?f11, ?f12, ?f13, ?f14, ?f15, ?f16, ?f17, ?f18, ?f19, ?f20, ?f21,
    ?f22, ?f23, ?f24, ?f25, ?f26, ?f27⟩
  case f0 => exact (ha.read (by simp)).trans h0
  case f1 => exact hR1'
  case f2 => exact hR5'
  case f3 => exact hR6
  case f4 => exact hR7
  case f5 => exact (ha.read (by simp)).trans h11
  case f6 => exact hR12
  case f7 => exact (ha.read (by simp)).trans h13
  case f8 => exact (ha.read (by simp)).trans h14
  case f9 => exact (ha.read (by simp)).trans h15
  case f10 => exact (hmem 0 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM0
  case f11 => exact (hmem 4 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM4
  case f12 => exact (hmem 8 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM8
  case f13 => exact hM16
  case f14 => exact (hmem 24 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM24
  case f15 => exact (hmem 32 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM32
  case f16 => exact (hmem 40 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM40
  case f17 => exact (hmem 48 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM48
  case f18 => exact (hmem 56 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM56
  case f19 => exact (hmem 64 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM64
  case f20 => exact (hmem 72 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM72
  case f21 => exact (hmem 80 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM80
  case f22 => exact (hmem 88 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM88
  case f23 => exact (hmem 116 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM116
  case f24 => exact (hmem 120 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM120
  case f25 => exact (hmem 124 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM124
  case f26 => exact (hmem 144 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM144
  case f27 => exact (hmem 152 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM152

theorem effect068_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16}
    {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut068 stack input H M))
    (he : (effect068 s).Holds s t) :
    Write.AllHold t (cut069 stack input H M) := by
  have hWork65 : (workingAfter M H 65).a =
      ((workingAfter M H 64).a).rotateLeft 5 +
        ((workingAfter M H 63).a ^^^ ((workingAfter M H 62).a).rotateLeft 30 ^^^
          ((workingAfter M H 61).a).rotateLeft 30) +
        ((workingAfter M H 60).a).rotateLeft 30 + 0xca62c1d6 + scheduleWord M 64 := by
    rw [workingAfter_step_a_values M H 60 (by decide +kernel),
      sha1_f_parity_last (by decide +kernel), Parity]
    simp [K]
  have hWork64 : (workingAfter M H 64).a =
      ((workingAfter M H 63).a).rotateLeft 5 +
        ((workingAfter M H 62).a ^^^ ((workingAfter M H 61).a).rotateLeft 30 ^^^
          ((workingAfter M H 60).a).rotateLeft 30) +
        ((workingAfter M H 59).a).rotateLeft 30 + 0xca62c1d6 + scheduleWord M 63 := by
    rw [workingAfter_step_a_values M H 59 (by decide +kernel),
      sha1_f_parity_last (by decide +kernel), Parity]
    simp [K]
  have hW64 : scheduleWord M 64 =
      (scheduleWord M 61 ^^^ scheduleWord M 56 ^^^ scheduleWord M 50 ^^^
        scheduleWord M 48).rotateLeft 1 := by
    change scheduleWord M (⟨64, by decide +kernel⟩ : Fin 80) = _
    rw [scheduleWord_recurrence M ⟨64, by decide +kernel⟩ (by decide +kernel),
      sha1Rotl_eq_rotateLeft 1 _ (by decide +kernel)]
    simp only [Nat.reduceSub]
    have h61 : (⟨61, by decide +kernel⟩ : Fin 80) = 61 := by decide +kernel
    have h56 : (⟨56, by decide +kernel⟩ : Fin 80) = 56 := by decide +kernel
    have h50 : (⟨50, by decide +kernel⟩ : Fin 80) = 50 := by decide +kernel
    have h48 : (⟨48, by decide +kernel⟩ : Fin 80) = 48 := by decide +kernel
    simp only [h61, h56, h50, h48]
  exact cutTransport068 (fun n ↦ (workingAfter M H n).a) (scheduleWord M)
    hWork64 hWork65 hW64 hf.stackPointer hw he
end Words068

end Block068

open Block068 in
theorem segment068 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x103356 0x103394
      cut068 cut069 := by
  have hout : ∀ d : Nat, d ≤ bytes068.length →
      0x103356 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      simp only [bytes068, List.length_cons, List.length_nil] at hd <;>
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  apply Segment.of_block (fun _ _ _ _ => effect068)
    (fun stack input H M => block068 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64
      0x3356) bytes068,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect068_rip he
  · intro stack input H M s t _ hf _ he
    exact effect068_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect068_words hf hw he

namespace Block069

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Spec.Program
open Standards.NIST.SHA1
open Sha1.Proofs.Compress.Rounds



def bytes069 : List UInt8 :=
  [0x48, 0x8b, 0x54, 0x24, 0x38, 0x41, 0x31, 0xd3, 0x44, 0x33, 0x1c, 0x24, 0x4c, 0x8b, 0x4c, 0x24, 0x48, 0x45, 0x31, 0xcb, 0x41, 0xd1, 0xc3, 0x31, 0xf5, 0x44, 0x01, 0xd8, 0x01, 0xe8, 0x33, 0x54, 0x24, 0x04, 0x33, 0x54, 0x24, 0x50, 0x44, 0x31, 0xe2, 0xd1, 0xc2, 0x49, 0x89, 0xd0, 0x89, 0xca, 0xc1, 0xc2, 0x05, 0xc1, 0xc6, 0x1e, 0x01, 0xd0, 0x05, 0xd6, 0xc1, 0x62, 0xca]

def effect069 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq ((movR64M64Effect 0x103394 2 (.sib 4 none 0 (.d8 0x38)))) (xorR32R32Effect 0x103399 3 11 2)) (xorR32M32Effect 0x10339c 11 (.sib 4 none 0 .none))) (movR64M64Effect 0x1033a0 9 (.sib 4 none 0 (.d8 0x48)))) (xorR32R32Effect 0x1033a5 3 11 9)) (rolR32Effect 0x1033a8 3 11 1)) (xorR32R32Effect 0x1033ab 2 5 6)) (addR32R32Effect 0x1033ad 3 0 11)) (addR32R32Effect 0x1033b0 2 0 5)) (xorR32M32LowEffect 0x1033b2 2 (.sib 4 none 0 (.d8 0x4)))) (xorR32M32LowEffect 0x1033b6 2 (.sib 4 none 0 (.d8 0x50)))) (xorR32R32Effect 0x1033ba 3 2 12)) (rolR32Effect 0x1033bd 2 2 1)) (movR64R64Effect 0x1033bf 8 2)) (movR32R32Effect 0x1033c2 2 2 1)) (rolR32Effect 0x1033c4 3 2 5)) (rolR32Effect 0x1033c7 3 6 30)) (addR32R32Effect 0x1033ca 2 0 2)) (addR32Imm32Effect 0x1033cc 5 0 0xca62c1d6)

set_option maxHeartbeats 800000 in
theorem block069 [Bindings] (boundary : ReturnBoundary) (stack input : BitVec 64)
    (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes069.length →
      0x103394 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x103394 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut069 stack input H M))
      (codeRange 0x103394 bytes069) effect069 := by
  have hRaw : AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x103394 ∧ FrameData stack input M s)
      (codeRange 0x103394 bytes069) effect069 := by
    unfold bytes069 at hout ⊢
    sha1_run_begin (mov_r64_m64_effect_step 0x103394 0x48 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) 2 (.sib 4 none 0 (.d8 0x38)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (xor_r32_r32_rex_effect_step 0x103399 0x41 0xd3 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (xor_r32_m32_effect_step 0x10339c 0x44 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) 3 (.sib 4 none 0 .none) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (mov_r64_m64_effect_step 0x1033a0 0x4c (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) 1 (.sib 4 none 0 (.d8 0x48)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (xor_r32_r32_rex_effect_step 0x1033a5 0x45 0xcb (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (rol_r32_one_rex_effect_step 0x1033a8 0x41 0xc3 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (xor_r32_r32_effect_step 0x1033ab 0xf5 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (add_r32_r32_rex_effect_step 0x1033ad 0x44 0xd8 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (add_r32_r32_effect_step 0x1033b0 0xe8 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (xor_r32_m32_low_effect_step 0x1033b2 2 (.sib 4 none 0 (.d8 0x4)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (xor_r32_m32_low_effect_step 0x1033b6 2 (.sib 4 none 0 (.d8 0x50)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (xor_r32_r32_rex_effect_step 0x1033ba 0x44 0xe2 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (rol_r32_one_effect_step 0x1033bd 0xc2 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (mov_r64_r64_effect_step 0x1033bf 0x49 0xd0 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (mov_r32_r32_effect_step 0x1033c2 0xca (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (rol_r32_imm8_effect_step 0x1033c4 0xc2 0x5 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (rol_r32_imm8_effect_step 0x1033c7 0xc6 0x1e (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (add_r32_r32_effect_step 0x1033ca 0xd0 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (add_eax_imm32_effect_step 0x1033cc 0xca62c1d6)
    sha1_run_finish [effect069]
  intro s hr hc hp
  exact hRaw s hr hc ⟨hp.1, hp.2.1⟩

private def genericCut069 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), ((A 61)).rotateLeft 30⟩,
    ⟨(.reg 1 : Operand 32), (A 65)⟩,
    ⟨(.reg 5 : Operand 32), (((A 62)).rotateLeft 30 ^^^ ((A 63)).rotateLeft 30)⟩,
    ⟨(.reg 6 : Operand 32), (A 64)⟩,
    ⟨(.reg 7 : Operand 32), ((A 63)).rotateLeft 30⟩,
    ⟨(.reg 11 : Operand 32), (W 49)⟩,
    ⟨(.reg 12 : Operand 32), (W 64)⟩,
    ⟨(.reg 13 : Operand 32), (W 61)⟩,
    ⟨(.reg 14 : Operand 32), (W 56)⟩,
    ⟨(.reg 15 : Operand 32), (W 60)⟩,
    ⟨(.mem (stack + 0) : Operand 32), (W 57)⟩,
    ⟨(.mem (stack + 4) : Operand 32), (W 53)⟩,
    ⟨(.mem (stack + 8) : Operand 32), (W 52)⟩,
    ⟨(.mem (stack + 16) : Operand 32), ((W 66) + ((A 62)).rotateLeft 30)⟩,
    ⟨(.mem (stack + 24) : Operand 32), (W 58)⟩,
    ⟨(.mem (stack + 32) : Operand 32), (W 54)⟩,
    ⟨(.mem (stack + 40) : Operand 32), (W 55)⟩,
    ⟨(.mem (stack + 48) : Operand 32), (W 63)⟩,
    ⟨(.mem (stack + 56) : Operand 32), (W 51)⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), (W 62)⟩,
    ⟨(.mem (stack + 80) : Operand 32), (W 59)⟩,
    ⟨(.mem (stack + 88) : Operand 32), (W 66)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

private def genericCut070 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), (A 66)⟩,
    ⟨(.reg 1 : Operand 32), (A 65)⟩,
    ⟨(.reg 6 : Operand 32), ((A 64)).rotateLeft 30⟩,
    ⟨(.reg 7 : Operand 32), ((A 63)).rotateLeft 30⟩,
    ⟨(.reg 8 : Operand 32), (W 67)⟩,
    ⟨(.reg 9 : Operand 32), (W 62)⟩,
    ⟨(.reg 11 : Operand 32), (W 65)⟩,
    ⟨(.reg 12 : Operand 32), (W 64)⟩,
    ⟨(.reg 13 : Operand 32), (W 61)⟩,
    ⟨(.reg 14 : Operand 32), (W 56)⟩,
    ⟨(.reg 15 : Operand 32), (W 60)⟩,
    ⟨(.mem (stack + 0) : Operand 32), (W 57)⟩,
    ⟨(.mem (stack + 4) : Operand 32), (W 53)⟩,
    ⟨(.mem (stack + 8) : Operand 32), (W 52)⟩,
    ⟨(.mem (stack + 16) : Operand 32), ((W 66) + ((A 62)).rotateLeft 30)⟩,
    ⟨(.mem (stack + 24) : Operand 32), (W 58)⟩,
    ⟨(.mem (stack + 32) : Operand 32), (W 54)⟩,
    ⟨(.mem (stack + 40) : Operand 32), (W 55)⟩,
    ⟨(.mem (stack + 48) : Operand 32), (W 63)⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), (W 62)⟩,
    ⟨(.mem (stack + 80) : Operand 32), (W 59)⟩,
    ⟨(.mem (stack + 88) : Operand 32), (W 66)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

theorem effect069_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (_hf : FrameData stack input M s)
    (he : (effect069 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hfoot : ∀ c ∈ (effect069 s).components, c ∈ [.reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect069
    iterate 18 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [addR32Imm32Effect_components, addR32R32Effect_components, movR32R32Effect_components, movR64M64Effect_components, movR64R64Effect_components, rolR32Effect_components, xorR32M32Effect_components, xorR32M32LowEffect, xorR32R32Effect_components, List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and, forall_eq]
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


theorem effect069_rip {s t : RamState}
    (he : (effect069 s).Holds s t) :
    t.RIP = 0x1033d1 := by
  exact he.rip.trans (by rfl)

section Words069

private theorem full069 (s : RamState) : ∀ w ∈ (effect069 s).writes, w.Full := by
  apply Effect.Local.full
  unfold effect069
  repeat' first | (solve | x86_local) | apply Effect.Local.seq

private theorem rawR6_069 {s t : RamState} (v6 : BitVec 32)
    (h6 : (Operand.reg 6 : Operand 32).read s = v6)
    (he : (effect069 s).Holds s t) :
    (Operand.reg 6 : Operand 32).read t = v6.rotateLeft 30 := by
  have ho := he.obsAfter (full069 s) true
  sha1_norm at h6
  simp only [← ho.read_reg]
  sha1_norm [leaSpec, effect069, h6,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]


private theorem rawR9_069 {s t : RamState} (stack : BitVec 64) (v72 : BitVec 32)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (h72 : (Operand.mem (stack + 72) : Operand 32).read s = v72)
    (he : (effect069 s).Holds s t) :
    (Operand.reg 9 : Operand 32).read t = v72 := by
  have ho := he.obsAfter (full069 s) true
  sha1_norm at hs h72
  simp only [Operand.read] at h72
  simp only [← ho.read_reg]
  sha1_norm [leaSpec, effect069, hs, h72,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
  all_goals simp only [Operand.read, memLoad_low32, h72]

private theorem rawR11_069 {s t : RamState} (stack : BitVec 64) (v11 v0 v56 v72 : BitVec 32)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (h11 : (Operand.reg 11 : Operand 32).read s = v11)
    (h0 : (Operand.mem (stack + 0) : Operand 32).read s = v0)
    (h56 : (Operand.mem (stack + 56) : Operand 32).read s = v56)
    (h72 : (Operand.mem (stack + 72) : Operand 32).read s = v72)
    (he : (effect069 s).Holds s t) :
    (Operand.reg 11 : Operand 32).read t = (v11 ^^^ v56 ^^^ v0 ^^^ v72).rotateLeft 1 := by
  have ho := he.obsAfter (full069 s) true
  sha1_norm at hs h11 h0 h56 h72
  simp only [Operand.read] at h0 h56 h72
  simp only [← ho.read_reg]
  sha1_norm [leaSpec, effect069, hs, h11, h0, h56, h72,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
  all_goals simp only [Operand.read, memLoad_low32, h0, h56, h72]

private theorem rawR8_069 {s t : RamState} (stack : BitVec 64) (v12 v4 v56 v80 : BitVec 32)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (h12 : (Operand.reg 12 : Operand 32).read s = v12)
    (h4 : (Operand.mem (stack + 4) : Operand 32).read s = v4)
    (h56 : (Operand.mem (stack + 56) : Operand 32).read s = v56)
    (h80 : (Operand.mem (stack + 80) : Operand 32).read s = v80)
    (he : (effect069 s).Holds s t) :
    (Operand.reg 8 : Operand 32).read t = (v56 ^^^ v4 ^^^ v80 ^^^ v12).rotateLeft 1 := by
  have ho := he.obsAfter (full069 s) true
  sha1_norm at hs h12 h4 h56 h80
  simp only [Operand.read] at h4 h56 h80
  simp only [← ho.read_reg]
  sha1_norm [leaSpec, effect069, hs, h12, h4, h56, h80,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
  all_goals simp only [Operand.read, memLoad_low32, h4, h56, h80]

private theorem rawR0_069 {s t : RamState} (stack : BitVec 64) (v0 v1 v5 v6 v11 m0 m56 m72 : BitVec 32)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (h0 : (Operand.reg 0 : Operand 32).read s = v0)
    (h1 : (Operand.reg 1 : Operand 32).read s = v1)
    (h5 : (Operand.reg 5 : Operand 32).read s = v5)
    (h6 : (Operand.reg 6 : Operand 32).read s = v6)
    (h11 : (Operand.reg 11 : Operand 32).read s = v11)
    (hM0 : (Operand.mem (stack + 0) : Operand 32).read s = m0)
    (hM56 : (Operand.mem (stack + 56) : Operand 32).read s = m56)
    (hM72 : (Operand.mem (stack + 72) : Operand 32).read s = m72)
    (he : (effect069 s).Holds s t) :
    (Operand.reg 0 : Operand 32).read t = 
      v0 + (v11 ^^^ m56 ^^^ m0 ^^^ m72).rotateLeft 1 +
        (v5 ^^^ v6) + v1.rotateLeft 5 + 0xca62c1d6 := by
  have ho := he.obsAfter (full069 s) true
  sha1_norm at hs h0 h1 h5 h6 h11 hM0 hM56 hM72
  simp only [Operand.read] at hM0 hM56 hM72
  simp only [← ho.read_reg]
  sha1_norm [leaSpec, effect069, hs, h0, h1, h5, h6, h11, hM0, hM56, hM72,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
  all_goals simp only [Operand.read, memLoad_low32, hM0, hM56, hM72]

theorem effect069_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16}
    {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut069 stack input H M))
    (he : (effect069 s).Holds s t) :
    Write.AllHold t (cut070 stack input H M) := by
  have hWork : (workingAfter M H 66).a =
      ((workingAfter M H 65).a).rotateLeft 5 +
        ((workingAfter M H 64).a ^^^ ((workingAfter M H 63).a).rotateLeft 30 ^^^
          ((workingAfter M H 62).a).rotateLeft 30) +
        ((workingAfter M H 61).a).rotateLeft 30 + 0xca62c1d6 + scheduleWord M 65 := by
    rw [workingAfter_step_a_values M H 61 (by decide +kernel),
      sha1_f_parity_last (by decide +kernel), Parity]
    have hpar (x y z : BitVec 32) : x ^^^ y ^^^ z = x ^^^ (z ^^^ y) := by
      calc
        x ^^^ y ^^^ z = x ^^^ (y ^^^ z) := BitVec.xor_assoc x y z
        _ = x ^^^ (z ^^^ y) := by rw [BitVec.xor_comm y z]
    rw [hpar]
    simp only [Nat.reduceAdd]
    rw [show K (⟨65, by decide +kernel⟩ : Fin 80) = 0xca62c1d6 by decide +kernel]
    have h65 : (⟨65, by decide +kernel⟩ : Fin 80) = 65 := by decide +kernel
    rw [h65]
  have hW65 : scheduleWord M 65 =
      (scheduleWord M 62 ^^^ scheduleWord M 57 ^^^ scheduleWord M 51 ^^^
        scheduleWord M 49).rotateLeft 1 := by
    change scheduleWord M (⟨65, by decide +kernel⟩ : Fin 80) = _
    rw [scheduleWord_recurrence M ⟨65, by decide +kernel⟩ (by decide +kernel),
      sha1Rotl_eq_rotateLeft 1 _ (by decide +kernel)]
    simp only [Nat.reduceSub]
    have h62 : (⟨62, by decide +kernel⟩ : Fin 80) = 62 := by decide +kernel
    have h57 : (⟨57, by decide +kernel⟩ : Fin 80) = 57 := by decide +kernel
    have h51 : (⟨51, by decide +kernel⟩ : Fin 80) = 51 := by decide +kernel
    have h49 : (⟨49, by decide +kernel⟩ : Fin 80) = 49 := by decide +kernel
    simp only [h62, h57, h51, h49]
  have hW67 : scheduleWord M 67 =
      (scheduleWord M 64 ^^^ scheduleWord M 59 ^^^ scheduleWord M 53 ^^^
        scheduleWord M 51).rotateLeft 1 := by
    change scheduleWord M (⟨67, by decide +kernel⟩ : Fin 80) = _
    rw [scheduleWord_recurrence M ⟨67, by decide +kernel⟩ (by decide +kernel),
      sha1Rotl_eq_rotateLeft 1 _ (by decide +kernel)]
    simp only [Nat.reduceSub]
    have h64 : (⟨64, by decide +kernel⟩ : Fin 80) = 64 := by decide +kernel
    have h59 : (⟨59, by decide +kernel⟩ : Fin 80) = 59 := by decide +kernel
    have h53 : (⟨53, by decide +kernel⟩ : Fin 80) = 53 := by decide +kernel
    have h51 : (⟨51, by decide +kernel⟩ : Fin 80) = 51 := by decide +kernel
    simp only [h64, h59, h53, h51]
  simp only [cut069, Write.AllHold] at hw
  obtain ⟨h0,h1,h5,h6,h7,h11,h12,h13,h14,h15,
    hM0,hM4,hM8,hM16,hM24,hM32,hM40,hM48,hM56,hM64,
    hM72,hM80,hM88,hM116,hM120,hM124,hM144,hM152⟩ := hw
  have hR6 := rawR6_069 _ h6 he
  have hR9 := rawR9_069 stack _ hf.stackPointer hM72 he
  have hR11 := rawR11_069 stack _ _ _ _ hf.stackPointer h11 hM0 hM56 hM72 he
  have hR8 := rawR8_069 stack _ _ _ _ hf.stackPointer h12 hM4 hM56 hM80 he
  have hR0 := rawR0_069 stack _ _ _ _ _ _ _ _
    hf.stackPointer h0 h1 h5 h6 h11 hM0 hM56 hM72 he
  have hV11 : (Operand.reg 11 : Operand 32).read t = scheduleWord M 65 := by
    rw [hR11, hW65]
    congr 1
    ac_rfl
  have hV8 : (Operand.reg 8 : Operand 32).read t = scheduleWord M 67 := by
    rw [hR8, hW67]
    congr 1
    ac_rfl
  have hV0 : (Operand.reg 0 : Operand 32).read t = (workingAfter M H 66).a := by
    rw [hR0, hWork, hW65]
    simp only [BitVec.xor_assoc, BitVec.xor_comm]
    ac_rfl
  have hfoot : ∀ c ∈ (effect069 s).components,
      c ∈ [.reg 0, .reg 2, .reg 5, .reg 6, .reg 8, .reg 9, .reg 11, .flags, .rip] := by
    unfold effect069
    iterate 18 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [addR32Imm32Effect_components, addR32R32Effect_components,
        movR32R32Effect_components, movR64M64Effect_components, movR64R64Effect_components,
        rolR32Effect_components, xorR32M32Effect_components, xorR32M32LowEffect,
        xorR32R32Effect_components, List.mem_cons, List.not_mem_nil, or_false,
        or_imp, forall_and, forall_eq]
    all_goals sha1_norm
  have ha := he.agrees.mono hfoot
  have hmem {n : Nat} (off : BitVec 64) :
      (Operand.mem (stack + off) : Operand n).read t =
        (Operand.mem (stack + off) : Operand n).read s := by
    apply memLoad_congr
    intro i hi
    apply congrArg (fun b : Option UInt8 ↦ b.getD 0)
    apply ha.byte
    intro c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact hCov.elim
  simp only [cut070, Write.AllHold]
  refine ⟨hV0, ?_, hR6, ?_, hV8, hR9, hV11, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (ha.read (by simp)).trans h1
  · exact (ha.read (by simp)).trans h7
  · exact (ha.read (by simp)).trans h12
  · exact (ha.read (by simp)).trans h13
  · exact (ha.read (by simp)).trans h14
  · exact (ha.read (by simp)).trans h15
  · exact (hmem 0).trans hM0
  · exact (hmem 4).trans hM4
  · exact (hmem 8).trans hM8
  · exact (hmem 16).trans hM16
  · exact (hmem 24).trans hM24
  · exact (hmem 32).trans hM32
  · exact (hmem 40).trans hM40
  · exact (hmem 48).trans hM48
  · exact (hmem 64).trans hM64
  · exact (hmem 72).trans hM72
  · exact (hmem 80).trans hM80
  · exact (hmem 88).trans hM88
  · exact (hmem 116).trans hM116
  · exact (hmem 120).trans hM120
  · exact (hmem 124).trans hM124
  · exact (hmem 144).trans hM144
  · exact (hmem 152).trans hM152
end Words069

end Block069

open Block069 in
theorem segment069 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x103394 0x1033d1
      cut069 cut070 := by
  have hout : ∀ d : Nat, d ≤ bytes069.length →
      0x103394 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      simp only [bytes069, List.length_cons, List.length_nil] at hd <;>
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  apply Segment.of_block (fun _ _ _ _ => effect069)
    (fun stack input H M => block069 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64
      0x3394) bytes069,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect069_rip he
  · intro stack input H M s t _ hf _ he
    exact effect069_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect069_words hf hw he

namespace Block070

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Spec.Program
open Standards.NIST.SHA1 Sha1.Proofs.Compress.Rounds


def bytes070 : List UInt8 :=
  [0x89, 0xc2, 0xc1, 0xc2, 0x5, 0x45, 0x8d, 0x14, 0x38, 0x4c, 0x89, 0xc5, 0x4c, 0x89, 0x44, 0x24, 0x38, 0x31, 0xf7, 0x31, 0xcf, 0x3, 0x7c, 0x24, 0x10, 0x8d, 0x1c, 0x3a, 0x81, 0xc3, 0xd6, 0xc1, 0x62, 0xca]

set_option maxHeartbeats 800000 in
def effect070 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq ((movR32R32Effect 0x1033d1 2 2 0)) (rolR32Effect 0x1033d3 3 2 5)) (leaR32Effect 0x1033d6 4 10 (.sib 8 (some 7) 0 .none))) (movR64R64Effect 0x1033da 5 8)) (movM64R64Effect 0x1033dd 8 (.sib 4 none 0 (.d8 0x38)))) (xorR32R32Effect 0x1033e2 2 7 6)) (xorR32R32Effect 0x1033e4 2 7 1)) (addR32M32Effect 0x1033e6 4 7 (.sib 4 none 0 (.d8 0x10)))) (leaR32Effect 0x1033ea 3 3 (.sib 2 (some 7) 0 .none))) (addR32Imm32Effect 0x1033ed 6 3 0xca62c1d6)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
theorem block070 [Bindings] (boundary : ReturnBoundary)
    (stack input : BitVec 64) (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes070.length → 0x1033d1 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x1033d1 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut070 stack input H M))
      (codeRange 0x1033d1 bytes070) effect070 := by
  unfold bytes070 at hout ⊢
  sha1_run_begin (mov_r32_r32_effect_step 0x1033d1 0xc2 (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x1033d3 0xc2 0x5 (by decide +kernel) (by decide +kernel))
  sha1_run_then (lea_r32_rex_effect_step 0x1033d6 0x45 (by unfold RexNoWPrefix; decide +kernel) 2 (.sib 8 (some 7) 0 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_r64_effect_step 0x1033da 0x4c 0xc5 (by unfold RexWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step 0x1033dd 0x4c (by unfold RexWPrefix; decide +kernel) 0 (.sib 4 none 0 (.d8 0x38)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x1033e2 0xf7 (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x1033e4 0xcf (by decide +kernel))
  sha1_run_then (add_r32_m32_effect_step 0x1033e6 7 (.sib 4 none 0 (.d8 0x10)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (lea_r32_effect_step 0x1033ea 3 (.sib 2 (some 7) 0 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_imm32_effect_step 0x1033ed 0xc3 0xca62c1d6 (by decide +kernel) (by decide +kernel))
  sha1_run_finish [effect070]

set_option maxRecDepth 10000 in
private theorem components070 (s : RamState) :
    ∀ c ∈ (effect070 s).components, c ∈ [.mem ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 56) 8, .reg 2, .reg 3, .reg 5, .reg 7, .reg 10, .flags, .rip] := by
  unfold effect070
  iterate 9 apply components_seq_of
  all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
    [addR32Imm32Effect_components, addR32M32Effect_components, leaR32Effect_components, movM64R64Effect_components, movR32R32Effect_components, movR64R64Effect_components, rolR32Effect_components, xorR32R32Effect_components, List.mem_cons, List.not_mem_nil,
      or_false, or_imp, forall_and, forall_eq, or_true]
  all_goals sha1_norm

set_option maxRecDepth 10000 in
theorem effect070_agrees {stack input : BitVec 64} {M : Vector (BitVec 32) 16}
    {s t : RamState} (hf : FrameData stack input M s) (he : (effect070 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have ha := he.agrees.mono (components070 s)
  rw [hs] at ha
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all (config := {decide := true, implicitDefEqProofs := false}) only
      [Component.isMem, scratchComponents, x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hCov.elim
      | exact scratchComponents_stack (Or.inl (by decide +kernel)) hCov

set_option maxRecDepth 10000 in
private theorem full070 (s : RamState) : ∀ w ∈ (effect070 s).writes, w.Full := by
  apply Effect.Local.full
  unfold effect070
  repeat' first | (solve | x86_local) | apply Effect.Local.seq

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
theorem effect070_words {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (hw : Write.AllHold s (cut070 stack input H M))
    (he : (effect070 s).Holds s t) : Write.AllHold t (cut071 stack input H M) := by
  have ho := he.obsAfter (full070 s) true
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have ha := he.agrees.mono (components070 s)
  rw [hs] at ha
  simp only [cut070, Write.AllHold] at hw
  obtain ⟨h0, h1, h6, h7, h8, h9, h11, h12, h13, h14, h15, hM0, hM4, hM8, hM16, hM24, hM32, hM40, hM48, hM64, hM72, hM80, hM88, hM116, hM120, hM124, hM144, hM152⟩ := hw
  have hmem {width : Nat} (off : BitVec 64)
      (hb : OffsetsApart 56 8 off (width / 8)) (hz : 8 + width / 8 < 2 ^ 64) :
      (Operand.mem (stack + off) : Operand width).read t =
      (Operand.mem (stack + off) : Operand width).read s := by
    apply memLoad_congr
    intro i hi
    apply congrArg (fun b : Option UInt8 ↦ b.getD 0)
    apply ha.byte
    intro c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨j, hj, heq⟩ := hCov
      exact hb.ne stack hj hi hz heq.symm
    all_goals exact hCov.elim
  have hA67 := workingAfter_step_a_values M H 62 (by decide +kernel)
  simp (config := {decide := true}) only [Nat.reduceAdd, f, K, Parity, ite_false] at hA67
  have hT66 : (⟨66, by decide +kernel⟩ : Fin 80) = 66 := by decide +kernel
  simp only [hT66] at hA67
  sha1_norm at hA67
  simp only [cut071, Write.AllHold]
  refine ⟨?f0, ?f1, ?f2, ?f3, ?f4, ?f5, ?f6, ?f7, ?f8, ?f9, ?f10, ?f11, ?f12, ?f13, ?f14, ?f15, ?f16, ?f17, ?f18, ?f19, ?f20, ?f21, ?f22, ?f23, ?f24, ?f25, ?f26, ?f27, ?f28⟩
  case f0 =>
    exact (ha.read (by simp)).trans h0
  case f1 =>
    exact (ha.read (by simp)).trans h1
  case f2 =>
    sha1_norm at hs h0 h1 h6 h7 h8 h9 h11 h12 h13 h14 h15 hM0 hM4 hM8 hM16 hM24 hM32 hM40 hM48 hM64 hM72 hM80 hM88 hM116 hM120 hM124 hM144 hM152
    simp only [← ho.read_reg]
    sha1_norm [effect070, hs, h0, h1, h6, h7, h8, h9, h11, h12, h13, h14, h15, hM0, hM4, hM8, hM16, hM24, hM32, hM40, hM48, hM64, hM72, hM80, hM88, hM116, hM120, hM124, hM144, hM152, leaSpec,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, read32_memStore64_low,
      extractLsb'_zero_eq_setWidth, memLoad_memStore]
    all_goals simp only [hA67]
    all_goals ac_rfl
  case f3 =>
    sha1_norm at hs h0 h1 h6 h7 h8 h9 h11 h12 h13 h14 h15 hM0 hM4 hM8 hM16 hM24 hM32 hM40 hM48 hM64 hM72 hM80 hM88 hM116 hM120 hM124 hM144 hM152
    simp only [← ho.read_reg]
    sha1_norm [effect070, hs, h0, h1, h6, h7, h8, h9, h11, h12, h13, h14, h15, hM0, hM4, hM8, hM16, hM24, hM32, hM40, hM48, hM64, hM72, hM80, hM88, hM116, hM120, hM124, hM144, hM152, leaSpec,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, read32_memStore64_low,
      extractLsb'_zero_eq_setWidth, memLoad_memStore]
    all_goals ac_rfl
  case f4 =>
    exact (ha.read (by simp)).trans h6
  case f5 =>
    exact (ha.read (by simp)).trans h9
  case f6 =>
    sha1_norm at hs h0 h1 h6 h7 h8 h9 h11 h12 h13 h14 h15 hM0 hM4 hM8 hM16 hM24 hM32 hM40 hM48 hM64 hM72 hM80 hM88 hM116 hM120 hM124 hM144 hM152
    simp only [← ho.read_reg]
    sha1_norm [effect070, hs, h0, h1, h6, h7, h8, h9, h11, h12, h13, h14, h15, hM0, hM4, hM8, hM16, hM24, hM32, hM40, hM48, hM64, hM72, hM80, hM88, hM116, hM120, hM124, hM144, hM152, leaSpec,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, read32_memStore64_low,
      extractLsb'_zero_eq_setWidth, memLoad_memStore]
    all_goals ac_rfl
  case f7 =>
    exact (ha.read (by simp)).trans h11
  case f8 =>
    exact (ha.read (by simp)).trans h12
  case f9 =>
    exact (ha.read (by simp)).trans h13
  case f10 =>
    exact (ha.read (by simp)).trans h14
  case f11 =>
    exact (ha.read (by simp)).trans h15
  case f12 =>
    exact (hmem 0 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM0
  case f13 =>
    exact (hmem 4 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM4
  case f14 =>
    exact (hmem 8 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM8
  case f15 =>
    exact (hmem 24 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM24
  case f16 =>
    exact (hmem 32 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM32
  case f17 =>
    exact (hmem 40 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM40
  case f18 =>
    exact (hmem 48 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM48
  case f19 =>
    sha1_norm at hs h0 h1 h6 h7 h8 h9 h11 h12 h13 h14 h15 hM0 hM4 hM8 hM16 hM24 hM32 hM40 hM48 hM64 hM72 hM80 hM88 hM116 hM120 hM124 hM144 hM152
    simp only [← ho.read_mem]
    sha1_norm [effect070, hs, h0, h1, h6, h7, h8, h9, h11, h12, h13, h14, h15, hM0, hM4, hM8, hM16, hM24, hM32, hM40, hM48, hM64, hM72, hM80, hM88, hM116, hM120, hM124, hM144, hM152, leaSpec,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, read32_memStore64_low,
      extractLsb'_zero_eq_setWidth, memLoad_memStore]
    all_goals ac_rfl
  case f20 =>
    exact (hmem 64 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM64
  case f21 =>
    exact (hmem 72 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM72
  case f22 =>
    exact (hmem 80 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM80
  case f23 =>
    exact (hmem 88 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM88
  case f24 =>
    exact (hmem 116 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM116
  case f25 =>
    exact (hmem 120 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM120
  case f26 =>
    exact (hmem 124 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM124
  case f27 =>
    exact (hmem 144 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM144
  case f28 =>
    exact (hmem 152 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM152

end Block070

open Block070 in
set_option maxRecDepth 10000 in
theorem segment070 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x1033d1 0x1033f3 cut070 cut071 := by
  have hout : ∀ d : Nat, d ≤ bytes070.length →
      0x1033d1 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      simp only [bytes070, List.length_cons, List.length_nil] at hd <;>
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  apply Segment.of_block (fun _ _ _ _ ↦ effect070)
    (fun stack input H M ↦ block070 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64
      0x33d1) bytes070, x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact he.rip.trans (by rfl)
  · intro stack input H M s t _ hf _ he
    exact effect070_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect070_words hf hw he

namespace Block071

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Spec.Program
open Standards.NIST.SHA1
open Sha1.Proofs.Compress.Rounds



def bytes071 : List UInt8 :=
  [0xc1, 0xc1, 0x1e, 0x41, 0x89, 0xc8, 0x41, 0x31, 0xf0, 0x41, 0x31, 0xc0, 0x45, 0x01, 0xd0, 0xc1, 0xc0, 0x1e, 0x48, 0x8b, 0x54, 0x24, 0x20, 0x44, 0x8b, 0x54, 0x24, 0x08, 0x41, 0x31, 0xd2, 0x44, 0x31, 0xf2, 0x44, 0x31, 0xca, 0x31, 0xea, 0xd1, 0xc2, 0x48, 0x89, 0x54, 0x24, 0x20, 0x89, 0xdf, 0xc1, 0xc7, 0x1e, 0x89, 0xfd]

def effect071 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq ((rolR32Effect 0x1033f3 3 1 30)) (movR32R32Effect 0x1033f6 3 8 1)) (xorR32R32Effect 0x1033f9 3 8 6)) (xorR32R32Effect 0x1033fc 3 8 0)) (addR32R32Effect 0x1033ff 3 8 10)) (rolR32Effect 0x103402 3 0 30)) (movR64M64Effect 0x103405 2 (.sib 4 none 0 (.d8 0x20)))) (movR32M32Effect 0x10340a 10 (.sib 4 none 0 (.d8 0x8)))) (xorR32R32Effect 0x10340f 3 10 2)) (xorR32R32Effect 0x103412 3 2 14)) (xorR32R32Effect 0x103415 3 2 9)) (xorR32R32Effect 0x103418 2 2 5)) (rolR32Effect 0x10341a 2 2 1)) (movM64R64Effect 0x10341c 2 (.sib 4 none 0 (.d8 0x20)))) (movR32R32Effect 0x103421 2 7 3)) (rolR32Effect 0x103423 3 7 30)) (movR32R32Effect 0x103426 2 5 7)

set_option maxHeartbeats 800000 in
theorem block071 [Bindings] (boundary : ReturnBoundary) (stack input : BitVec 64)
    (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes071.length →
      0x1033f3 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x1033f3 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut071 stack input H M))
      (codeRange 0x1033f3 bytes071) effect071 := by
  have hRaw : AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x1033f3 ∧ FrameData stack input M s)
      (codeRange 0x1033f3 bytes071) effect071 := by
    unfold bytes071 at hout ⊢
    sha1_run_begin (rol_r32_imm8_effect_step 0x1033f3 0xc1 0x1e (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (mov_r32_r32_rex_effect_step 0x1033f6 0x41 0xc8 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (xor_r32_r32_rex_effect_step 0x1033f9 0x41 0xf0 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (xor_r32_r32_rex_effect_step 0x1033fc 0x41 0xc0 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (add_r32_r32_rex_effect_step 0x1033ff 0x45 0xd0 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (rol_r32_imm8_effect_step 0x103402 0xc0 0x1e (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (mov_r64_m64_effect_step 0x103405 0x48 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) 2 (.sib 4 none 0 (.d8 0x20)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (mov_r32_m32_effect_step 0x10340a 0x44 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) 2 (.sib 4 none 0 (.d8 0x8)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (xor_r32_r32_rex_effect_step 0x10340f 0x41 0xd2 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (xor_r32_r32_rex_effect_step 0x103412 0x44 0xf2 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (xor_r32_r32_rex_effect_step 0x103415 0x44 0xca (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (xor_r32_r32_effect_step 0x103418 0xea (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (rol_r32_one_effect_step 0x10341a 0xc2 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step 0x10341c 0x48 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) 2 (.sib 4 none 0 (.d8 0x20)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (mov_r32_r32_effect_step 0x103421 0xdf (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (rol_r32_imm8_effect_step 0x103423 0xc7 0x1e (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (mov_r32_r32_effect_step 0x103426 0xfd (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_finish [effect071]
  intro s hr hc hp
  exact hRaw s hr hc ⟨hp.1, hp.2.1⟩

private def genericCut071 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), (A 66)⟩,
    ⟨(.reg 1 : Operand 32), (A 65)⟩,
    ⟨(.reg 3 : Operand 32), (A 67)⟩,
    ⟨(.reg 5 : Operand 32), (W 67)⟩,
    ⟨(.reg 6 : Operand 32), ((A 64)).rotateLeft 30⟩,
    ⟨(.reg 9 : Operand 32), (W 62)⟩,
    ⟨(.reg 10 : Operand 32), ((W 67) + ((A 63)).rotateLeft 30)⟩,
    ⟨(.reg 11 : Operand 32), (W 65)⟩,
    ⟨(.reg 12 : Operand 32), (W 64)⟩,
    ⟨(.reg 13 : Operand 32), (W 61)⟩,
    ⟨(.reg 14 : Operand 32), (W 56)⟩,
    ⟨(.reg 15 : Operand 32), (W 60)⟩,
    ⟨(.mem (stack + 0) : Operand 32), (W 57)⟩,
    ⟨(.mem (stack + 4) : Operand 32), (W 53)⟩,
    ⟨(.mem (stack + 8) : Operand 32), (W 52)⟩,
    ⟨(.mem (stack + 24) : Operand 32), (W 58)⟩,
    ⟨(.mem (stack + 32) : Operand 32), (W 54)⟩,
    ⟨(.mem (stack + 40) : Operand 32), (W 55)⟩,
    ⟨(.mem (stack + 48) : Operand 32), (W 63)⟩,
    ⟨(.mem (stack + 56) : Operand 32), (W 67)⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), (W 62)⟩,
    ⟨(.mem (stack + 80) : Operand 32), (W 59)⟩,
    ⟨(.mem (stack + 88) : Operand 32), (W 66)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

private def genericCut072 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), ((A 66)).rotateLeft 30⟩,
    ⟨(.reg 1 : Operand 32), ((A 65)).rotateLeft 30⟩,
    ⟨(.reg 2 : Operand 32), (W 70)⟩,
    ⟨(.reg 3 : Operand 32), (A 67)⟩,
    ⟨(.reg 5 : Operand 32), ((A 67)).rotateLeft 30⟩,
    ⟨(.reg 6 : Operand 32), ((A 64)).rotateLeft 30⟩,
    ⟨(.reg 7 : Operand 32), ((A 67)).rotateLeft 30⟩,
    ⟨(.reg 8 : Operand 32), ((W 67) + ((A 63)).rotateLeft 30 + ((A 66) ^^^ ((A 64)).rotateLeft 30 ^^^ ((A 65)).rotateLeft 30))⟩,
    ⟨(.reg 10 : Operand 32), ((W 52) ^^^ (W 54))⟩,
    ⟨(.reg 11 : Operand 32), (W 65)⟩,
    ⟨(.reg 12 : Operand 32), (W 64)⟩,
    ⟨(.reg 13 : Operand 32), (W 61)⟩,
    ⟨(.reg 14 : Operand 32), (W 56)⟩,
    ⟨(.reg 15 : Operand 32), (W 60)⟩,
    ⟨(.mem (stack + 0) : Operand 32), (W 57)⟩,
    ⟨(.mem (stack + 4) : Operand 32), (W 53)⟩,
    ⟨(.mem (stack + 24) : Operand 32), (W 58)⟩,
    ⟨(.mem (stack + 32) : Operand 32), (W 70)⟩,
    ⟨(.mem (stack + 40) : Operand 32), (W 55)⟩,
    ⟨(.mem (stack + 48) : Operand 32), (W 63)⟩,
    ⟨(.mem (stack + 56) : Operand 32), (W 67)⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), (W 62)⟩,
    ⟨(.mem (stack + 80) : Operand 32), (W 59)⟩,
    ⟨(.mem (stack + 88) : Operand 32), (W 66)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

theorem effect071_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (he : (effect071 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hfoot : ∀ c ∈ (effect071 s).components, c ∈ [.mem ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 32) 8, .reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect071
    iterate 16 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [addR32R32Effect_components, movM64R64Effect_components, movR32M32Effect_components, movR32R32Effect_components, movR64M64Effect_components, rolR32Effect_components, xorR32R32Effect_components, List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and, forall_eq, or_true]
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

theorem effect071_rip {s t : RamState}
    (he : (effect071 s).Holds s t) :
    t.RIP = 0x103428 := by
  exact he.rip.trans (by rfl)

section Words071
private theorem genericWords071 {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} (A : Nat → BitVec 32)
    (W : Fin 80 → BitVec 32) {s t : RamState}
    (hSchedule70 : W 70 =
      (W 67 ^^^ W 62 ^^^ W 56 ^^^ W 54).rotateLeft 1)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hw : Write.AllHold s (genericCut071 stack input H A W))
    (he : (effect071 s).Holds s t) :
    Write.AllHold t (genericCut072 stack input H A W) := by
  have hfull : ∀ wr ∈ (effect071 s).writes, wr.Full := by
    apply Effect.Local.full
    unfold effect071
    repeat' first
      | solve | x86_local
      | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  sha1_norm at hs
  simp only [genericCut071, Write.AllHold] at hw
  obtain ⟨h0,h1,h3,h5,h6,h9,h10,h11,h12,h13,h14,h15,
    hM0,hM4,hM8,hM24,hM32,hM40,hM48,hM56,hM64,hM72,hM80,hM88,
    hM116,hM120,hM124,hM144,hM152⟩ := hw
  sha1_norm at h0 h1 h3 h5 h6 h9 h10 h11 h12 h13 h14 h15
  sha1_norm at hM0 hM4 hM8 hM24 hM32 hM40 hM48 hM56 hM64 hM72 hM80 hM88 hM116 hM120 hM124 hM144 hM152
  simp only [Operand.read] at hM8 hM32
  simp only [genericCut072, Write.AllHold, ← ho.read_reg, ← ho.read_mem]
  sha1_norm [leaSpec, effect071, hs, h0,h1,h3,h5,h6,h9,h10,h11,h12,h13,h14,h15,
    hM0,hM4,hM8,hM24,hM32,hM40,hM48,hM56,hM64,hM72,hM80,hM88,
    hM116,hM120,hM124,hM144,hM152]
  rw [hSchedule70]
  simp (config := {implicitDefEqProofs := false, decide := true}) only [Operand.read,
    memLoad_low32,
    read32_memStore64_low,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    BitVec.extractLsb'_setWidth_of_le, BitVec.extractLsb'_eq_self,
    BitVec.xor_assoc, BitVec.xor_comm, hM8, hM32]
  simp only [true_and]
  generalize hF : A 66 ^^^ (A 64).rotateLeft 30 ^^^ A 65 = f at ⊢
  generalize hS : (W 67 ^^^ W 62 ^^^ W 56 ^^^ W 54).rotateLeft 1 = w at ⊢
  generalize hW : W 52 ^^^ W 54 = x at ⊢
  ac_rfl

theorem effect071_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16}
    {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut071 stack input H M))
    (he : (effect071 s).Holds s t) :
    Write.AllHold t (cut072 stack input H M) := by
  have hSchedule70 : scheduleWord M 70 =
      (scheduleWord M 67 ^^^ scheduleWord M 62 ^^^ scheduleWord M 56 ^^^
        scheduleWord M 54).rotateLeft 1 := by
    change scheduleWord M (⟨70, by decide +kernel⟩ : Fin 80) = _
    rw [scheduleWord_recurrence M ⟨70, by decide +kernel⟩ (by decide +kernel),
      sha1Rotl_eq_rotateLeft 1 _ (by decide +kernel)]
    simp only [Nat.reduceSub]
    have h67 : (⟨67, by decide +kernel⟩ : Fin 80) = 67 := by decide +kernel
    have h62 : (⟨62, by decide +kernel⟩ : Fin 80) = 62 := by decide +kernel
    have h56 : (⟨56, by decide +kernel⟩ : Fin 80) = 56 := by decide +kernel
    have h54 : (⟨54, by decide +kernel⟩ : Fin 80) = 54 := by decide +kernel
    simp only [h67, h62, h56, h54]
  exact genericWords071 (fun n ↦ (workingAfter M H n).a) (scheduleWord M)
    hSchedule70 hf.stackPointer hw he
end Words071

end Block071

open Block071 in
theorem segment071 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x1033f3 0x103428
      cut071 cut072 := by
  have hout : ∀ d : Nat, d ≤ bytes071.length →
      0x1033f3 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      simp only [bytes071, List.length_cons, List.length_nil] at hd <;>
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  apply Segment.of_block (fun _ _ _ _ => effect071)
    (fun stack input H M => block071 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64
      0x33f3) bytes071,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect071_rip he
  · intro stack input H M s t _ hf _ he
    exact effect071_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect071_words hf hw he

theorem segments061_071 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x1031cd 0x103428 cut061 cut072 := by
  have h0 := segment061 boundary hOutside
  have h1 := h0.seq (segment062 boundary hOutside)
  have h2 := h1.seq (segment063 boundary hOutside)
  have h3 := h2.seq (segment064 boundary hOutside)
  have h4 := h3.seq (segment065 boundary hOutside)
  have h5 := h4.seq (segment066 boundary hOutside)
  have h6 := h5.seq (segment067 boundary hOutside)
  have h7 := h6.seq (segment068 boundary hOutside)
  have h8 := h7.seq (segment069 boundary hOutside)
  have h9 := h8.seq (segment070 boundary hOutside)
  have h10 := h9.seq (segment071 boundary hOutside)
  exact h10


end Sha1.Proofs.Compress.Machine
