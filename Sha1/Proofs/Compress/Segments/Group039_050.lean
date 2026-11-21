import Sha1.Proofs.Compress.Segments.Group045_050
import X86Proofs.Instructions.Mov.Triple
import Sha1.Proofs.Compress.Machine.Run
import Sha1.Proofs.Compress.Rounds.Scalar
import Sha1.Proofs.Common.Instructions.MovStore.Triple
import X86Proofs.Instructions.Mov.Generated.RM.Triple
import X86Proofs.Instructions.Lea.Generated.RM.Triple
import X86Proofs.Instructions.Add.Generated.AccImm32.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Add.Generated.Imm32.Triple

namespace Sha1.Proofs.Compress.Machine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Spec.Program
open Standards.NIST.SHA1 Sha1.Proofs.Compress.Rounds
open Sha1.Proofs.Common.Instructions.MovStore

attribute [local irreducible] workingAfter scheduleWord messageSchedule

def bytes039 : List UInt8 :=
  [0x41, 0xc1, 0xc1, 0x1e, 0x42, 0x8d, 0x04, 0x07, 0x48, 0x89, 0xf9, 0x48, 0x89, 0x7c, 0x24, 0x28, 0x45, 0x31, 0xc8, 0x45, 0x31, 0xd0, 0x41, 0x01, 0xe8, 0x89, 0xf2, 0xc1, 0xc2, 0x05, 0x41, 0xc1, 0xc2, 0x1e, 0x42, 0x8d, 0x3c, 0x02, 0x81, 0xc7, 0xa1, 0xeb, 0xd9, 0x6e, 0x44, 0x89, 0xd2, 0x44, 0x31, 0xca, 0x31, 0xf2, 0x01, 0xc2, 0x89, 0xf8, 0xc1, 0xc0, 0x05, 0x01, 0xd0, 0x05, 0xa1, 0xeb, 0xd9, 0x6e]

set_option maxRecDepth 2048 in
def effect039 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq ((rolR32Effect 0x102d54 4 9 30)) (leaR32Effect 0x102d58 4 0 (.sib 7 (some 8) 0 .none))) (movR64R64Effect 0x102d5c 1 7)) (movM64R64Effect 0x102d5f 7 (.sib 4 none 0 (.d8 0x28)))) (xorR32R32Effect 0x102d64 3 8 9)) (xorR32R32Effect 0x102d67 3 8 10)) (addR32R32Effect 0x102d6a 3 8 5)) (movR32R32Effect 0x102d6d 2 2 6)) (rolR32Effect 0x102d6f 3 2 5)) (rolR32Effect 0x102d72 4 10 30)) (leaR32Effect 0x102d76 4 7 (.sib 2 (some 8) 0 .none))) (addR32Imm32Effect 0x102d7a 6 7 0x6ed9eba1)) (movR32R32Effect 0x102d80 3 2 10)) (xorR32R32Effect 0x102d83 3 2 9)) (xorR32R32Effect 0x102d86 2 2 6)) (addR32R32Effect 0x102d88 2 2 0)) (movR32R32Effect 0x102d8a 2 0 7)) (rolR32Effect 0x102d8c 3 0 5)) (addR32R32Effect 0x102d8f 2 0 2)) (addEaxImm32Effect 0x102d91 0x6ed9eba1)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
private theorem block039_raw [Bindings] (boundary : ReturnBoundary) (stack input : BitVec 64)
    (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes039.length →
      0x102d54 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x102d54 ∧ FrameData stack input M s)
      (codeRange 0x102d54 bytes039) effect039 := by
  unfold bytes039 at hout ⊢
  sha1_run_begin (rol_r32_imm8_rex_effect_step 0x102d54 0x41 0xc1 0x1e (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (lea_r32_rex_effect_step 0x102d58 0x42 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) 0 (.sib 7 (some 8) 0 .none) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (mov_r64_r64_effect_step 0x102d5c 0x48 0xf9 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step 0x102d5f 0x48 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) 7 (.sib 4 none 0 (.d8 0x28)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102d64 0x45 0xc8 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102d67 0x45 0xd0 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (add_r32_r32_rex_effect_step 0x102d6a 0x41 0xe8 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (mov_r32_r32_effect_step 0x102d6d 0xf2 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (rol_r32_imm8_effect_step 0x102d6f 0xc2 0x5 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (rol_r32_imm8_rex_effect_step 0x102d72 0x41 0xc2 0x1e (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (lea_r32_rex_effect_step 0x102d76 0x42 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) 7 (.sib 2 (some 8) 0 .none) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (add_r32_imm32_effect_step 0x102d7a 0xc7 0x6ed9eba1 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x102d80 0x44 0xd2 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102d83 0x44 0xca (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (xor_r32_r32_effect_step 0x102d86 0xf2 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (add_r32_r32_effect_step 0x102d88 0xc2 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (mov_r32_r32_effect_step 0x102d8a 0xf8 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (rol_r32_imm8_effect_step 0x102d8c 0xc0 0x5 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (add_r32_r32_effect_step 0x102d8f 0xd0 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (add_eax_imm32_effect_step 0x102d91 0x6ed9eba1)
  sha1_run_finish [effect039]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
theorem block039 [Bindings] (boundary : ReturnBoundary) (stack input : BitVec 64)
    (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes039.length →
      0x102d54 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x102d54 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut039 stack input H M))
      (codeRange 0x102d54 bytes039) effect039 := by
  have hRaw := block039_raw boundary stack input M hout
  intro s hr hc hp
  exact hRaw s hr hc ⟨hp.1, hp.2.1⟩

private def genericCut039 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 3 : Operand 32), (W 34)⟩,
    ⟨(.reg 5 : Operand 32), ((W 38) + ((A 34)).rotateLeft 30)⟩,
    ⟨(.reg 6 : Operand 32), (A 38)⟩,
    ⟨(.reg 7 : Operand 32), (W 39)⟩,
    ⟨(.reg 8 : Operand 32), ((A 35)).rotateLeft 30⟩,
    ⟨(.reg 9 : Operand 32), (A 36)⟩,
    ⟨(.reg 10 : Operand 32), (A 37)⟩,
    ⟨(.reg 12 : Operand 32), (W 28)⟩,
    ⟨(.reg 13 : Operand 32), (W 29)⟩,
    ⟨(.reg 14 : Operand 32), (W 24)⟩,
    ⟨(.reg 15 : Operand 32), (W 33)⟩,
    ⟨(.mem (stack + 0) : Operand 32), (W 25)⟩,
    ⟨(.mem (stack + 4) : Operand 32), (W 37)⟩,
    ⟨(.mem (stack + 8) : Operand 32), (W 36)⟩,
    ⟨(.mem (stack + 12) : Operand 32), (W 32)⟩,
    ⟨(.mem (stack + 24) : Operand 32), (W 26)⟩,
    ⟨(.mem (stack + 32) : Operand 32), (W 38)⟩,
    ⟨(.mem (stack + 48) : Operand 32), (W 31)⟩,
    ⟨(.mem (stack + 56) : Operand 32), (W 35)⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), (W 30)⟩,
    ⟨(.mem (stack + 80) : Operand 32), (W 27)⟩,
    ⟨(.mem (stack + 88) : Operand 32), (W 34)⟩,
    ⟨(.mem (stack + 96) : Operand 32), (W 28)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

private def genericCut040 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), (A 40)⟩,
    ⟨(.reg 1 : Operand 32), (W 39)⟩,
    ⟨(.reg 3 : Operand 32), (W 34)⟩,
    ⟨(.reg 6 : Operand 32), (A 38)⟩,
    ⟨(.reg 7 : Operand 32), (A 39)⟩,
    ⟨(.reg 9 : Operand 32), ((A 36)).rotateLeft 30⟩,
    ⟨(.reg 10 : Operand 32), ((A 37)).rotateLeft 30⟩,
    ⟨(.reg 12 : Operand 32), (W 28)⟩,
    ⟨(.reg 13 : Operand 32), (W 29)⟩,
    ⟨(.reg 14 : Operand 32), (W 24)⟩,
    ⟨(.reg 15 : Operand 32), (W 33)⟩,
    ⟨(.mem (stack + 0) : Operand 32), (W 25)⟩,
    ⟨(.mem (stack + 4) : Operand 32), (W 37)⟩,
    ⟨(.mem (stack + 8) : Operand 32), (W 36)⟩,
    ⟨(.mem (stack + 12) : Operand 32), (W 32)⟩,
    ⟨(.mem (stack + 24) : Operand 32), (W 26)⟩,
    ⟨(.mem (stack + 32) : Operand 32), (W 38)⟩,
    ⟨(.mem (stack + 40) : Operand 32), (W 39)⟩,
    ⟨(.mem (stack + 48) : Operand 32), (W 31)⟩,
    ⟨(.mem (stack + 56) : Operand 32), (W 35)⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), (W 30)⟩,
    ⟨(.mem (stack + 80) : Operand 32), (W 27)⟩,
    ⟨(.mem (stack + 88) : Operand 32), (W 34)⟩,
    ⟨(.mem (stack + 96) : Operand 32), (W 28)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

theorem effect039_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (he : (effect039 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hfoot : ∀ c ∈ (effect039 s).components, c ∈ [.mem ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 40) 8, .reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect039
    iterate 19 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [leaR32Effect_components, addR32Imm32Effect_components, addEaxImm32Effect_components, addR32R32Effect_components, movM64R64Effect_components, movR32R32Effect_components, movR64R64Effect_components, rolR32Effect_components, xorR32R32Effect_components, List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and, forall_eq, or_true]
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

theorem effect039_rip {s t : RamState}
    (he : (effect039 s).Holds s t) :
    t.RIP = 0x102d96 := by
  exact he.rip.trans (by rfl)

section Words039

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
private theorem obs039 {s t : RamState} (he : (effect039 s).Holds s t) :
    Obs ((effect039 s).after s true) t := by
  apply he.obsAfter _ true
  apply Effect.Local.full
  unfold effect039
  repeat' first | (solve | x86_local) | apply Effect.Local.seq

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
private theorem rawR9_039 {s t : RamState}
    (v9 : BitVec 32)
    (h9 : (Operand.reg 9 : Operand 32).read s = v9)
    (he : (effect039 s).Holds s t) :
    (Operand.reg 9 : Operand 32).read t = v9.rotateLeft 30 := by
  sha1_norm at h9
  have ho := obs039 he
  simp only [← ho.read_reg]
  sha1_norm [effect039, h9,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, BitVec.add_zero, leaSpec, BitVec.signExtend_eq]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
private theorem rawR10_039 {s t : RamState}
    (v10 : BitVec 32)
    (h10 : (Operand.reg 10 : Operand 32).read s = v10)
    (he : (effect039 s).Holds s t) :
    (Operand.reg 10 : Operand 32).read t = v10.rotateLeft 30 := by
  sha1_norm at h10
  have ho := obs039 he
  simp only [← ho.read_reg]
  sha1_norm [effect039, h10,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, BitVec.add_zero, leaSpec, BitVec.signExtend_eq]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
private theorem rawR1_039 {s t : RamState}
    (v7 : BitVec 32)
    (h7 : (Operand.reg 7 : Operand 32).read s = v7)
    (he : (effect039 s).Holds s t) :
    (Operand.reg 1 : Operand 32).read t = v7 := by
  sha1_norm at h7
  have ho := obs039 he
  simp only [← ho.read_reg]
  sha1_norm [effect039, h7,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, BitVec.add_zero, leaSpec, BitVec.signExtend_eq]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
private theorem rawR7_039 {s t : RamState}
    (v5 v6 v8 v9 v10 : BitVec 32)
    (h5 : (Operand.reg 5 : Operand 32).read s = v5)
    (h6 : (Operand.reg 6 : Operand 32).read s = v6)
    (h8 : (Operand.reg 8 : Operand 32).read s = v8)
    (h9 : (Operand.reg 9 : Operand 32).read s = v9)
    (h10 : (Operand.reg 10 : Operand 32).read s = v10)
    (he : (effect039 s).Holds s t) :
    (Operand.reg 7 : Operand 32).read t = (v8 ^^^ v9.rotateLeft 30 ^^^ v10) + v5 + v6.rotateLeft 5 + 0x6ed9eba1 := by
  sha1_norm at h5 h6 h8 h9 h10
  have ho := obs039 he
  simp only [← ho.read_reg]
  sha1_norm [effect039, h5, h6, h8, h9, h10,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, BitVec.add_zero, leaSpec, BitVec.signExtend_eq]
  ac_rfl


set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
private theorem rawR0_039 {s t : RamState}
    (v5 v6 v7 v8 v9 v10 : BitVec 32)
    (h5 : (Operand.reg 5 : Operand 32).read s = v5)
    (h6 : (Operand.reg 6 : Operand 32).read s = v6)
    (h7 : (Operand.reg 7 : Operand 32).read s = v7)
    (h8 : (Operand.reg 8 : Operand 32).read s = v8)
    (h9 : (Operand.reg 9 : Operand 32).read s = v9)
    (h10 : (Operand.reg 10 : Operand 32).read s = v10)
    (he : (effect039 s).Holds s t) :
    (Operand.reg 0 : Operand 32).read t = ((v8 ^^^ v9.rotateLeft 30 ^^^ v10) + v5 + v6.rotateLeft 5 + 0x6ed9eba1).rotateLeft 5 +
      ((v10.rotateLeft 30 ^^^ v9.rotateLeft 30 ^^^ v6) + (v7 + v8)) + 0x6ed9eba1 := by
  sha1_norm at h5 h6 h7 h8 h9 h10
  have ho := obs039 he
  simp only [← ho.read_reg]
  sha1_norm [effect039, h5, h6, h7, h8, h9, h10,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, BitVec.add_zero, leaSpec, BitVec.signExtend_eq]
  ac_rfl


set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
private theorem rawM40_039 {s t : RamState} (stack : BitVec 64) (v7 : BitVec 32)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (h7 : (Operand.reg 7 : Operand 32).read s = v7)
    (he : (effect039 s).Holds s t) :
    (Operand.mem (stack + 40) : Operand 32).read t = v7 := by
  sha1_norm at hs h7
  have ho := obs039 he
  simp only [← ho.read_mem]
  sha1_norm [effect039, hs]
  rw [read32_memStore64_low]
  exact h7

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
private theorem genericWords039 {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32)
    (hWork39 : A 39 = (A 38).rotateLeft 5 +
      (A 37 ^^^ (A 36).rotateLeft 30 ^^^ (A 35).rotateLeft 30) +
      (A 34).rotateLeft 30 + K ⟨38, by decide⟩ + W 38)
    (hWork : A 40 = (A 39).rotateLeft 5 +
      (A 38 ^^^ (A 37).rotateLeft 30 ^^^ (A 36).rotateLeft 30) +
      (A 35).rotateLeft 30 + K ⟨39, by decide⟩ + W 39)
    {s t : RamState}
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hw : Write.AllHold s (genericCut039 stack input H A W))
    (he : (effect039 s).Holds s t) :
    Write.AllHold t (genericCut040 stack input H A W) := by
  simp only [genericCut039, Write.AllHold] at hw
  obtain ⟨h3,h5,h6,h7,h8,h9,h10,h12,h13,h14,h15,
    hM0,hM4,hM8,hM12,hM24,hM32,hM48,hM56,hM64,hM72,hM80,hM88,hM96,
    hM116,hM120,hM124,hM144,hM152⟩ := hw
  have hR1 := rawR1_039 (W 39) h7 he
  have hR9 := rawR9_039 (A 36) h9 he
  have hR10 := rawR10_039 (A 37) h10 he
  have hR7 := rawR7_039 (W 38 + (A 34).rotateLeft 30) (A 38)
    ((A 35).rotateLeft 30) (A 36) (A 37) h5 h6 h8 h9 h10 he
  have hMachine39 :
      ((A 35).rotateLeft 30 ^^^ (A 36).rotateLeft 30 ^^^ A 37) +
        (W 38 + (A 34).rotateLeft 30) + (A 38).rotateLeft 5 + 0x6ed9eba1 = A 39 := by
    rw [hWork39]
    change _ = _ + _ + _ + (0x6ed9eba1 : BitVec 32) + _
    ac_rfl
  rw [hMachine39] at hR7
  have hR0 := rawR0_039 (W 38 + (A 34).rotateLeft 30) (A 38) (W 39)
    ((A 35).rotateLeft 30) (A 36) (A 37) h5 h6 h7 h8 h9 h10 he
  rw [hMachine39] at hR0
  have hV0 : (Operand.reg 0 : Operand 32).read t = A 40 := by
    calc
      _ = _ := hR0
      _ = _ := by
        rw [hWork]
        change _ = _ + _ + _ + (0x6ed9eba1 : BitVec 32) + _
        ac_rfl
  have hM40 := rawM40_039 stack (W 39) hs h7 he
  have hfoot : ∀ c ∈ (effect039 s).components,
      c ∈ [.mem ((Operand.reg 4 : Operand 64).read s + 40) 8,
        .reg 0,.reg 1,.reg 2,.reg 7,.reg 8,.reg 9,.reg 10,.flags,.rip] := by
    unfold effect039
    iterate 19 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [movR64R64Effect_components, xorR32R32Effect_components,
       rolR32Effect_components, movR32R32Effect_components,
       leaR32Effect_components, movM64R64Effect_components,
       addR32R32Effect_components, addR32Imm32Effect_components, addEaxImm32Effect_components,
       List.mem_cons,List.not_mem_nil,or_false,or_imp,forall_and,forall_eq,or_true]
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose]
  have ha := he.agrees.mono hfoot
  rw [hs] at ha
  have hmem {n : Nat} (off : BitVec 64) (hb : OffsetsApart 40 8 off (n / 8))
      (hsize : 8 + n / 8 < 2 ^ 64) :
      (Operand.mem (stack+off) : Operand n).read t =
      (Operand.mem (stack+off) : Operand n).read s := by
    apply memLoad_congr
    intro i hi
    apply congrArg (fun b : Option UInt8 => b.getD 0)
    apply ha.byte
    intro c hc hCov
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨j,hj,heq⟩ := hCov
      exact hb.ne stack hj hi hsize heq.symm
    all_goals exact hCov.elim
  simp only [genericCut040, Write.AllHold]
  refine ⟨?f0, ?f1, ?f2, ?f3, ?f4, ?f5, ?f6, ?f7, ?f8, ?f9, ?f10, ?f11, ?f12, ?f13, ?f14, ?f15, ?f16, ?f17, ?f18, ?f19, ?f20, ?f21, ?f22, ?f23, ?f24, ?f25, ?f26, ?f27, ?f28, ?f29⟩
  case f0 => exact hV0
  case f1 => exact hR1
  case f2 => exact (ha.read (by simp)).trans h3
  case f3 => exact (ha.read (by simp)).trans h6
  case f4 => exact hR7
  case f5 => exact hR9
  case f6 => exact hR10
  case f7 => exact (ha.read (by simp)).trans h12
  case f8 => exact (ha.read (by simp)).trans h13
  case f9 => exact (ha.read (by simp)).trans h14
  case f10 => exact (ha.read (by simp)).trans h15
  case f11 => exact (hmem 0 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM0
  case f12 => exact (hmem 4 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM4
  case f13 => exact (hmem 8 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM8
  case f14 => exact (hmem 12 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM12
  case f15 => exact (hmem 24 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM24
  case f16 => exact (hmem 32 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM32
  case f17 => exact hM40
  case f18 => exact (hmem 48 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM48
  case f19 => exact (hmem 56 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM56
  case f20 => exact (hmem 64 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM64
  case f21 => exact (hmem 72 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM72
  case f22 => exact (hmem 80 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM80
  case f23 => exact (hmem 88 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM88
  case f24 => exact (hmem 96 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM96
  case f25 => exact (hmem 116 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM116
  case f26 => exact (hmem 120 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM120
  case f27 => exact (hmem 124 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM124
  case f28 => exact (hmem 144 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM144
  case f29 => exact (hmem 152 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM152

theorem effect039_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16}
    {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut039 stack input H M))
    (he : (effect039 s).Holds s t) :
    Write.AllHold t (cut040 stack input H M) := by
  have hWork39 : (workingAfter M H 39).a =
      ((workingAfter M H 38).a).rotateLeft 5 +
        (((workingAfter M H 37).a) ^^^ ((workingAfter M H 36).a).rotateLeft 30 ^^^
          ((workingAfter M H 35).a).rotateLeft 30) +
        ((workingAfter M H 34).a).rotateLeft 30 + K ⟨38, by decide⟩ + scheduleWord M 38 := by
    rw [workingAfter_step_a_values M H 34 (by decide)]
    rw [sha1_f_parity_first (by decide) (by decide)]
    simp only [Parity]
    ac_rfl
  have hWork : (workingAfter M H 40).a =
      ((workingAfter M H 39).a).rotateLeft 5 +
        (((workingAfter M H 38).a) ^^^ ((workingAfter M H 37).a).rotateLeft 30 ^^^
          ((workingAfter M H 36).a).rotateLeft 30) +
        ((workingAfter M H 35).a).rotateLeft 30 + K ⟨39, by decide⟩ + scheduleWord M 39 := by
    rw [workingAfter_step_a_values M H 35 (by decide)]
    rw [sha1_f_parity_first (by decide) (by decide)]
    simp only [Parity]
    ac_rfl
  let A := fun n ↦ (workingAfter M H n).a
  let W := scheduleWord M
  have hpre : Write.AllHold s (genericCut039 stack input H A W) := by
    simpa (config := {implicitDefEqProofs := false, decide := true}) only
      [genericCut039, A, W, cut039] using hw
  have hraw := genericWords039 A W hWork39 hWork hf.stackPointer hpre he
  change Write.AllHold t (cut040 stack input H M) at hraw
  exact hraw
end Words039

theorem segment039 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x102d54 0x102d96
      cut039 cut040 := by
  have hout : ∀ d : Nat, d ≤ bytes039.length →
      0x102d54 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      (simp only [bytes039, List.length_cons, List.length_nil] at hd;
       simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
  apply Segment.of_block (fun _ _ _ _ => effect039)
    (fun stack input H M => block039 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64
      0x2d54) bytes039,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect039_rip he
  · intro stack input H M s t _ hf _ he
    exact effect039_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect039_words hf hw he


def bytes040 : List UInt8 :=
  [0xc1, 0xc6, 0x1e, 0x89, 0xf2, 0x44, 0x31, 0xd2, 0x21, 0xfa, 0x41, 0x89, 0xf0, 0x45, 0x21, 0xd0, 0x41, 0x31, 0xd0, 0x48, 0x8b, 0x6c, 0x24, 0x18, 0x41, 0x31, 0xee, 0x44, 0x33, 0x74, 0x24, 0x0c, 0x44, 0x33, 0x74, 0x24, 0x04, 0x41, 0xd1, 0xc6, 0x45, 0x01, 0xf1, 0x45, 0x01, 0xc1, 0x89, 0xc2, 0xc1, 0xc2, 0x05, 0x44, 0x01, 0xca, 0x81, 0xc2, 0xdc, 0xbc, 0x1b, 0x8f]

set_option maxRecDepth 2048 in
def effect040 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq ((rolR32Effect 0x102d96 3 6 30)) (movR32R32Effect 0x102d99 2 2 6)) (xorR32R32Effect 0x102d9b 3 2 10)) (andR32R32Effect 0x102d9e 2 2 7)) (movR32R32Effect 0x102da0 3 8 6)) (andR32R32Effect 0x102da3 3 8 10)) (xorR32R32Effect 0x102da6 3 8 2)) (movR64M64Effect 0x102da9 5 (.sib 4 none 0 (.d8 0x18)))) (xorR32R32Effect 0x102dae 3 14 5)) (xorR32M32Effect 0x102db1 14 (.sib 4 none 0 (.d8 0xc)))) (xorR32M32Effect 0x102db6 14 (.sib 4 none 0 (.d8 0x4)))) (rolR32Effect 0x102dbb 3 14 1)) (addR32R32Effect 0x102dbe 3 9 14)) (addR32R32Effect 0x102dc1 3 9 8)) (movR32R32Effect 0x102dc4 2 2 0)) (rolR32Effect 0x102dc6 3 2 5)) (addR32R32Effect 0x102dc9 3 2 9)) (addR32Imm32Effect 0x102dcc 6 2 0x8f1bbcdc)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
theorem block040 [Bindings] (boundary : ReturnBoundary) (stack input : BitVec 64)
    (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes040.length →
      0x102d96 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x102d96 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut040 stack input H M))
      (codeRange 0x102d96 bytes040) effect040 := by
  unfold bytes040 at hout ⊢
  sha1_run_begin (rol_r32_imm8_effect_step 0x102d96 0xc6 0x1e (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (mov_r32_r32_effect_step 0x102d99 0xf2 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102d9b 0x44 0xd2 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (and_r32_r32_effect_step 0x102d9e 0xfa (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x102da0 0x41 0xf0 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (and_r32_r32_rex_effect_step 0x102da3 0x45 0xd0 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102da6 0x41 0xd0 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (mov_r64_m64_effect_step 0x102da9 0x48 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) 5 (.sib 4 none 0 (.d8 0x18)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102dae 0x41 0xee (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (xor_r32_m32_effect_step 0x102db1 0x44 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) 6 (.sib 4 none 0 (.d8 0xc)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (xor_r32_m32_effect_step 0x102db6 0x44 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) 6 (.sib 4 none 0 (.d8 0x4)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (rol_r32_one_rex_effect_step 0x102dbb 0x41 0xc6 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (add_r32_r32_rex_effect_step 0x102dbe 0x45 0xf1 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (add_r32_r32_rex_effect_step 0x102dc1 0x45 0xc1 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (mov_r32_r32_effect_step 0x102dc4 0xc2 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (rol_r32_imm8_effect_step 0x102dc6 0xc2 0x5 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (add_r32_r32_rex_effect_step 0x102dc9 0x44 0xca (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (add_r32_imm32_effect_step 0x102dcc 0xc2 0x8f1bbcdc (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_finish [effect040]


private def genericCut041 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), (A 40)⟩,
    ⟨(.reg 1 : Operand 32), (W 39)⟩,
    ⟨(.reg 2 : Operand 32), (A 41)⟩,
    ⟨(.reg 3 : Operand 32), (W 34)⟩,
    ⟨(.reg 5 : Operand 32), (W 26)⟩,
    ⟨(.reg 6 : Operand 32), ((A 38)).rotateLeft 30⟩,
    ⟨(.reg 7 : Operand 32), (A 39)⟩,
    ⟨(.reg 10 : Operand 32), ((A 37)).rotateLeft 30⟩,
    ⟨(.reg 12 : Operand 32), (W 28)⟩,
    ⟨(.reg 13 : Operand 32), (W 29)⟩,
    ⟨(.reg 14 : Operand 32), (W 40)⟩,
    ⟨(.reg 15 : Operand 32), (W 33)⟩,
    ⟨(.mem (stack + 0) : Operand 32), (W 25)⟩,
    ⟨(.mem (stack + 4) : Operand 32), (W 37)⟩,
    ⟨(.mem (stack + 8) : Operand 32), (W 36)⟩,
    ⟨(.mem (stack + 12) : Operand 32), (W 32)⟩,
    ⟨(.mem (stack + 32) : Operand 32), (W 38)⟩,
    ⟨(.mem (stack + 40) : Operand 32), (W 39)⟩,
    ⟨(.mem (stack + 48) : Operand 32), (W 31)⟩,
    ⟨(.mem (stack + 56) : Operand 32), (W 35)⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), (W 30)⟩,
    ⟨(.mem (stack + 80) : Operand 32), (W 27)⟩,
    ⟨(.mem (stack + 88) : Operand 32), (W 34)⟩,
    ⟨(.mem (stack + 96) : Operand 32), (W 28)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

theorem effect040_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (_hf : FrameData stack input M s)
    (he : (effect040 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hfoot : ∀ c ∈ (effect040 s).components, c ∈ [.reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect040
    iterate 17 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [addR32Imm32Effect_components, addR32R32Effect_components, andR32R32Effect_components, movR32R32Effect_components, movR64M64Effect_components, rolR32Effect_components, xorR32M32Effect_components, xorR32R32Effect_components, List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and, forall_eq]
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

theorem effect040_rip {s t : RamState}
    (he : (effect040 s).Holds s t) :
    t.RIP = 0x102dd2 := by
  exact he.rip.trans (by rfl)

section Words040




private theorem scheduleWord_40_40 (M : Vector (BitVec 32) 16) :
    scheduleWord M 40 = (scheduleWord M 37 ^^^ scheduleWord M 32 ^^^
      scheduleWord M 26 ^^^ scheduleWord M 24).rotateLeft 1 := by
  change scheduleWord M (⟨40, by decide⟩ : Fin 80) = _
  rw [scheduleWord_recurrence M ⟨40, by decide⟩ (by decide)]
  simp only [Nat.reduceSub]
  rw [sha1Rotl_eq_rotateLeft 1 _ (by decide)]
  rfl

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
private theorem obs040 {s t : RamState} (he : (effect040 s).Holds s t) :
    Obs ((effect040 s).after s true) t := by
  apply he.obsAfter _ true
  apply Effect.Local.full
  unfold effect040
  repeat' first | (solve | x86_local) | apply Effect.Local.seq

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
private theorem rawR6_040 {s t : RamState}
    (v6 : BitVec 32)
    (h6 : (Operand.reg 6 : Operand 32).read s = v6)
    (he : (effect040 s).Holds s t) :
    (Operand.reg 6 : Operand 32).read t = v6.rotateLeft 30 := by
  sha1_norm at h6
  have ho := obs040 he
  simp only [← ho.read_reg]
  sha1_norm [effect040, h6,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, BitVec.add_zero, leaSpec, BitVec.signExtend_eq]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
private theorem rawR5_040 {s t : RamState}
    (m24 : BitVec 64) (stack : BitVec 64)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hm24 : (Operand.mem (stack + 24) : Operand 64).read s = m24)
    (he : (effect040 s).Holds s t) :
    (Operand.reg 5 : Operand 32).read t = m24.setWidth 32 := by
  sha1_norm at hs hm24
  have ho := obs040 he
  simp only [← ho.read_reg]
  sha1_norm [effect040, hs, hm24,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, BitVec.add_zero, leaSpec, BitVec.signExtend_eq]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
private theorem rawR14_040 {s t : RamState}
    (v14 : BitVec 32)
    (m24 : BitVec 64) (m4 m12 : BitVec 32) (stack : BitVec 64)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (h14 : (Operand.reg 14 : Operand 32).read s = v14)
    (hm24 : (Operand.mem (stack + 24) : Operand 64).read s = m24)
    (hm4 : (Operand.mem (stack + 4) : Operand 32).read s = m4)
    (hm12 : (Operand.mem (stack + 12) : Operand 32).read s = m12)
    (he : (effect040 s).Holds s t) :
    (Operand.reg 14 : Operand 32).read t = (v14 ^^^ m24.setWidth 32 ^^^ m12 ^^^ m4).rotateLeft 1 := by
  sha1_norm at hs h14 hm24 hm4 hm12
  have ho := obs040 he
  simp only [← ho.read_reg]
  sha1_norm [effect040, hs, h14, hm24, hm4, hm12,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, BitVec.add_zero, leaSpec, BitVec.signExtend_eq]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
private theorem rawR2_040 {s t : RamState}
    (v0 v6 v7 v9 v10 v14 : BitVec 32)
    (m24 : BitVec 64) (m4 m12 : BitVec 32) (stack : BitVec 64)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (h0 : (Operand.reg 0 : Operand 32).read s = v0)
    (h6 : (Operand.reg 6 : Operand 32).read s = v6)
    (h7 : (Operand.reg 7 : Operand 32).read s = v7)
    (h9 : (Operand.reg 9 : Operand 32).read s = v9)
    (h10 : (Operand.reg 10 : Operand 32).read s = v10)
    (h14 : (Operand.reg 14 : Operand 32).read s = v14)
    (hm24 : (Operand.mem (stack + 24) : Operand 64).read s = m24)
    (hm4 : (Operand.mem (stack + 4) : Operand 32).read s = m4)
    (hm12 : (Operand.mem (stack + 12) : Operand 32).read s = m12)
    (he : (effect040 s).Holds s t) :
    (Operand.reg 2 : Operand 32).read t = v0.rotateLeft 5 + (v9 + (v14 ^^^ m24.setWidth 32 ^^^ m12 ^^^ m4).rotateLeft 1 + (v6.rotateLeft 30 &&& v10 ^^^ ((v6.rotateLeft 30 ^^^ v10) &&& v7))) + 0x8f1bbcdc := by
  sha1_norm at hs h0 h6 h7 h9 h10 h14 hm24 hm4 hm12
  have ho := obs040 he
  simp only [← ho.read_reg]
  sha1_norm [effect040, hs, h0, h6, h7, h9, h10, h14, hm24, hm4, hm12,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, BitVec.add_zero, leaSpec, BitVec.signExtend_eq]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
private theorem genericWords040 {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32)
    (hWork : A 41 = (A 40).rotateLeft 5 +
      (((A 39) &&& ((A 37).rotateLeft 30)) ^^^
        ((A 39) &&& ((A 38).rotateLeft 30)) ^^^
        (((A 37).rotateLeft 30) &&& ((A 38).rotateLeft 30))) +
      (A 36).rotateLeft 30 + K ⟨40, by decide⟩ + W 40)
    (hSched40 : W 40 = (W 37 ^^^ W 32 ^^^
      W 26 ^^^ W 24).rotateLeft 1)
    {s t : RamState}
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hw : Write.AllHold s (genericCut040 stack input H A W))
    (he : (effect040 s).Holds s t) :
    Write.AllHold t (genericCut041 stack input H A W) := by
  simp only [genericCut040, Write.AllHold] at hw
  obtain ⟨h0,h1,h3,h6,h7,h9,h10,h12,h13,h14,h15,
    hM0,hM4,hM8,hM12,hM24,hM32,hM40,hM48,hM56,hM64,hM72,hM80,hM88,hM96,
    hM116,hM120,hM124,hM144,hM152⟩ := hw
  have lo24 := (read32_of_read64_low
    (s := s) (a := stack + 24)
    (v := (Operand.mem (stack + 24) : Operand 64).read s) rfl).symm.trans hM24
  have hR6 := rawR6_040 (A 38) h6 he
  have hR5 := rawR5_040 ((Operand.mem (stack + 24) : Operand 64).read s)
    stack hs rfl he
  rw [lo24] at hR5
  have hR14 := rawR14_040 (W 24) ((Operand.mem (stack + 24) : Operand 64).read s)
    (W 37) (W 32) stack hs h14 rfl hM4 hM12 he
  have hSchedule : (W 24 ^^^ W 26 ^^^ W 32 ^^^ W 37).rotateLeft 1 = W 40 := by
    rw [hSched40]
    congr 1
    ac_rfl
  rw [lo24, hSchedule] at hR14
  have hR2 := rawR2_040 (A 40) (A 38) (A 39) ((A 36).rotateLeft 30)
    ((A 37).rotateLeft 30) (W 24)
    ((Operand.mem (stack + 24) : Operand 64).read s) (W 37) (W 32)
    stack hs h0 h6 h7 h9 h10 h14 rfl hM4 hM12 he
  rw [lo24, hSchedule] at hR2
  have hMaj (a b c : BitVec 32) :
      (b &&& c) ^^^ ((b ^^^ c) &&& a) =
      (a &&& c) ^^^ (a &&& b) ^^^ (c &&& b) := by
    rw [← sha1Maj_eq_xor]
    simp only [Standards.NIST.SHA2.SHA256.Maj, BitVec.and_comm]
    all_goals ac_rfl
  rw [hMaj] at hR2
  have hV2 : (Operand.reg 2 : Operand 32).read t = A 41 := by
    calc
      _ = _ := hR2
      _ = _ := by
        rw [hWork]
        change _ = _ + _ + _ + (0x8f1bbcdc : BitVec 32) + _
        ac_rfl
  have hfoot : ∀ c ∈ (effect040 s).components,
      c ∈ [.reg 2,.reg 5,.reg 6,.reg 8,.reg 9,.reg 14,.flags,.rip] := by
    unfold effect040
    iterate 17 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [movR64M64Effect_components, xorR32R32Effect_components, xorR32M32Effect_components,
       rolR32Effect_components, movR32R32Effect_components, andR32R32Effect_components,
       addR32R32Effect_components, addR32Imm32Effect_components, 
       List.mem_cons,List.not_mem_nil,or_false,or_imp,forall_and,forall_eq]
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose]
  have ha := he.agrees.mono hfoot
  have hExt : t.external = s.external := by
    apply ha.external
    intro c hc x
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact fun h => h.elim
  have hmem {n : Nat} (a : BitVec 64) :
      (Operand.mem a : Operand n).read t = (Operand.mem a : Operand n).read s := by
    change memLoad t.external a n = memLoad s.external a n
    rw [hExt]
  simp only [genericCut041, Write.AllHold]
  refine ⟨?f0, ?f1, ?f2, ?f3, ?f4, ?f5, ?f6, ?f7, ?f8, ?f9, ?f10, ?f11, ?f12, ?f13, ?f14, ?f15, ?f16, ?f17, ?f18, ?f19, ?f20, ?f21, ?f22, ?f23, ?f24, ?f25, ?f26, ?f27, ?f28, ?f29⟩
  case f0 => exact (ha.read (by simp)).trans h0
  case f1 => exact (ha.read (by simp)).trans h1
  case f2 => exact hV2
  case f3 => exact (ha.read (by simp)).trans h3
  case f4 => exact hR5
  case f5 => exact hR6
  case f6 => exact (ha.read (by simp)).trans h7
  case f7 => exact (ha.read (by simp)).trans h10
  case f8 => exact (ha.read (by simp)).trans h12
  case f9 => exact (ha.read (by simp)).trans h13
  case f10 => exact hR14
  case f11 => exact (ha.read (by simp)).trans h15
  case f12 => exact (hmem (stack + 0)).trans hM0
  case f13 => exact (hmem (stack + 4)).trans hM4
  case f14 => exact (hmem (stack + 8)).trans hM8
  case f15 => exact (hmem (stack + 12)).trans hM12
  case f16 => exact (hmem (stack + 32)).trans hM32
  case f17 => exact (hmem (stack + 40)).trans hM40
  case f18 => exact (hmem (stack + 48)).trans hM48
  case f19 => exact (hmem (stack + 56)).trans hM56
  case f20 => exact (hmem (stack + 64)).trans hM64
  case f21 => exact (hmem (stack + 72)).trans hM72
  case f22 => exact (hmem (stack + 80)).trans hM80
  case f23 => exact (hmem (stack + 88)).trans hM88
  case f24 => exact (hmem (stack + 96)).trans hM96
  case f25 => exact (hmem (stack + 116)).trans hM116
  case f26 => exact (hmem (stack + 120)).trans hM120
  case f27 => exact (hmem (stack + 124)).trans hM124
  case f28 => exact (hmem (stack + 144)).trans hM144
  case f29 => exact (hmem (stack + 152)).trans hM152

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
private theorem work040_actual (M : Vector (BitVec 32) 16)
    (H : Vector (BitVec 32) 5) :
    (workingAfter M H 41).a =
      ((workingAfter M H 40).a).rotateLeft 5 +
        (((workingAfter M H 39).a &&& ((workingAfter M H 37).a).rotateLeft 30) ^^^
          ((workingAfter M H 39).a &&& ((workingAfter M H 38).a).rotateLeft 30) ^^^
          (((workingAfter M H 37).a).rotateLeft 30 &&& ((workingAfter M H 38).a).rotateLeft 30)) +
        ((workingAfter M H 36).a).rotateLeft 30 + K ⟨40, by decide⟩ + scheduleWord M 40 := by
  rw [workingAfter_step_a_values M H 36 (by decide)]
  rw [sha1_f_majority (t := ⟨40, by decide⟩) (by decide) (by decide)]
  have hMaj (x y z : BitVec 32) :
      Standards.NIST.SHA2.SHA256.Maj x y z = (x &&& y) ^^^ ((x ^^^ y) &&& z) :=
    sha1Maj_eq_xor x y z
  have hMajAlt (x y z : BitVec 32) :
      (x &&& y) ^^^ ((x ^^^ y) &&& z) =
        (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z) := by
    exact (sha1Maj_eq_xor x y z).symm
  have hK : K (⟨40, by decide⟩ : Fin 80) = 0x8f1bbcdc := by decide
  rw [hMaj, hMajAlt, hK]
  ac_rfl

theorem effect040_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16}
    {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut040 stack input H M))
    (he : (effect040 s).Holds s t) :
    Write.AllHold t (cut041 stack input H M) := by
  have hWork := work040_actual M H
  have hSched40 := scheduleWord_40_40 M
  let A := fun n ↦ (workingAfter M H n).a
  let W := scheduleWord M
  have hpre : Write.AllHold s (genericCut040 stack input H A W) := by
    simpa (config := {implicitDefEqProofs := false, decide := true}) only
      [genericCut040, A, W, cut040] using hw
  have hraw := genericWords040 A W hWork hSched40 hf.stackPointer hpre he
  change Write.AllHold t (cut041 stack input H M) at hraw
  exact hraw
end Words040

theorem segment040 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x102d96 0x102dd2
      cut040 cut041 := by
  have hout : ∀ d : Nat, d ≤ bytes040.length →
      0x102d96 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      (simp only [bytes040, List.length_cons, List.length_nil] at hd;
       simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
  apply Segment.of_block (fun _ _ _ _ => effect040)
    (fun stack input H M => block040 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64
      0x2d96) bytes040,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect040_rip he
  · intro stack input H M s t _ hf _ he
    exact effect040_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect040_words hf hw he


def bytes041 : List UInt8 :=
  [0x44, 0x31, 0xe5, 0x31, 0xdd, 0x31, 0xcd, 0xd1, 0xc5, 0x48, 0x89, 0x6c, 0x24, 0x18, 0xc1, 0xc7, 0x1e, 0x41, 0x89, 0xf9]

set_option maxRecDepth 2048 in
def effect041 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq ((xorR32R32Effect 0x102dd2 3 5 12)) (xorR32R32Effect 0x102dd5 2 5 3)) (xorR32R32Effect 0x102dd7 2 5 1)) (rolR32Effect 0x102dd9 2 5 1)) (movM64R64Effect 0x102ddb 5 (.sib 4 none 0 (.d8 0x18)))) (rolR32Effect 0x102de0 3 7 30)) (movR32R32Effect 0x102de3 3 9 7)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
theorem block041 [Bindings] (boundary : ReturnBoundary) (stack input : BitVec 64)
    (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes041.length →
      0x102dd2 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x102dd2 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut041 stack input H M))
      (codeRange 0x102dd2 bytes041) effect041 := by
  unfold bytes041 at hout ⊢
  sha1_run_begin (xor_r32_r32_rex_effect_step 0x102dd2 0x44 0xe5 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (xor_r32_r32_effect_step 0x102dd5 0xdd (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (xor_r32_r32_effect_step 0x102dd7 0xcd (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (rol_r32_one_effect_step 0x102dd9 0xc5 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step 0x102ddb 0x48 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) 5 (.sib 4 none 0 (.d8 0x18)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (rol_r32_imm8_effect_step 0x102de0 0xc7 0x1e (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x102de3 0x41 0xf9 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_finish [effect041]


private def genericCut042 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), (A 40)⟩,
    ⟨(.reg 2 : Operand 32), (A 41)⟩,
    ⟨(.reg 5 : Operand 32), (W 42)⟩,
    ⟨(.reg 6 : Operand 32), ((A 38)).rotateLeft 30⟩,
    ⟨(.reg 7 : Operand 32), ((A 39)).rotateLeft 30⟩,
    ⟨(.reg 9 : Operand 32), ((A 39)).rotateLeft 30⟩,
    ⟨(.reg 10 : Operand 32), ((A 37)).rotateLeft 30⟩,
    ⟨(.reg 13 : Operand 32), (W 29)⟩,
    ⟨(.reg 14 : Operand 32), (W 40)⟩,
    ⟨(.reg 15 : Operand 32), (W 33)⟩,
    ⟨(.mem (stack + 0) : Operand 32), (W 25)⟩,
    ⟨(.mem (stack + 4) : Operand 32), (W 37)⟩,
    ⟨(.mem (stack + 8) : Operand 32), (W 36)⟩,
    ⟨(.mem (stack + 12) : Operand 32), (W 32)⟩,
    ⟨(.mem (stack + 24) : Operand 32), (W 42)⟩,
    ⟨(.mem (stack + 32) : Operand 32), (W 38)⟩,
    ⟨(.mem (stack + 40) : Operand 32), (W 39)⟩,
    ⟨(.mem (stack + 48) : Operand 32), (W 31)⟩,
    ⟨(.mem (stack + 56) : Operand 32), (W 35)⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), (W 30)⟩,
    ⟨(.mem (stack + 80) : Operand 32), (W 27)⟩,
    ⟨(.mem (stack + 88) : Operand 32), (W 34)⟩,
    ⟨(.mem (stack + 96) : Operand 32), (W 28)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

theorem effect041_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (he : (effect041 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hfoot : ∀ c ∈ (effect041 s).components, c ∈ [.mem ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 24) 8, .reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect041
    iterate 6 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [movM64R64Effect_components, movR32R32Effect_components, rolR32Effect_components, xorR32R32Effect_components, List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and, forall_eq, or_true]
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

theorem effect041_rip {s t : RamState}
    (he : (effect041 s).Holds s t) :
    t.RIP = 0x102de6 := by
  exact he.rip.trans (by rfl)

section Words041




private theorem scheduleWord_42_41 (M : Vector (BitVec 32) 16) :
    scheduleWord M 42 = (scheduleWord M 39 ^^^ scheduleWord M 34 ^^^
      scheduleWord M 28 ^^^ scheduleWord M 26).rotateLeft 1 := by
  change scheduleWord M (⟨42, by decide⟩ : Fin 80) = _
  rw [scheduleWord_recurrence M ⟨42, by decide⟩ (by decide)]
  simp only [Nat.reduceSub]
  rw [sha1Rotl_eq_rotateLeft 1 _ (by decide)]
  rfl

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
private theorem obs041 {s t : RamState} (he : (effect041 s).Holds s t) :
    Obs ((effect041 s).after s true) t := by
  apply he.obsAfter _ true
  apply Effect.Local.full
  unfold effect041
  repeat' first | (solve | x86_local) | apply Effect.Local.seq

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
private theorem rawR7_041 {s t : RamState} (v7 : BitVec 32)
    (h7 : (Operand.reg 7 : Operand 32).read s = v7)
    (he : (effect041 s).Holds s t) :
    (Operand.reg 7 : Operand 32).read t = v7.rotateLeft 30 := by
  sha1_norm at h7
  have ho := obs041 he
  simp only [← ho.read_reg]
  sha1_norm [effect041, h7,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
private theorem rawR9_041 {s t : RamState} (v7 : BitVec 32)
    (h7 : (Operand.reg 7 : Operand 32).read s = v7)
    (he : (effect041 s).Holds s t) :
    (Operand.reg 9 : Operand 32).read t = v7.rotateLeft 30 := by
  sha1_norm at h7
  have ho := obs041 he
  simp only [← ho.read_reg]
  sha1_norm [effect041, h7,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
private theorem rawR5_041 {s t : RamState} (v1 v3 v5 v12 : BitVec 32)
    (h1 : (Operand.reg 1 : Operand 32).read s = v1)
    (h3 : (Operand.reg 3 : Operand 32).read s = v3)
    (h5 : (Operand.reg 5 : Operand 32).read s = v5)
    (h12 : (Operand.reg 12 : Operand 32).read s = v12)
    (he : (effect041 s).Holds s t) :
    (Operand.reg 5 : Operand 32).read t = (v5 ^^^ v12 ^^^ v3 ^^^ v1).rotateLeft 1 := by
  sha1_norm at h1 h3 h5 h12
  have ho := obs041 he
  simp only [← ho.read_reg]
  sha1_norm [effect041, h1, h3, h5, h12,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
private theorem rawM24_041 {s t : RamState} (stack : BitVec 64)
    (v1 v3 v5 v12 : BitVec 32)
    (h1 : (Operand.reg 1 : Operand 32).read s = v1)
    (h3 : (Operand.reg 3 : Operand 32).read s = v3)
    (h5 : (Operand.reg 5 : Operand 32).read s = v5)
    (h12 : (Operand.reg 12 : Operand 32).read s = v12)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (he : (effect041 s).Holds s t) :
    (Operand.mem (stack + 24) : Operand 32).read t =
      (v5 ^^^ v12 ^^^ v3 ^^^ v1).rotateLeft 1 := by
  sha1_norm at hs h1 h3 h5 h12
  have ho := obs041 he
  simp only [← ho.read_mem]
  sha1_norm [effect041, hs, h1, h3, h5, h12]
  rw [read32_memStore64_low]
  rw [extractLsb'_zero_eq_setWidth _ 32 (by decide)]
  sha1_norm [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
private theorem genericWords041 {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32)
    (hSched42 : W 42 = (W 39 ^^^ W 34 ^^^ W 28 ^^^ W 26).rotateLeft 1)
    {s t : RamState}
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hw : Write.AllHold s (genericCut041 stack input H A W))
    (he : (effect041 s).Holds s t) :
    Write.AllHold t (genericCut042 stack input H A W) := by
  simp only [genericCut041, Write.AllHold] at hw
  obtain ⟨h0,h1,h2,h3,h5,h6,h7,h10,h12,h13,h14,h15,
    hM0,hM4,hM8,hM12,hM32,hM40,hM48,hM56,hM64,hM72,hM80,hM88,hM96,
    hM116,hM120,hM124,hM144,hM152⟩ := hw
  have hR5 := rawR5_041 (W 39) (W 34) (W 26) (W 28) h1 h3 h5 h12 he
  have hR7 := rawR7_041 (A 39) h7 he
  have hR9 := rawR9_041 (A 39) h7 he
  have hM24 := rawM24_041 stack (W 39) (W 34) (W 26) (W 28) h1 h3 h5 h12 hs he
  have hSchedule : (W 26 ^^^ W 28 ^^^ W 34 ^^^ W 39).rotateLeft 1 = W 42 := by
    rw [hSched42]
    congr 1
    ac_rfl
  rw [hSchedule] at hR5 hM24
  have hfoot : ∀ c ∈ (effect041 s).components,
      c ∈ [.mem ((Operand.reg 4 : Operand 64).read s + 24) 8,
        .reg 5, .reg 7, .reg 9, .flags, .rip] := by
    unfold effect041
    iterate 6 apply components_seq_of
    all_goals sha1_norm
      [movM64R64Effect_components, movR32R32Effect_components,
       rolR32Effect_components, xorR32R32Effect_components,
       List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and, forall_eq, or_true]
  have ha := he.agrees.mono hfoot
  rw [hs] at ha
  have hmem {n : Nat} (off : BitVec 64) (hb : OffsetsApart 24 8 off (n / 8))
      (hsize : 8 + n / 8 < 2 ^ 64) :
      (Operand.mem (stack + off) : Operand n).read t =
      (Operand.mem (stack + off) : Operand n).read s := by
    apply memLoad_congr
    intro i hi
    apply congrArg (fun b : Option UInt8 => b.getD 0)
    apply ha.byte
    intro c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨j,hj,heq⟩ := hCov
      exact hb.ne stack hj hi hsize heq.symm
    all_goals exact hCov.elim
  simp only [genericCut042, Write.AllHold]
  refine ⟨?f0, ?f1, ?f2, ?f3, ?f4, ?f5, ?f6, ?f7, ?f8, ?f9, ?f10, ?f11, ?f12, ?f13, ?f14, ?f15, ?f16, ?f17, ?f18, ?f19, ?f20, ?f21, ?f22, ?f23, ?f24, ?f25, ?f26, ?f27, ?f28⟩
  case f0 => exact (ha.read (by simp)).trans h0
  case f1 => exact (ha.read (by simp)).trans h2
  case f2 => exact hR5
  case f3 => exact (ha.read (by simp)).trans h6
  case f4 => exact hR7
  case f5 => exact hR9
  case f6 => exact (ha.read (by simp)).trans h10
  case f7 => exact (ha.read (by simp)).trans h13
  case f8 => exact (ha.read (by simp)).trans h14
  case f9 => exact (ha.read (by simp)).trans h15
  case f10 => exact (hmem 0 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM0
  case f11 => exact (hmem 4 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM4
  case f12 => exact (hmem 8 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM8
  case f13 => exact (hmem 12 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM12
  case f14 => exact hM24
  case f15 => exact (hmem 32 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM32
  case f16 => exact (hmem 40 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM40
  case f17 => exact (hmem 48 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM48
  case f18 => exact (hmem 56 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM56
  case f19 => exact (hmem 64 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM64
  case f20 => exact (hmem 72 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM72
  case f21 => exact (hmem 80 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM80
  case f22 => exact (hmem 88 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM88
  case f23 => exact (hmem 96 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM96
  case f24 => exact (hmem 116 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM116
  case f25 => exact (hmem 120 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM120
  case f26 => exact (hmem 124 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM124
  case f27 => exact (hmem 144 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM144
  case f28 => exact (hmem 152 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM152

theorem effect041_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16}
    {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut041 stack input H M))
    (he : (effect041 s).Holds s t) :
    Write.AllHold t (cut042 stack input H M) := by
  apply genericWords041 (fun n ↦ (workingAfter M H n).a) (scheduleWord M)
  · exact scheduleWord_42_41 M
  · exact hf.stackPointer
  · exact hw
  · exact he
end Words041

theorem segment041 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x102dd2 0x102de6
      cut041 cut042 := by
  have hout : ∀ d : Nat, d ≤ bytes041.length →
      0x102dd2 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      (simp only [bytes041, List.length_cons, List.length_nil] at hd;
       simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
  apply Segment.of_block (fun _ _ _ _ => effect041)
    (fun stack input H M => block041 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64
      0x2dd2) bytes041,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect041_rip he
  · intro stack input H M s t _ hf _ he
    exact effect041_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect041_words hf hw he


def bytes042 : List UInt8 :=
  [0x41, 0x31, 0xf1, 0x41, 0x21, 0xc1, 0x44, 0x8d, 0x04, 0x2e, 0x21, 0xfe, 0x44, 0x31, 0xce, 0x44, 0x8b, 0x24, 0x24, 0x48, 0x8b, 0x4c, 0x24, 0x50, 0x41, 0x31, 0xcc, 0x45, 0x31, 0xfc, 0x48, 0x8b, 0x6c, 0x24, 0x20, 0x41, 0x31, 0xec, 0x41, 0xd1, 0xc4, 0x45, 0x01, 0xe2, 0x41, 0x01, 0xf2, 0x89, 0xd6, 0xc1, 0xc6, 0x05, 0x44, 0x01, 0xd6, 0x81, 0xc6, 0xdc, 0xbc, 0x1b, 0x8f]

set_option maxRecDepth 2048 in
def effect042 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq ((xorR32R32Effect 0x102de6 3 9 6)) (andR32R32Effect 0x102de9 3 9 0)) (leaR32Effect 0x102dec 4 8 (.sib 6 (some 5) 0 .none))) (andR32R32Effect 0x102df0 2 6 7)) (xorR32R32Effect 0x102df2 3 6 9)) (movR32M32Effect 0x102df5 12 (.sib 4 none 0 .none))) (movR64M64Effect 0x102df9 1 (.sib 4 none 0 (.d8 0x50)))) (xorR32R32Effect 0x102dfe 3 12 1)) (xorR32R32Effect 0x102e01 3 12 15)) (movR64M64Effect 0x102e04 5 (.sib 4 none 0 (.d8 0x20)))) (xorR32R32Effect 0x102e09 3 12 5)) (rolR32Effect 0x102e0c 3 12 1)) (addR32R32Effect 0x102e0f 3 10 12)) (addR32R32Effect 0x102e12 3 10 6)) (movR32R32Effect 0x102e15 2 6 2)) (rolR32Effect 0x102e17 3 6 5)) (addR32R32Effect 0x102e1a 3 6 10)) (addR32Imm32Effect 0x102e1d 6 6 0x8f1bbcdc)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
theorem block042 [Bindings] (boundary : ReturnBoundary) (stack input : BitVec 64)
    (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes042.length →
      0x102de6 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x102de6 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut042 stack input H M))
      (codeRange 0x102de6 bytes042) effect042 := by
  unfold bytes042 at hout ⊢
  sha1_run_begin (xor_r32_r32_rex_effect_step 0x102de6 0x41 0xf1 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (and_r32_r32_rex_effect_step 0x102de9 0x41 0xc1 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (lea_r32_rex_effect_step 0x102dec 0x44 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) 0 (.sib 6 (some 5) 0 .none) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (and_r32_r32_effect_step 0x102df0 0xfe (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102df2 0x44 0xce (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (mov_r32_m32_effect_step 0x102df5 0x44 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) 4 (.sib 4 none 0 .none) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (mov_r64_m64_effect_step 0x102df9 0x48 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) 1 (.sib 4 none 0 (.d8 0x50)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102dfe 0x41 0xcc (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102e01 0x45 0xfc (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (mov_r64_m64_effect_step 0x102e04 0x48 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) 5 (.sib 4 none 0 (.d8 0x20)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102e09 0x41 0xec (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (rol_r32_one_rex_effect_step 0x102e0c 0x41 0xc4 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (add_r32_r32_rex_effect_step 0x102e0f 0x45 0xe2 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (add_r32_r32_rex_effect_step 0x102e12 0x41 0xf2 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (mov_r32_r32_effect_step 0x102e15 0xd6 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (rol_r32_imm8_effect_step 0x102e17 0xc6 0x5 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (add_r32_r32_rex_effect_step 0x102e1a 0x44 0xd6 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (add_r32_imm32_effect_step 0x102e1d 0xc6 0x8f1bbcdc (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_finish [effect042]


private def genericCut043 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), (A 40)⟩,
    ⟨(.reg 1 : Operand 32), (W 27)⟩,
    ⟨(.reg 2 : Operand 32), (A 41)⟩,
    ⟨(.reg 5 : Operand 32), (W 38)⟩,
    ⟨(.reg 6 : Operand 32), (A 42)⟩,
    ⟨(.reg 7 : Operand 32), ((A 39)).rotateLeft 30⟩,
    ⟨(.reg 8 : Operand 32), ((W 42) + ((A 38)).rotateLeft 30)⟩,
    ⟨(.reg 12 : Operand 32), (W 41)⟩,
    ⟨(.reg 13 : Operand 32), (W 29)⟩,
    ⟨(.reg 14 : Operand 32), (W 40)⟩,
    ⟨(.reg 15 : Operand 32), (W 33)⟩,
    ⟨(.mem (stack + 4) : Operand 32), (W 37)⟩,
    ⟨(.mem (stack + 8) : Operand 32), (W 36)⟩,
    ⟨(.mem (stack + 12) : Operand 32), (W 32)⟩,
    ⟨(.mem (stack + 24) : Operand 32), (W 42)⟩,
    ⟨(.mem (stack + 32) : Operand 32), (W 38)⟩,
    ⟨(.mem (stack + 40) : Operand 32), (W 39)⟩,
    ⟨(.mem (stack + 48) : Operand 32), (W 31)⟩,
    ⟨(.mem (stack + 56) : Operand 32), (W 35)⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), (W 30)⟩,
    ⟨(.mem (stack + 88) : Operand 32), (W 34)⟩,
    ⟨(.mem (stack + 96) : Operand 32), (W 28)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

theorem effect042_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (he : (effect042 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  rw [← hf.stackPointer]
  have hfoot : ∀ c ∈ (effect042 s).components, c ∈ [.reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect042
    iterate 17 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [leaR32Effect_components, addR32Imm32Effect_components, addR32R32Effect_components, andR32R32Effect_components, movR32M32Effect_components, movR32R32Effect_components, movR64M64Effect_components, rolR32Effect_components, xorR32R32Effect_components, List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and, forall_eq]
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

theorem effect042_rip {s t : RamState}
    (he : (effect042 s).Holds s t) :
    t.RIP = 0x102e23 := by
  exact he.rip.trans (by rfl)

section Words042




private theorem scheduleWord_41_42 (M : Vector (BitVec 32) 16) :
    scheduleWord M 41 = (scheduleWord M 38 ^^^ scheduleWord M 33 ^^^
      scheduleWord M 27 ^^^ scheduleWord M 25).rotateLeft 1 := by
  change scheduleWord M (⟨41, by decide⟩ : Fin 80) = _
  rw [scheduleWord_recurrence M ⟨41, by decide⟩ (by decide)]
  simp only [Nat.reduceSub]
  rw [sha1Rotl_eq_rotateLeft 1 _ (by decide)]
  rfl

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
private theorem obs042 {s t : RamState} (he : (effect042 s).Holds s t) :
    Obs ((effect042 s).after s true) t := by
  apply he.obsAfter _ true
  apply Effect.Local.full
  unfold effect042
  repeat' first | (solve | x86_local) | apply Effect.Local.seq

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
private theorem rawR1_042 {s t : RamState}
    (stack : BitVec 64) (v : BitVec 32)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hm : BitVec.setWidth 32 (memLoad s.external (stack + 80) 64) = v)
    (he : (effect042 s).Holds s t) :
    (Operand.reg 1 : Operand 32).read t = v := by
  sha1_norm at hs hm
  have ho := obs042 he
  simp only [← ho.read_reg]
  sha1_norm [effect042, hs,hm,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
    BitVec.shiftLeft_zero, BitVec.add_zero, leaSpec, BitVec.signExtend_eq]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
private theorem rawR5_042 {s t : RamState}
    (stack : BitVec 64) (v : BitVec 32)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hm : BitVec.setWidth 32 (memLoad s.external (stack + 32) 64) = v)
    (he : (effect042 s).Holds s t) :
    (Operand.reg 5 : Operand 32).read t = v := by
  sha1_norm at hs hm
  have ho := obs042 he
  simp only [← ho.read_reg]
  sha1_norm [effect042, hs,hm,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
    BitVec.shiftLeft_zero, BitVec.add_zero, leaSpec, BitVec.signExtend_eq]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
private theorem rawR8_042 {s t : RamState}
    (v5 v6 : BitVec 32)
    (h5 : (Operand.reg 5 : Operand 32).read s = v5)
    (h6 : (Operand.reg 6 : Operand 32).read s = v6)
    (he : (effect042 s).Holds s t) :
    (Operand.reg 8 : Operand 32).read t = v6 + v5 := by
  sha1_norm at h5 h6
  have ho := obs042 he
  simp only [← ho.read_reg]
  sha1_norm [effect042, h5,h6,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
    BitVec.shiftLeft_zero, BitVec.add_zero, leaSpec, BitVec.signExtend_eq]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
private theorem rawR12_042 {s t : RamState}
    (stack : BitVec 64) (m0 m32 m80 v15 : BitVec 32)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hm0 : (Operand.mem (stack + 0) : Operand 32).read s = m0)
    (hm32 : BitVec.setWidth 32 (memLoad s.external (stack + 32) 64) = m32)
    (hm80 : BitVec.setWidth 32 (memLoad s.external (stack + 80) 64) = m80)
    (h15 : (Operand.reg 15 : Operand 32).read s = v15)
    (he : (effect042 s).Holds s t) :
    (Operand.reg 12 : Operand 32).read t = (m0 ^^^ m80 ^^^ v15 ^^^ m32).rotateLeft 1 := by
  sha1_norm [BitVec.add_zero] at hs hm0 hm32 hm80 h15
  have ho := obs042 he
  simp only [← ho.read_reg]
  sha1_norm [effect042, hs,hm0,hm32,hm80,h15,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
    BitVec.shiftLeft_zero, BitVec.add_zero, leaSpec, BitVec.signExtend_eq]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
private theorem rawR6_042 {s t : RamState}
    (stack : BitVec 64) (m0 m32 m80 v15 : BitVec 32) (v0 v2 v6 v7 v9 v10 : BitVec 32)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hm0 : (Operand.mem (stack + 0) : Operand 32).read s = m0)
    (hm32 : BitVec.setWidth 32 (memLoad s.external (stack + 32) 64) = m32)
    (hm80 : BitVec.setWidth 32 (memLoad s.external (stack + 80) 64) = m80)
    (h15 : (Operand.reg 15 : Operand 32).read s = v15)
    (h0 : (Operand.reg 0 : Operand 32).read s = v0)
    (h2 : (Operand.reg 2 : Operand 32).read s = v2)
    (h6 : (Operand.reg 6 : Operand 32).read s = v6)
    (h7 : (Operand.reg 7 : Operand 32).read s = v7)
    (h9 : (Operand.reg 9 : Operand 32).read s = v9)
    (h10 : (Operand.reg 10 : Operand 32).read s = v10)
    (he : (effect042 s).Holds s t) :
    (Operand.reg 6 : Operand 32).read t = v2.rotateLeft 5 +
      (v10 + (m0 ^^^ m80 ^^^ v15 ^^^ m32).rotateLeft 1 +
        (v6 &&& v7 ^^^ ((v9 ^^^ v6) &&& v0))) + 0x8f1bbcdc := by
  sha1_norm [BitVec.add_zero] at hs hm0 hm32 hm80 h15 h0 h2 h6 h7 h9 h10
  have ho := obs042 he
  simp only [← ho.read_reg]
  sha1_norm [effect042, hs,hm0,hm32,hm80,h15,h0,h2,h6,h7,h9,h10,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
    BitVec.shiftLeft_zero, BitVec.add_zero, leaSpec, BitVec.signExtend_eq]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
private theorem genericWords042 {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32)
    (hWork : A 42 = (A 41).rotateLeft 5 +
      (((A 40) &&& ((A 39).rotateLeft 30)) ^^^
        ((A 40) &&& ((A 38).rotateLeft 30)) ^^^
        (((A 39).rotateLeft 30) &&& ((A 38).rotateLeft 30))) +
      (A 37).rotateLeft 30 + K ⟨41, by decide⟩ + W 41)
    (hSched41 : W 41 = (W 38 ^^^ W 33 ^^^ W 27 ^^^ W 25).rotateLeft 1)
    {s t : RamState}
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hw : Write.AllHold s (genericCut042 stack input H A W))
    (he : (effect042 s).Holds s t) :
    Write.AllHold t (genericCut043 stack input H A W) := by
  simp only [genericCut042, Write.AllHold] at hw
  obtain ⟨h0,h2,h5,h6,h7,h9,h10,h13,h14,h15,hM0,hM4,hM8,hM12,hM24,hM32,hM40,hM48,hM56,hM64,hM72,hM80,hM88,hM96,hM116,hM120,hM124,hM144,hM152⟩ := hw
  have hwide {off : BitVec 64} {v : BitVec 32}
      (hm : (Operand.mem (stack + off) : Operand 32).read s = v) :
      BitVec.setWidth 32 (memLoad s.external (stack + off) 64) = v := by
    calc
      _ = (memLoad s.external (stack + off) 64).extractLsb' 0 32 := by
        rw [extractLsb'_zero_eq_setWidth _ 32 (by decide)]
      _ = memLoad s.external (stack + off) 32 := by
        symm
        simpa only [BitVec.add_zero, Nat.mul_zero] using
          memLoad_extractLsb' s.external (stack + off)
            64 32 0 (by decide) (by decide)
      _ = v := hm
  have hM32wide := hwide hM32
  have hM80wide := hwide hM80
  have hR1 := rawR1_042 stack (W 27) hs hM80wide he
  have hR5 := rawR5_042 stack (W 38) hs hM32wide he
  have hR8 := rawR8_042 (W 42) ((A 38).rotateLeft 30) h5 h6 he
  have hR12 := rawR12_042 stack (W 25) (W 38) (W 27) (W 33)
    hs hM0 hM32wide hM80wide h15 he
  have hR6 := rawR6_042 stack (W 25) (W 38) (W 27) (W 33)
    (A 40) (A 41) ((A 38).rotateLeft 30) ((A 39).rotateLeft 30)
    ((A 39).rotateLeft 30) ((A 37).rotateLeft 30)
    hs hM0 hM32wide hM80wide h15 h0 h2 h6 h7 h9 h10 he
  have hSchedule : (W 25 ^^^ W 27 ^^^ W 33 ^^^ W 38).rotateLeft 1 = W 41 := by
    rw [hSched41]
    congr 1
    ac_rfl
  rw [hSchedule] at hR12 hR6
  have hMaj (a b c : BitVec 32) :
      (b &&& c) ^^^ ((c ^^^ b) &&& a) =
        (a &&& c) ^^^ (a &&& b) ^^^ (c &&& b) := by
    rw [BitVec.xor_comm c b, ← sha1Maj_eq_xor]
    simp only [Standards.NIST.SHA2.SHA256.Maj, BitVec.and_comm]
    all_goals ac_rfl
  rw [hMaj] at hR6
  have hV6 : (Operand.reg 6 : Operand 32).read t = A 42 := by
    calc
      _ = _ := hR6
      _ = _ := by
        rw [hWork, show K (⟨41, by decide⟩ : Fin 80) = 0x8f1bbcdc by decide]
        ac_rfl
  have hfoot : ∀ c ∈ (effect042 s).components,
      c ∈ [.reg 1, .reg 5, .reg 6, .reg 8, .reg 9, .reg 10, .reg 12, .flags, .rip] := by
    unfold effect042
    iterate 17 apply components_seq_of
    all_goals sha1_norm
      [leaR32Effect_components,
       addR32Imm32Effect_components, addR32R32Effect_components, andR32R32Effect_components,
       movR32M32Effect_components, movR32R32Effect_components, movR64M64Effect_components,
       rolR32Effect_components, xorR32R32Effect_components,
       List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and, forall_eq]
  have ha := he.agrees.mono hfoot
  have hmem {n : Nat} (off : BitVec 64) :
      (Operand.mem (stack + off) : Operand n).read t =
      (Operand.mem (stack + off) : Operand n).read s := by
    apply memLoad_congr
    intro i hi
    apply congrArg (fun b : Option UInt8 => b.getD 0)
    apply ha.byte
    intro c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact hCov.elim
  simp only [genericCut043, Write.AllHold]
  refine ⟨?f0, ?f1, ?f2, ?f3, ?f4, ?f5, ?f6, ?f7, ?f8, ?f9, ?f10, ?f11, ?f12, ?f13, ?f14, ?f15, ?f16, ?f17, ?f18, ?f19, ?f20, ?f21, ?f22, ?f23, ?f24, ?f25, ?f26, ?f27⟩
  case f0 => exact (ha.read (by simp)).trans h0
  case f1 => exact hR1
  case f2 => exact (ha.read (by simp)).trans h2
  case f3 => exact hR5
  case f4 => exact hV6
  case f5 => exact (ha.read (by simp)).trans h7
  case f6 => exact by rw [hR8]; ac_rfl
  case f7 => exact hR12
  case f8 => exact (ha.read (by simp)).trans h13
  case f9 => exact (ha.read (by simp)).trans h14
  case f10 => exact (ha.read (by simp)).trans h15
  case f11 => exact (hmem 4).trans hM4
  case f12 => exact (hmem 8).trans hM8
  case f13 => exact (hmem 12).trans hM12
  case f14 => exact (hmem 24).trans hM24
  case f15 => exact (hmem 32).trans hM32
  case f16 => exact (hmem 40).trans hM40
  case f17 => exact (hmem 48).trans hM48
  case f18 => exact (hmem 56).trans hM56
  case f19 => exact (hmem 64).trans hM64
  case f20 => exact (hmem 72).trans hM72
  case f21 => exact (hmem 88).trans hM88
  case f22 => exact (hmem 96).trans hM96
  case f23 => exact (hmem 116).trans hM116
  case f24 => exact (hmem 120).trans hM120
  case f25 => exact (hmem 124).trans hM124
  case f26 => exact (hmem 144).trans hM144
  case f27 => exact (hmem 152).trans hM152

theorem effect042_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16}
    {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut042 stack input H M))
    (he : (effect042 s).Holds s t) :
    Write.AllHold t (cut043 stack input H M) := by
  apply genericWords042 (fun n ↦ (workingAfter M H n).a) (scheduleWord M)
  · have hWork := workingAfter_step_a_values M H 37 (by decide)
    simp only [Nat.reduceAdd] at hWork
    rw [sha1_f_majority (t := ⟨41, by decide⟩) (by decide) (by decide)] at hWork
    simp only [Standards.NIST.SHA2.SHA256.Maj] at hWork
    exact hWork
  · exact scheduleWord_41_42 M
  · exact hf.stackPointer
  · exact hw
  · exact he
end Words042

theorem segment042 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x102de6 0x102e23
      cut042 cut043 := by
  have hout : ∀ d : Nat, d ≤ bytes042.length →
      0x102de6 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      (simp only [bytes042, List.length_cons, List.length_nil] at hd;
       simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
  apply Segment.of_block (fun _ _ _ _ => effect042)
    (fun stack input H M => block042 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64
      0x2de6) bytes042,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect042_rip he
  · intro stack input H M s t _ hf _ he
    exact effect042_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect042_words hf hw he


def bytes043 : List UInt8 :=
  [0x49, 0x89, 0xca, 0x45, 0x31, 0xea, 0x44, 0x33, 0x54, 0x24, 0x38, 0x45, 0x31, 0xf2, 0x41, 0xd1, 0xc2, 0xc1, 0xc0, 0x1e, 0x89, 0xc1, 0x31, 0xf9, 0x21, 0xd1, 0x45, 0x8d, 0x0c, 0x3a, 0x4c, 0x89, 0x54, 0x24, 0x50, 0x21, 0xc7, 0x31, 0xcf, 0x44, 0x01, 0xc7, 0x89, 0xf1, 0xc1, 0xc1, 0x05, 0xc1, 0xc2, 0x1e, 0x01, 0xcf, 0x81, 0xc7, 0xdc, 0xbc, 0x1b, 0x8f]

def effect043 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq ((movR64R64Effect 0x102e23 10 1)) (xorR32R32Effect 0x102e26 3 10 13)) (xorR32M32Effect 0x102e29 10 (.sib 4 none 0 (.d8 0x38)))) (xorR32R32Effect 0x102e2e 3 10 14)) (rolR32Effect 0x102e31 3 10 1)) (rolR32Effect 0x102e34 3 0 30)) (movR32R32Effect 0x102e37 2 1 0)) (xorR32R32Effect 0x102e39 2 1 7)) (andR32R32Effect 0x102e3b 2 1 2)) (leaR32Effect 0x102e3d 4 9 (.sib 10 (some 7) 0 .none))) (movM64R64Effect 0x102e41 10 (.sib 4 none 0 (.d8 0x50)))) (andR32R32Effect 0x102e46 2 7 0)) (xorR32R32Effect 0x102e48 2 7 1)) (addR32R32Effect 0x102e4a 3 7 8)) (movR32R32Effect 0x102e4d 2 1 6)) (rolR32Effect 0x102e4f 3 1 5)) (rolR32Effect 0x102e52 3 2 30)) (addR32R32Effect 0x102e55 2 7 1)) (addR32Imm32Effect 0x102e57 6 7 0x8f1bbcdc)

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4000 in
theorem block043 [Bindings] (boundary : ReturnBoundary) (stack input : BitVec 64)
    (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes043.length →
      0x102e23 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x102e23 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut043 stack input H M))
      (codeRange 0x102e23 bytes043) effect043 := by
  have hRaw : AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x102e23 ∧ FrameData stack input M s)
      (codeRange 0x102e23 bytes043) effect043 := by
    unfold bytes043 at hout ⊢
    sha1_run_begin (mov_r64_r64_effect_step 0x102e23 0x49 0xca (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (xor_r32_r32_rex_effect_step 0x102e26 0x45 0xea (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (xor_r32_m32_effect_step 0x102e29 0x44 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) 2 (.sib 4 none 0 (.d8 0x38)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (xor_r32_r32_rex_effect_step 0x102e2e 0x45 0xf2 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (rol_r32_one_rex_effect_step 0x102e31 0x41 0xc2 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (rol_r32_imm8_effect_step 0x102e34 0xc0 0x1e (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (mov_r32_r32_effect_step 0x102e37 0xc1 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (xor_r32_r32_effect_step 0x102e39 0xf9 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (and_r32_r32_effect_step 0x102e3b 0xd1 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (lea_r32_rex_effect_step 0x102e3d 0x45 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) 1 (.sib 10 (some 7) 0 .none) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step 0x102e41 0x4c (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) 2 (.sib 4 none 0 (.d8 0x50)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (and_r32_r32_effect_step 0x102e46 0xc7 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (xor_r32_r32_effect_step 0x102e48 0xcf (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (add_r32_r32_rex_effect_step 0x102e4a 0x44 0xc7 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (mov_r32_r32_effect_step 0x102e4d 0xf1 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (rol_r32_imm8_effect_step 0x102e4f 0xc1 0x5 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (rol_r32_imm8_effect_step 0x102e52 0xc2 0x1e (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (add_r32_r32_effect_step 0x102e55 0xcf (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (add_r32_imm32_effect_step 0x102e57 0xc7 0x8f1bbcdc (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_finish [effect043]
  intro s hr hc hp
  exact hRaw s hr hc ⟨hp.1, hp.2.1⟩


private def genericCut044 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), ((A 40)).rotateLeft 30⟩,
    ⟨(.reg 2 : Operand 32), ((A 41)).rotateLeft 30⟩,
    ⟨(.reg 5 : Operand 32), (W 38)⟩,
    ⟨(.reg 6 : Operand 32), (A 42)⟩,
    ⟨(.reg 7 : Operand 32), (A 43)⟩,
    ⟨(.reg 9 : Operand 32), ((W 43) + ((A 39)).rotateLeft 30)⟩,
    ⟨(.reg 10 : Operand 32), (W 43)⟩,
    ⟨(.reg 12 : Operand 32), (W 41)⟩,
    ⟨(.reg 13 : Operand 32), (W 29)⟩,
    ⟨(.reg 14 : Operand 32), (W 40)⟩,
    ⟨(.reg 15 : Operand 32), (W 33)⟩,
    ⟨(.mem (stack + 4) : Operand 32), (W 37)⟩,
    ⟨(.mem (stack + 8) : Operand 32), (W 36)⟩,
    ⟨(.mem (stack + 12) : Operand 32), (W 32)⟩,
    ⟨(.mem (stack + 24) : Operand 32), (W 42)⟩,
    ⟨(.mem (stack + 32) : Operand 32), (W 38)⟩,
    ⟨(.mem (stack + 40) : Operand 32), (W 39)⟩,
    ⟨(.mem (stack + 48) : Operand 32), (W 31)⟩,
    ⟨(.mem (stack + 56) : Operand 32), (W 35)⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), (W 30)⟩,
    ⟨(.mem (stack + 80) : Operand 32), (W 43)⟩,
    ⟨(.mem (stack + 88) : Operand 32), (W 34)⟩,
    ⟨(.mem (stack + 96) : Operand 32), (W 28)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

theorem effect043_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (he : (effect043 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hfoot : ∀ c ∈ (effect043 s).components, c ∈ [.mem ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 80) 8, .reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect043
    iterate 18 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [leaR32Effect_components, addR32Imm32Effect_components, addR32R32Effect_components, andR32R32Effect_components, movM64R64Effect_components, movR32R32Effect_components, movR64R64Effect_components, rolR32Effect_components, xorR32M32Effect_components, xorR32R32Effect_components, List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and, forall_eq, or_true]
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

theorem effect043_rip {s t : RamState}
    (he : (effect043 s).Holds s t) :
    t.RIP = 0x102e5d := by
  exact he.rip.trans (by rfl)

section Words043
set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
private theorem obs043 {s t : RamState} (he : (effect043 s).Holds s t) :
    Obs ((effect043 s).after s true) t := by
  apply he.obsAfter _ true
  apply Effect.Local.full
  unfold effect043
  repeat' first | (solve | x86_local) | apply Effect.Local.seq

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
private theorem rawR0_043 {s t : RamState}
    (v0 : BitVec 32)
    (h0 : (Operand.reg 0 : Operand 32).read s = v0)
    (he : (effect043 s).Holds s t) :
    (Operand.reg 0 : Operand 32).read t = v0.rotateLeft 30 := by
  simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose] at h0
  have ho := obs043 he
  simp only [← ho.read_reg]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [x86_compose, effect043, h0,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, BitVec.add_zero, leaSpec, BitVec.signExtend_eq]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
private theorem rawR2_043 {s t : RamState}
    (v2 : BitVec 32)
    (h2 : (Operand.reg 2 : Operand 32).read s = v2)
    (he : (effect043 s).Holds s t) :
    (Operand.reg 2 : Operand 32).read t = v2.rotateLeft 30 := by
  simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose] at h2
  have ho := obs043 he
  simp only [← ho.read_reg]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [x86_compose, effect043, h2,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, BitVec.add_zero, leaSpec, BitVec.signExtend_eq]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
private theorem rawR7_043 {s t : RamState}
    (v0 v2 v6 v7 v8 : BitVec 32)
    (h0 : (Operand.reg 0 : Operand 32).read s = v0)
    (h2 : (Operand.reg 2 : Operand 32).read s = v2)
    (h6 : (Operand.reg 6 : Operand 32).read s = v6)
    (h7 : (Operand.reg 7 : Operand 32).read s = v7)
    (h8 : (Operand.reg 8 : Operand 32).read s = v8)
    (he : (effect043 s).Holds s t) :
    (Operand.reg 7 : Operand 32).read t = (v7 &&& v0.rotateLeft 30 ^^^ ((v0.rotateLeft 30 ^^^ v7) &&& v2)) + v8 + v6.rotateLeft 5 + 0x8f1bbcdc := by
  simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose] at h0 h2 h6 h7 h8
  have ho := obs043 he
  simp only [← ho.read_reg]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [x86_compose, effect043, h0, h2, h6, h7, h8,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, BitVec.add_zero, leaSpec, BitVec.signExtend_eq]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
private theorem rawR9_043 {s t : RamState}
    (v1 v7 v13 v14 : BitVec 32)
    (m56 : BitVec 32) (stack : BitVec 64)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (h1 : (Operand.reg 1 : Operand 32).read s = v1)
    (h7 : (Operand.reg 7 : Operand 32).read s = v7)
    (h13 : (Operand.reg 13 : Operand 32).read s = v13)
    (h14 : (Operand.reg 14 : Operand 32).read s = v14)
    (hm56 : (Operand.mem (stack+56) : Operand 32).read s = m56)
    (he : (effect043 s).Holds s t) :
    (Operand.reg 9 : Operand 32).read t = (v1 ^^^ v13 ^^^ m56 ^^^ v14).rotateLeft 1 + v7 := by
  simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose] at hs h1 h7 h13 h14 hm56
  have ho := obs043 he
  simp only [← ho.read_reg]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [x86_compose, effect043, hs, h1, h7, h13, h14, hm56,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, BitVec.add_zero, leaSpec, BitVec.signExtend_eq]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
private theorem rawR10_043 {s t : RamState}
    (v1 v13 v14 : BitVec 32)
    (m56 : BitVec 32) (stack : BitVec 64)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (h1 : (Operand.reg 1 : Operand 32).read s = v1)
    (h13 : (Operand.reg 13 : Operand 32).read s = v13)
    (h14 : (Operand.reg 14 : Operand 32).read s = v14)
    (hm56 : (Operand.mem (stack+56) : Operand 32).read s = m56)
    (he : (effect043 s).Holds s t) :
    (Operand.reg 10 : Operand 32).read t = (v1 ^^^ v13 ^^^ m56 ^^^ v14).rotateLeft 1 := by
  simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose] at hs h1 h13 h14 hm56
  have ho := obs043 he
  simp only [← ho.read_reg]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [x86_compose, effect043, hs, h1, h13, h14, hm56,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
      BitVec.shiftLeft_zero, BitVec.add_zero, leaSpec, BitVec.signExtend_eq]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
private theorem rawM80_043 {s t : RamState}
    (v1 v13 v14 m56 : BitVec 32) (stack : BitVec 64)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (h1 : (Operand.reg 1 : Operand 32).read s = v1)
    (h13 : (Operand.reg 13 : Operand 32).read s = v13)
    (h14 : (Operand.reg 14 : Operand 32).read s = v14)
    (hm56 : (Operand.mem (stack+56) : Operand 32).read s = m56)
    (he : (effect043 s).Holds s t) :
    (Operand.mem (stack+80) : Operand 32).read t =
      (v1 ^^^ v13 ^^^ m56 ^^^ v14).rotateLeft 1 := by
  simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose] at hs h1 h13 h14 hm56
  have ho := obs043 he
  simp only [← ho.read_mem]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [x86_compose,effect043,hs,h1,h13,h14,hm56]
  rw [read32_memStore64_low]
  rw [extractLsb'_zero_eq_setWidth _ 32 (by decide)]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [BitVec.setWidth_setWidth_of_le,BitVec.setWidth_eq]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
private theorem genericWords043 {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) {s t : RamState}
    (hWork : A 43 = (A 42).rotateLeft 5 +
      (((A 41) &&& ((A 39).rotateLeft 30)) ^^^
        ((A 41) &&& ((A 40).rotateLeft 30)) ^^^
        (((A 39).rotateLeft 30) &&& ((A 40).rotateLeft 30))) +
      (A 38).rotateLeft 30 + K ⟨42, by decide⟩ + W 42)
    (hSched43 : W 43 = (W 40 ^^^ W 35 ^^^ W 29 ^^^ W 27).rotateLeft 1)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hw : Write.AllHold s (genericCut043 stack input H A W))
    (he : (effect043 s).Holds s t) :
    Write.AllHold t (genericCut044 stack input H A W) := by
  have hw0 := hw
  simp only [genericCut043,Write.AllHold] at hw0
  obtain ⟨h0,h1,h2,h5,h6,h7,h8,h12,h13,h14,h15,
    hM4,hM8,hM12,hM24,hM32,hM40,hM48,hM56,hM64,hM72,hM88,hM96,
    hM116,hM120,hM124,hM144,hM152⟩ := hw0
  have hR0 := rawR0_043 (A 40) h0 he
  have hR2 := rawR2_043 (A 41) h2 he
  have hR7 := rawR7_043 (A 40) (A 41) (A 42) ((A 39).rotateLeft 30)
    (W 42 + (A 38).rotateLeft 30) h0 h2 h6 h7 h8 he
  have hR9 := rawR9_043 (W 27) ((A 39).rotateLeft 30) (W 29) (W 40) (W 35)
    stack hs h1 h7 h13 h14 hM56 he
  have hR10 := rawR10_043 (W 27) (W 29) (W 40) (W 35) stack hs h1 h13 h14 hM56 he
  have hM80 := rawM80_043 (W 27) (W 29) (W 40) (W 35) stack hs h1 h13 h14 hM56 he
  have hSchedule : (W 27 ^^^ W 29 ^^^ W 35 ^^^ W 40).rotateLeft 1 = W 43 := by
    rw [hSched43]
    congr 1
    ac_rfl
  rw [hSchedule] at hR9 hR10 hM80
  have hMaj (a b c : BitVec 32) :
      (b &&& c) ^^^ ((c ^^^ b) &&& a) =
      (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c) := by
    rw [BitVec.xor_comm c b, ← sha1Maj_eq_xor]
    simp only [Standards.NIST.SHA2.SHA256.Maj, BitVec.and_comm]
    all_goals ac_rfl
  rw [hMaj] at hR7
  have hV7 : (Operand.reg 7 : Operand 32).read t = A 43 := by
    calc
      _ = _ := hR7
      _ = _ := by rw [hWork]; change _ = _; rw [show K (⟨42,by decide⟩ : Fin 80) = 0x8f1bbcdc by decide]; ac_rfl
  have hfoot : ∀ c ∈ (effect043 s).components,
      c ∈ [.mem ((Operand.reg 4 : Operand 64).read s + 80) 8,
        .reg 0,.reg 1,.reg 2,.reg 7,.reg 9,.reg 10,.flags,.rip] := by
    unfold effect043
    iterate 18 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [movR64R64Effect_components, xorR32R32Effect_components, xorR32M32Effect_components,
       rolR32Effect_components, movR32R32Effect_components, andR32R32Effect_components,
       leaR32Effect_components, movM64R64Effect_components,
       addR32R32Effect_components, addR32Imm32Effect_components, 
       List.mem_cons,List.not_mem_nil,or_false,or_imp,forall_and,forall_eq,or_true]
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose]
  have ha := he.agrees.mono hfoot
  rw [hs] at ha
  have hmem {n : Nat} (off : BitVec 64) (hb : OffsetsApart 80 8 off (n / 8))
      (hsize : 8 + n / 8 < 2 ^ 64) :
      (Operand.mem (stack+off) : Operand n).read t =
      (Operand.mem (stack+off) : Operand n).read s := by
    apply memLoad_congr
    intro i hi
    apply congrArg (fun b : Option UInt8 => b.getD 0)
    apply ha.byte
    intro c hc hCov
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨j,hj,heq⟩ := hCov
      exact hb.ne stack hj hi hsize heq.symm
    all_goals exact hCov.elim
  simp only [genericCut044,Write.AllHold]
  refine ⟨?f0, ?f1, ?f2, ?f3, ?f4, ?f5, ?f6, ?f7, ?f8, ?f9, ?f10, ?f11, ?f12, ?f13, ?f14, ?f15, ?f16, ?f17, ?f18, ?f19, ?f20, ?f21, ?f22, ?f23, ?f24, ?f25, ?f26, ?f27, ?f28⟩
  case f0 => exact hR0
  case f1 => exact hR2
  case f2 => exact (ha.read (by simp)).trans h5
  case f3 => exact (ha.read (by simp)).trans h6
  case f4 => exact hV7
  case f5 => exact hR9
  case f6 => exact hR10
  case f7 => exact (ha.read (by simp)).trans h12
  case f8 => exact (ha.read (by simp)).trans h13
  case f9 => exact (ha.read (by simp)).trans h14
  case f10 => exact (ha.read (by simp)).trans h15
  case f11 => exact (hmem 4 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM4
  case f12 => exact (hmem 8 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM8
  case f13 => exact (hmem 12 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM12
  case f14 => exact (hmem 24 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM24
  case f15 => exact (hmem 32 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM32
  case f16 => exact (hmem 40 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM40
  case f17 => exact (hmem 48 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM48
  case f18 => exact (hmem 56 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM56
  case f19 => exact (hmem 64 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM64
  case f20 => exact (hmem 72 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM72
  case f21 => exact hM80
  case f22 => exact (hmem 88 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM88
  case f23 => exact (hmem 96 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM96
  case f24 => exact (hmem 116 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM116
  case f25 => exact (hmem 120 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM120
  case f26 => exact (hmem 124 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM124
  case f27 => exact (hmem 144 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM144
  case f28 => exact (hmem 152 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM152

private theorem scheduleWord_43_43 (M : Vector (BitVec 32) 16) :
    scheduleWord M 43 = (scheduleWord M 40 ^^^ scheduleWord M 35 ^^^
      scheduleWord M 29 ^^^ scheduleWord M 27).rotateLeft 1 := by
  change scheduleWord M (⟨43, by decide⟩ : Fin 80) = _
  rw [scheduleWord_recurrence M ⟨43, by decide⟩ (by decide)]
  simp only [Nat.reduceSub]
  rw [sha1Rotl_eq_rotateLeft 1 _ (by decide)]
  rfl

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
private theorem work043_actual (M : Vector (BitVec 32) 16)
    (H : Vector (BitVec 32) 5) :
    (workingAfter M H 43).a =
      ((workingAfter M H 42).a).rotateLeft 5 +
        (((workingAfter M H 41).a &&& ((workingAfter M H 39).a).rotateLeft 30) ^^^
          ((workingAfter M H 41).a &&& ((workingAfter M H 40).a).rotateLeft 30) ^^^
          (((workingAfter M H 39).a).rotateLeft 30 &&& ((workingAfter M H 40).a).rotateLeft 30)) +
        ((workingAfter M H 38).a).rotateLeft 30 + K ⟨42, by decide⟩ + scheduleWord M 42 := by
  rw [workingAfter_step_a_values M H 38 (by decide)]
  rw [sha1_f_majority (t := ⟨42, by decide⟩) (by decide) (by decide)]
  have hMaj (x y z : BitVec 32) :
      Standards.NIST.SHA2.SHA256.Maj x y z = (x &&& y) ^^^ ((x ^^^ y) &&& z) :=
    sha1Maj_eq_xor x y z
  have hMajAlt (x y z : BitVec 32) :
      (x &&& y) ^^^ ((x ^^^ y) &&& z) =
        (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z) := by
    exact (sha1Maj_eq_xor x y z).symm
  have hK : K (⟨42, by decide⟩ : Fin 80) = 0x8f1bbcdc := by decide
  rw [hMaj, hMajAlt, hK]
  ac_rfl

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
theorem effect043_words {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut043 stack input H M))
    (he : (effect043 s).Holds s t) :
    Write.AllHold t (cut044 stack input H M) := by
  exact genericWords043 (fun n => (workingAfter M H n).a) (scheduleWord M)
    (work043_actual M H) (scheduleWord_43_43 M) hf.stackPointer hw he

end Words043

theorem segment043 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x102e23 0x102e5d
      cut043 cut044 := by
  have hout : ∀ d : Nat, d ≤ bytes043.length →
      0x102e23 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      (simp only [bytes043, List.length_cons, List.length_nil] at hd;
       simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
  apply Segment.of_block (fun _ _ _ _ => effect043)
    (fun stack input H M => block043 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64
      0x2e23) bytes043,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect043_rip he
  · intro stack input H M s t _ hf _ he
    exact effect043_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect043_words hf hw he


def bytes044 : List UInt8 :=
  [0x89, 0xd1, 0x31, 0xc1, 0x21, 0xf1, 0x41, 0x89, 0xd0, 0x41, 0x21, 0xc0, 0x41, 0x31, 0xc8, 0x45, 0x01, 0xc8, 0x89, 0xf9, 0xc1, 0xc1, 0x05, 0x44, 0x01, 0xc1, 0x81, 0xc1, 0xdc, 0xbc, 0x1b, 0x8f, 0xc1, 0xc6, 0x1e, 0x41, 0x89, 0xf0]

def effect044 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq ((movR32R32Effect 0x102e5d 2 1 2)) (xorR32R32Effect 0x102e5f 2 1 0)) (andR32R32Effect 0x102e61 2 1 6)) (movR32R32Effect 0x102e63 3 8 2)) (andR32R32Effect 0x102e66 3 8 0)) (xorR32R32Effect 0x102e69 3 8 1)) (addR32R32Effect 0x102e6c 3 8 9)) (movR32R32Effect 0x102e6f 2 1 7)) (rolR32Effect 0x102e71 3 1 5)) (addR32R32Effect 0x102e74 3 1 8)) (addR32Imm32Effect 0x102e77 6 1 0x8f1bbcdc)) (rolR32Effect 0x102e7d 3 6 30)) (movR32R32Effect 0x102e80 3 8 6)

set_option maxHeartbeats 800000 in
set_option maxRecDepth 131072 in
theorem block044 [Bindings] (boundary : ReturnBoundary) (stack input : BitVec 64)
    (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes044.length →
      0x102e5d + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x102e5d ∧ FrameData stack input M s ∧
        Write.AllHold s (cut044 stack input H M))
      (codeRange 0x102e5d bytes044) effect044 := by
  have hRaw : AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x102e5d ∧ FrameData stack input M s)
      (codeRange 0x102e5d bytes044) effect044 := by
    unfold bytes044 at hout ⊢
    sha1_run_begin (mov_r32_r32_effect_step 0x102e5d 0xd1 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (xor_r32_r32_effect_step 0x102e5f 0xc1 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (and_r32_r32_effect_step 0x102e61 0xf1 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (mov_r32_r32_rex_effect_step 0x102e63 0x41 0xd0 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (and_r32_r32_rex_effect_step 0x102e66 0x41 0xc0 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (xor_r32_r32_rex_effect_step 0x102e69 0x41 0xc8 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (add_r32_r32_rex_effect_step 0x102e6c 0x45 0xc8 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (mov_r32_r32_effect_step 0x102e6f 0xf9 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (rol_r32_imm8_effect_step 0x102e71 0xc1 0x5 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (add_r32_r32_rex_effect_step 0x102e74 0x44 0xc1 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (add_r32_imm32_effect_step 0x102e77 0xc1 0x8f1bbcdc (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (rol_r32_imm8_effect_step 0x102e7d 0xc6 0x1e (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_then (mov_r32_r32_rex_effect_step 0x102e80 0x41 0xf0 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
    sha1_run_finish [effect044]
  intro s hr hc hp
  exact hRaw s hr hc ⟨hp.1, hp.2.1⟩


private def genericCut045 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), ((A 40)).rotateLeft 30⟩,
    ⟨(.reg 1 : Operand 32), (A 44)⟩,
    ⟨(.reg 2 : Operand 32), ((A 41)).rotateLeft 30⟩,
    ⟨(.reg 5 : Operand 32), (W 38)⟩,
    ⟨(.reg 6 : Operand 32), ((A 42)).rotateLeft 30⟩,
    ⟨(.reg 7 : Operand 32), (A 43)⟩,
    ⟨(.reg 8 : Operand 32), ((A 42)).rotateLeft 30⟩,
    ⟨(.reg 10 : Operand 32), (W 43)⟩,
    ⟨(.reg 12 : Operand 32), (W 41)⟩,
    ⟨(.reg 13 : Operand 32), (W 29)⟩,
    ⟨(.reg 14 : Operand 32), (W 40)⟩,
    ⟨(.reg 15 : Operand 32), (W 33)⟩,
    ⟨(.mem (stack + 4) : Operand 32), (W 37)⟩,
    ⟨(.mem (stack + 8) : Operand 32), (W 36)⟩,
    ⟨(.mem (stack + 12) : Operand 32), (W 32)⟩,
    ⟨(.mem (stack + 24) : Operand 32), (W 42)⟩,
    ⟨(.mem (stack + 32) : Operand 32), (W 38)⟩,
    ⟨(.mem (stack + 40) : Operand 32), (W 39)⟩,
    ⟨(.mem (stack + 48) : Operand 32), (W 31)⟩,
    ⟨(.mem (stack + 56) : Operand 32), (W 35)⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), (W 30)⟩,
    ⟨(.mem (stack + 80) : Operand 32), (W 43)⟩,
    ⟨(.mem (stack + 88) : Operand 32), (W 34)⟩,
    ⟨(.mem (stack + 96) : Operand 32), (W 28)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

theorem effect044_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (_hf : FrameData stack input M s)
    (he : (effect044 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hfoot : ∀ c ∈ (effect044 s).components, c ∈ [.reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect044
    iterate 12 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [addR32Imm32Effect_components, addR32R32Effect_components, andR32R32Effect_components, movR32R32Effect_components, rolR32Effect_components, xorR32R32Effect_components, List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and, forall_eq]
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

theorem effect044_rip {s t : RamState}
    (he : (effect044 s).Holds s t) :
    t.RIP = 0x102e83 := by
  exact he.rip.trans (by rfl)

section Words044




set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
private theorem genericWords044 {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32)
    (hWork : A 44 = (A 43).rotateLeft 5 +
      (((A 42) &&& ((A 40).rotateLeft 30)) ^^^
        ((A 42) &&& ((A 41).rotateLeft 30)) ^^^
        (((A 40).rotateLeft 30) &&& ((A 41).rotateLeft 30))) +
      (A 39).rotateLeft 30 + K ⟨43, by decide⟩ + W 43)
    {s t : RamState}
    (hw : Write.AllHold s (genericCut044 stack input H A W))
    (he : (effect044 s).Holds s t) :
    Write.AllHold t (genericCut045 stack input H A W) := by
  simp only [genericCut044, Write.AllHold] at hw
  obtain ⟨h0,h2,h5,h6,h7,h9,h10,h12,h13,h14,h15,
    hM4,hM8,hM12,hM24,hM32,hM40,hM48,hM56,hM64,hM72,hM80,hM88,hM96,
    hM116,hM120,hM124,hM144,hM152⟩ := hw
  have hfull : ∀ w ∈ (effect044 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect044
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  simp only [x86_compose] at h0 h2 h6 h7 h9
  have hMaj (a b c : BitVec 32) :
      (b &&& c) ^^^ ((b ^^^ c) &&& a) =
        (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c) := by
    rw [← sha1Maj_eq_xor]
    simp only [Standards.NIST.SHA2.SHA256.Maj, BitVec.and_comm]
    all_goals ac_rfl
  have hR1 : (Operand.reg 1 : Operand 32).read t = A 44 := by
    simp only [← ho.read_reg]
    simp (config := {decide := true, implicitDefEqProofs := false}) only
      [x86_compose, effect044, h0, h2, h6, h7, h9,
        BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
    rw [hMaj]
    rw [hWork]
    ac_rfl
  have hR6 : (Operand.reg 6 : Operand 32).read t = (A 42).rotateLeft 30 := by
    simp only [← ho.read_reg]
    simp (config := {decide := true, implicitDefEqProofs := false}) only
      [x86_compose, effect044, h6, BitVec.setWidth_setWidth_of_le,
        BitVec.setWidth_eq]
  have hR8 : (Operand.reg 8 : Operand 32).read t = (A 42).rotateLeft 30 := by
    simp only [← ho.read_reg]
    simp (config := {decide := true, implicitDefEqProofs := false}) only
      [x86_compose, effect044, h6, BitVec.setWidth_setWidth_of_le,
        BitVec.setWidth_eq]
  have hfoot : ∀ c ∈ (effect044 s).components,
      c ∈ [.reg 1, .reg 6, .reg 8, .flags, .rip] := by
    unfold effect044
    iterate 12 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [movR32R32Effect_components, xorR32R32Effect_components,
       andR32R32Effect_components, addR32R32Effect_components,
       addR32Imm32Effect_components, rolR32Effect_components,
       List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and, forall_eq]
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [x86_compose]
  have ha := he.agrees.mono hfoot
  have hmem {n : Nat} (address : BitVec 64) :
      (Operand.mem address : Operand n).read t =
        (Operand.mem address : Operand n).read s := by
    apply memLoad_congr
    intro i hi
    apply congrArg (fun b : Option UInt8 ↦ b.getD 0)
    apply ha.byte
    intro c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals exact hCov.elim
  simp only [genericCut045, Write.AllHold]
  refine ⟨?f0, ?f1, ?f2, ?f3, ?f4, ?f5, ?f6, ?f7, ?f8, ?f9, ?f10, ?f11,
    ?f12, ?f13, ?f14, ?f15, ?f16, ?f17, ?f18, ?f19, ?f20, ?f21, ?f22,
    ?f23, ?f24, ?f25, ?f26, ?f27, ?f28, ?f29⟩
  case f0 => exact (ha.read (by simp)).trans h0
  case f1 => exact hR1
  case f2 => exact (ha.read (by simp)).trans h2
  case f3 => exact (ha.read (by simp)).trans h5
  case f4 => exact hR6
  case f5 => exact (ha.read (by simp)).trans h7
  case f6 => exact hR8
  case f7 => exact (ha.read (by simp)).trans h10
  case f8 => exact (ha.read (by simp)).trans h12
  case f9 => exact (ha.read (by simp)).trans h13
  case f10 => exact (ha.read (by simp)).trans h14
  case f11 => exact (ha.read (by simp)).trans h15
  case f12 => exact (hmem (stack + 4)).trans hM4
  case f13 => exact (hmem (stack + 8)).trans hM8
  case f14 => exact (hmem (stack + 12)).trans hM12
  case f15 => exact (hmem (stack + 24)).trans hM24
  case f16 => exact (hmem (stack + 32)).trans hM32
  case f17 => exact (hmem (stack + 40)).trans hM40
  case f18 => exact (hmem (stack + 48)).trans hM48
  case f19 => exact (hmem (stack + 56)).trans hM56
  case f20 => exact (hmem (stack + 64)).trans hM64
  case f21 => exact (hmem (stack + 72)).trans hM72
  case f22 => exact (hmem (stack + 80)).trans hM80
  case f23 => exact (hmem (stack + 88)).trans hM88
  case f24 => exact (hmem (stack + 96)).trans hM96
  case f25 => exact (hmem (stack + 116)).trans hM116
  case f26 => exact (hmem (stack + 120)).trans hM120
  case f27 => exact (hmem (stack + 124)).trans hM124
  case f28 => exact (hmem (stack + 144)).trans hM144
  case f29 => exact (hmem (stack + 152)).trans hM152

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
private theorem work044_actual (M : Vector (BitVec 32) 16)
    (H : Vector (BitVec 32) 5) :
    (workingAfter M H 44).a =
      ((workingAfter M H 43).a).rotateLeft 5 +
        (((workingAfter M H 42).a &&& ((workingAfter M H 40).a).rotateLeft 30) ^^^
          ((workingAfter M H 42).a &&& ((workingAfter M H 41).a).rotateLeft 30) ^^^
          (((workingAfter M H 40).a).rotateLeft 30 &&& ((workingAfter M H 41).a).rotateLeft 30)) +
        ((workingAfter M H 39).a).rotateLeft 30 + K ⟨43, by decide⟩ + scheduleWord M 43 := by
  rw [workingAfter_step_a_values M H 39 (by decide)]
  simp only [Nat.reduceAdd]
  rw [sha1_f_majority (t := ⟨43, by decide⟩) (by decide) (by decide)]
  have hMaj (x y z : BitVec 32) :
      Standards.NIST.SHA2.SHA256.Maj x y z = (x &&& y) ^^^ ((x ^^^ y) &&& z) :=
    sha1Maj_eq_xor x y z
  have hMajAlt (x y z : BitVec 32) :
      (x &&& y) ^^^ ((x ^^^ y) &&& z) =
        (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z) := by
    exact (sha1Maj_eq_xor x y z).symm
  have hK : K (⟨43, by decide⟩ : Fin 80) = 0x8f1bbcdc := by decide
  rw [hMaj, hMajAlt, hK]
  ac_rfl

theorem effect044_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16}
    {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut044 stack input H M))
    (he : (effect044 s).Holds s t) :
    Write.AllHold t (cut045 stack input H M) := by
  let _ := hf
  have hWork := work044_actual M H
  let A := fun n ↦ (workingAfter M H n).a
  let W := scheduleWord M
  have hpre : Write.AllHold s (genericCut044 stack input H A W) := by
    simpa (config := {implicitDefEqProofs := false, decide := true}) only
      [genericCut044, A, W, cut044] using hw
  have hraw := genericWords044 A W hWork hpre he
  change Write.AllHold t (cut045 stack input H M) at hraw
  exact hraw
end Words044

theorem segment044 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x102e5d 0x102e83
      cut044 cut045 := by
  have hout : ∀ d : Nat, d ≤ bytes044.length →
      0x102e5d + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      (simp only [bytes044, List.length_cons, List.length_nil] at hd;
       simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
  apply Segment.of_block (fun _ _ _ _ => effect044)
    (fun stack input H M => block044 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64
      0x2e5d) bytes044,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect044_rip he
  · intro stack input H M s t _ hf _ he
    exact effect044_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect044_words hf hw he

theorem segments039_050 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x102d54 0x102fc0 cut039 cut051 := by
  have h0 := segment039 boundary hOutside
  have h1 := h0.seq (segment040 boundary hOutside)
  have h2 := h1.seq (segment041 boundary hOutside)
  have h3 := h2.seq (segment042 boundary hOutside)
  have h4 := h3.seq (segment043 boundary hOutside)
  have h5 := h4.seq (segment044 boundary hOutside)
  exact h5.seq (segments045_050 boundary hOutside)

end Sha1.Proofs.Compress.Machine
