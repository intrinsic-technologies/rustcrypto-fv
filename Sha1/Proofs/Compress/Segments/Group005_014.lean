import Sha1.Proofs.Compress.Machine.Run
import Sha1.Proofs.Compress.Rounds.Scalar
import Sha1.Proofs.Compress.Segments.Group010_014
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Mov.Generated.RM.Triple
import Sha1.Proofs.Common.Instructions.MovStore.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import X86Proofs.Instructions.Add.Generated.AccImm32.Triple
import X86Proofs.Instructions.Bswap.Generated.R.Triple
import X86Proofs.Instructions.Lea.Generated.RM.Triple

namespace Sha1.Proofs.Compress.Machine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Spec.Program
open Standards.NIST.SHA1 Sha1.Proofs.Compress.Rounds

attribute [local irreducible] workingAfter scheduleWord messageSchedule

def bytes005 : List UInt8 :=
  [0x41, 0x31, 0xc8, 0x41, 0x21, 0xc0, 0x41, 0x31, 0xc8, 0x44, 0x1, 0xca, 0x44, 0x1, 0xc2, 0x41,
    0x89, 0xf0, 0x41, 0xc1, 0xc0, 0x5, 0x44, 0x1, 0xc2, 0x81, 0xc2, 0x99, 0x79, 0x82, 0x5a, 0xc1,
    0xc0, 0x1e, 0x41, 0x89, 0xc0, 0x41, 0x31, 0xf8, 0x41, 0x21, 0xf0, 0x41, 0x31, 0xf8, 0x44, 0x1,
    0xf1, 0x44, 0x1, 0xc1, 0x41, 0x89, 0xd0, 0x41, 0xc1, 0xc0, 0x5, 0x44, 0x1, 0xc1, 0x81, 0xc1,
    0x99, 0x79, 0x82, 0x5a]

set_option maxHeartbeats 800000 in
def effect005 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq (Effect.seq ((xorR32R32Effect 0x1025f2 3 8 1)) (andR32R32Effect 0x1025f5
    3 8 0)) (xorR32R32Effect 0x1025f8 3 8 1)) (addR32R32Effect 0x1025fb 3 2 9)) (addR32R32Effect
    0x1025fe 3 2 8)) (movR32R32Effect 0x102601 3 8 6)) (rolR32Effect 0x102604 4 8 5))
    (addR32R32Effect 0x102608 3 2 8)) (addR32Imm32Effect 0x10260b 6 2 0x5a827999)) (rolR32Effect
    0x102611 3 0 30)) (movR32R32Effect 0x102614 3 8 0)) (xorR32R32Effect 0x102617 3 8 7))
    (andR32R32Effect 0x10261a 3 8 6)) (xorR32R32Effect 0x10261d 3 8 7)) (addR32R32Effect 0x102620 3
    1 14)) (addR32R32Effect 0x102623 3 1 8)) (movR32R32Effect 0x102626 3 8 2)) (rolR32Effect
    0x102629 4 8 5)) (addR32R32Effect 0x10262d 3 1 8)) (addR32Imm32Effect 0x102630 6 1 0x5a827999)

set_option maxHeartbeats 1600000 in
private theorem block005 [Bindings] (boundary : ReturnBoundary)
    (stack input : BitVec 64) (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes005.length → 0x1025f2 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x1025f2 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut005 stack input H M))
      (codeRange 0x1025f2 bytes005) effect005 := by
  unfold bytes005 at hout ⊢
  sha1_run_begin (xor_r32_r32_rex_effect_step 0x1025f2 0x41 0xc8
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) )
  sha1_run_then (and_r32_r32_rex_effect_step 0x1025f5 0x41 0xc0
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) )
  sha1_run_then (xor_r32_r32_rex_effect_step 0x1025f8 0x41 0xc8
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) )
  sha1_run_then (add_r32_r32_rex_effect_step 0x1025fb 0x44 0xca
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) )
  sha1_run_then (add_r32_r32_rex_effect_step 0x1025fe 0x44 0xc2
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) )
  sha1_run_then (mov_r32_r32_rex_effect_step 0x102601 0x41 0xf0
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) )
  sha1_run_then (rol_r32_imm8_rex_effect_step 0x102604 0x41 0xc0 0x5
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel) )
  sha1_run_then (add_r32_r32_rex_effect_step 0x102608 0x44 0xc2
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) )
  sha1_run_then (add_r32_imm32_effect_step 0x10260b 0xc2 0x5a827999 (by decide +kernel)
    (by decide +kernel) )
  sha1_run_then (rol_r32_imm8_effect_step 0x102611 0xc0 0x1e (by decide +kernel) (by decide +kernel)
    )
  sha1_run_then (mov_r32_r32_rex_effect_step 0x102614 0x41 0xc0
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) )
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102617 0x41 0xf8
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) )
  sha1_run_then (and_r32_r32_rex_effect_step 0x10261a 0x41 0xf0
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) )
  sha1_run_then (xor_r32_r32_rex_effect_step 0x10261d 0x41 0xf8
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) )
  sha1_run_then (add_r32_r32_rex_effect_step 0x102620 0x44 0xf1
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) )
  sha1_run_then (add_r32_r32_rex_effect_step 0x102623 0x44 0xc1
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) )
  sha1_run_then (mov_r32_r32_rex_effect_step 0x102626 0x41 0xd0
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) )
  sha1_run_then (rol_r32_imm8_rex_effect_step 0x102629 0x41 0xc0 0x5
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel) )
  sha1_run_then (add_r32_r32_rex_effect_step 0x10262d 0x44 0xc1
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) )
  sha1_run_then (add_r32_imm32_effect_step 0x102630 0xc1 0x5a827999 (by decide +kernel)
    (by decide +kernel) )
  sha1_run_finish [effect005]

set_option maxHeartbeats 800000 in
private theorem effect005_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (he : (effect005 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  sha1_norm at hs
  have hfoot : ∀ c ∈ (effect005 s).components, c ∈ scratchComponents stack := by
    unfold effect005
    iterate 19 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [addR32Imm32Effect_components, addR32R32Effect_components, andR32R32Effect_components,
        movR32R32Effect_components, rolR32Effect_components, xorR32R32Effect_components,
        scratchComponents,
        List.mem_cons, List.not_mem_nil, or_false, or_imp,
        forall_and, forall_eq, or_true, true_or]
    all_goals sha1_norm [hs]
  exact he.agrees.mono hfoot

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
private theorem effect005_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut005 stack input H M))
    (he : (effect005 s).Holds s t) :
    Write.AllHold t (cut006 stack input H M) := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hfull : ∀ w ∈ (effect005 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect005
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  simp only [cut005, Write.AllHold] at hw
  obtain ⟨h0,h1,h2,h6,h7,h8,h9,h12,h14,h15,hM8,hM56,hM64,hM88,hM116,hM120,hM124,hM144,hM152⟩ := hw
  sha1_norm at hs h0 h1 h2 h6 h7 h8 h9 h12 h14 h15 hM8 hM56 hM64 hM88 hM116 hM120 hM124 hM144 hM152
  simp only [cut006, Write.AllHold, ← ho.read_reg, ← ho.read_mem]
  sha1_norm
    [effect005,hs,h0,h1,h2,h6,h7,h8,h9,h12,h14,h15,hM8,hM56,hM64,hM88,
      hM116,hM120,hM124,hM144,hM152,
    movR32M32LowEffect, leaSpec, bswap32_bswap32,
    read32_memStore64_low, extractLsb'_zero_eq_setWidth,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
    BitVec.shiftLeft_zero, BitVec.add_zero]
  have h4 := workingAfter_step_a M H 3 (by decide +kernel)
  rw [workingAfter_step_b M H 2 (by decide +kernel),
    workingAfter_step_c M H 2 (by decide +kernel),
    workingAfter_step_b M H 1 (by decide +kernel),
    workingAfter_step_d M H 2 (by decide +kernel),
    workingAfter_step_c M H 1 (by decide +kernel),
    workingAfter_step_b M H 0 (by decide +kernel),
    workingAfter_step_e M H 2 (by decide +kernel),
    workingAfter_step_d M H 1 (by decide +kernel),
    workingAfter_step_c M H 0 (by decide +kernel), workingAfter_zero] at h4
  simp only [WorkingVariables.ofHashValue,
    sha1Rotl_eq_rotateLeft 5 _ (by decide), sha1Rotl_eq_rotateLeft 30 _ (by decide),
    sha1_f_choice (t := ⟨3, by decide⟩) (by decide),
    sha1_K_choice (t := ⟨3, by decide⟩) (by decide), Nat.reduceAdd] at h4
  have h5 := workingAfter_step_a_values M H 0 (by decide +kernel)
  simp only [Nat.reduceAdd, workingAfter_zero, WorkingVariables.ofHashValue,
    sha1_f_choice (t := ⟨4, by decide⟩) (by decide),
    sha1_K_choice (t := ⟨4, by decide⟩) (by decide)] at h5
  rw [sha1Ch_eq, BitVec.and_comm _ (_ ^^^ _), BitVec.xor_comm] at h4 h5
  change (workingAfter M H 4).a = (workingAfter M H 3).a.rotateLeft 5 +
    (((workingAfter M H 1).a.rotateLeft 30 ^^^ H[0].rotateLeft 30) &&&
      (workingAfter M H 2).a ^^^ H[0].rotateLeft 30) + (0x5a827999#32) +
    scheduleWord M 3 + H[1].rotateLeft 30 at h4
  change (workingAfter M H 5).a = (workingAfter M H 4).a.rotateLeft 5 +
    (((workingAfter M H 2).a.rotateLeft 30 ^^^ (workingAfter M H 1).a.rotateLeft 30) &&&
      (workingAfter M H 3).a ^^^ (workingAfter M H 1).a.rotateLeft 30) +
    H[0].rotateLeft 30 + (0x5a827999#32) + scheduleWord M 4 at h5
  constructor
  · rw [h5, h4]
    ac_rfl
  · rw [h4]
    ac_rfl

set_option maxHeartbeats 800000 in
theorem segment005 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x1025f2 0x102636 cut005 cut006 := by
  have hout : ∀ d : Nat, d ≤ bytes005.length →
      0x1025f2 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      simp only [bytes005, List.length_cons, List.length_nil] at hd <;>
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  apply Segment.of_block (fun _ _ _ _ ↦ effect005)
    (fun stack input H M ↦ block005 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 0x25f2) bytes005,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact he.rip.trans (by rfl)
  · intro stack input H M s t _ hf _ he
    exact effect005_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect005_words hf hw he

def bytes006 : List UInt8 :=
  [0x4c, 0x8b, 0x44, 0x24, 0x40, 0x45, 0x8b, 0x40, 0x14, 0x41, 0xf, 0xc8, 0x45, 0x89, 0xc1, 0x44,
    0x89, 0x44, 0x24, 0x4, 0xc1, 0xc6, 0x1e, 0x41, 0x89, 0xc8, 0x41, 0xc1, 0xc0, 0x5, 0x41, 0x89,
    0xf2, 0x41, 0x31, 0xc2, 0x41, 0x21, 0xd2, 0x41, 0x31, 0xc2, 0x44, 0x1, 0xcf, 0x44, 0x1, 0xd7,
    0x45, 0x8d, 0x14, 0x38, 0x41, 0x81, 0xc2, 0x99, 0x79, 0x82, 0x5a]

set_option maxHeartbeats 800000 in
def effect006 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    ((movR64M64Effect 0x102636 8 (.sib 4 none 0 (.d8 0x40)))) (movR32M32Effect 0x10263b 8 (.base 8
    (.d8 0x14)))) (bswapR32Effect 0x10263f 3 8)) (movR32R32Effect 0x102642 3 9 8)) (movM32R32Effect
    0x102645 8 (.sib 4 none 0 (.d8 0x4)))) (rolR32Effect 0x10264a 3 6 30)) (movR32R32Effect 0x10264d
    3 8 1)) (rolR32Effect 0x102650 4 8 5)) (movR32R32Effect 0x102654 3 10 6)) (xorR32R32Effect
    0x102657 3 10 0)) (andR32R32Effect 0x10265a 3 10 2)) (xorR32R32Effect 0x10265d 3 10 0))
    (addR32R32Effect 0x102660 3 7 9)) (addR32R32Effect 0x102663 3 7 10)) (leaR32Effect 0x102666 4 10
    (.sib 8 (some 7) 0 .none))) (addR32Imm32Effect 0x10266a 7 10 0x5a827999)

set_option maxHeartbeats 1600000 in
private theorem block006 [Bindings] (boundary : ReturnBoundary)
    (stack input : BitVec 64) (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes006.length → 0x102636 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x102636 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut006 stack input H M))
      (codeRange 0x102636 bytes006) effect006 := by
  unfold bytes006 at hout ⊢
  sha1_run_begin (mov_r64_m64_effect_step 0x102636 0x4c (by unfold RexWPrefix; decide +kernel) 0
    (.sib 4 none 0 (.d8 0x40)) (by decide +kernel) (by decide +kernel) (by decide +kernel) )
  sha1_run_then (mov_r32_m32_effect_step 0x10263b 0x45 (by unfold RexNoWPrefix; decide +kernel) 0
    (.base 8 (.d8 0x14)) (by decide +kernel) (by decide +kernel) (by decide +kernel) )
  sha1_run_then (bswap_r32_rex_effect_step 0x10263f 0x41 (by unfold RexNoWPrefix; decide +kernel)
    0xc8 (by decide +kernel) )
  sha1_run_then (mov_r32_r32_rex_effect_step 0x102642 0x45 0xc1
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) )
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m32_r32_effect_step 0x102645 0x44
    (by unfold RexNoWPrefix; decide +kernel) 0 (.sib 4 none 0 (.d8 0x4)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) )
  sha1_run_then (rol_r32_imm8_effect_step 0x10264a 0xc6 0x1e (by decide +kernel) (by decide +kernel)
    )
  sha1_run_then (mov_r32_r32_rex_effect_step 0x10264d 0x41 0xc8
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) )
  sha1_run_then (rol_r32_imm8_rex_effect_step 0x102650 0x41 0xc0 0x5
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel) )
  sha1_run_then (mov_r32_r32_rex_effect_step 0x102654 0x41 0xf2
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) )
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102657 0x41 0xc2
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) )
  sha1_run_then (and_r32_r32_rex_effect_step 0x10265a 0x41 0xd2
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) )
  sha1_run_then (xor_r32_r32_rex_effect_step 0x10265d 0x41 0xc2
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) )
  sha1_run_then (add_r32_r32_rex_effect_step 0x102660 0x44 0xcf
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) )
  sha1_run_then (add_r32_r32_rex_effect_step 0x102663 0x44 0xd7
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) )
  sha1_run_then (lea_r32_rex_effect_step 0x102666 0x45 (by unfold RexNoWPrefix; decide +kernel) 2
    (.sib 8 (some 7) 0 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel) )
  sha1_run_then (add_r32_imm32_rex_effect_step 0x10266a 0x41 0xc2 0x5a827999
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel) )
  sha1_run_finish [effect006]

set_option maxHeartbeats 800000 in
private theorem effect006_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (he : (effect006 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  sha1_norm at hs
  have hfoot : ∀ c ∈ (effect006 s).components, c ∈ [.mem (stack + 4) 4] ++ scratchComponents stack
    := by
    unfold effect006
    iterate 15 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [addR32Imm32Effect_components, addR32R32Effect_components, andR32R32Effect_components,
        bswapR32Effect_components, leaR32Effect_components, movM32R32Effect_components,
        movR32M32Effect_components, movR32R32Effect_components, movR64M64Effect_components,
        rolR32Effect_components, xorR32R32Effect_components, scratchComponents,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_imp,
        forall_and, forall_eq, or_true, true_or]
    all_goals sha1_norm [hs]
  apply (he.agrees.mono hfoot).widen
  · intro c hc hn
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | hc
    · cases hn
    · exact hc
  · intro a c hc hCov
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | hc
    · exact scratchComponents_stack (Or.inl (by decide +kernel)) hCov
    · exact ⟨c, hc, hCov⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
private theorem effect006_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut006 stack input H M))
    (he : (effect006 s).Holds s t) :
    Write.AllHold t (cut007 stack input H M) := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hin5 : (Operand.mem (input + 20) : Operand 32).read s =
      bswapSpec (scheduleWord M 5) := by
    rw [scheduleWord_initial M 5 (by decide +kernel)]
    exact hf.words 5
  sha1_norm at hin5
  have hfull : ∀ w ∈ (effect006 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect006
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  simp only [cut006, Write.AllHold] at hw
  obtain ⟨h0,h1,h2,h6,h7,h12,h15,hM8,hM56,hM64,hM88,hM116,hM120,hM124,hM144,hM152⟩ := hw
  sha1_norm at hs h0 h1 h2 h6 h7 h12 h15 hM8 hM56 hM64 hM88 hM116 hM120 hM124 hM144 hM152
  simp only [cut007, Write.AllHold, ← ho.read_reg, ← ho.read_mem]
  sha1_norm
    [effect006,hs,hin5,h0,h1,h2,h6,h7,h12,h15,hM8,hM56,hM64,hM88,
      hM116,hM120,hM124,hM144,hM152,
    movR32M32LowEffect, leaSpec, bswap32_bswap32,
    read32_memStore64_low, extractLsb'_zero_eq_setWidth,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
    BitVec.shiftLeft_zero, BitVec.add_zero]
  have hWork := workingAfter_step_a_values M H 1 (by decide +kernel)
  simp only [Nat.reduceAdd, sha1_f_choice (t := ⟨5, by decide⟩) (by decide),
    sha1_K_choice (t := ⟨5, by decide⟩) (by decide)] at hWork
  rw [sha1Ch_eq, BitVec.and_comm _ (_ ^^^ _), BitVec.xor_comm] at hWork
  change (workingAfter M H 6).a = (workingAfter M H 5).a.rotateLeft 5 +
    (((workingAfter M H 3).a.rotateLeft 30 ^^^ (workingAfter M H 2).a.rotateLeft 30) &&&
      (workingAfter M H 4).a ^^^ (workingAfter M H 2).a.rotateLeft 30) +
    (workingAfter M H 1).a.rotateLeft 30 + (0x5a827999#32) +
    scheduleWord M 5 at hWork
  rw [hWork]
  ac_rfl

set_option maxHeartbeats 800000 in
theorem segment006 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x102636 0x102671 cut006 cut007 := by
  have hout : ∀ d : Nat, d ≤ bytes006.length →
      0x102636 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      simp only [bytes006, List.length_cons, List.length_nil] at hd <;>
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  apply Segment.of_block (fun _ _ _ _ ↦ effect006)
    (fun stack input H M ↦ block006 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 0x2636) bytes006,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact he.rip.trans (by rfl)
  · intro stack input H M s t _ hf _ he
    exact effect006_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect006_words hf hw he

def bytes007 : List UInt8 :=
  [0x48, 0x8b, 0x7c, 0x24, 0x40, 0x8b, 0x7f, 0x18, 0xf, 0xcf, 0x49, 0x89, 0xf8, 0x48, 0x89, 0x7c,
    0x24, 0x20, 0xc1, 0xc2, 0x1e, 0x89, 0xd7, 0x31, 0xf7, 0x21, 0xcf, 0x31, 0xf7, 0x44, 0x1, 0xc0,
    0x1, 0xf8, 0x44, 0x89, 0xd7, 0xc1, 0xc7, 0x5, 0x1, 0xc7, 0x81, 0xc7, 0x99, 0x79, 0x82, 0x5a]

set_option maxHeartbeats 800000 in
def effect007 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    ((movR64M64Effect 0x102671 7 (.sib 4 none 0 (.d8 0x40)))) (movR32M32LowEffect 0x102676 7 (.base
    7 (.d8 0x18)))) (bswapR32Effect 0x102679 2 7)) (movR64R64Effect 0x10267b 8 7)) (movM64R64Effect
    0x10267e 7 (.sib 4 none 0 (.d8 0x20)))) (rolR32Effect 0x102683 3 2 30)) (movR32R32Effect
    0x102686 2 7 2)) (xorR32R32Effect 0x102688 2 7 6)) (andR32R32Effect 0x10268a 2 7 1))
    (xorR32R32Effect 0x10268c 2 7 6)) (addR32R32Effect 0x10268e 3 0 8)) (addR32R32Effect 0x102691 2
    0 7)) (movR32R32Effect 0x102693 3 7 10)) (rolR32Effect 0x102696 3 7 5)) (addR32R32Effect
    0x102699 2 7 0)) (addR32Imm32Effect 0x10269b 6 7 0x5a827999)

set_option maxHeartbeats 1600000 in
private theorem block007 [Bindings] (boundary : ReturnBoundary)
    (stack input : BitVec 64) (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes007.length → 0x102671 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x102671 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut007 stack input H M))
      (codeRange 0x102671 bytes007) effect007 := by
  unfold bytes007 at hout ⊢
  sha1_run_begin (mov_r64_m64_effect_step 0x102671 0x48 (by unfold RexWPrefix; decide +kernel) 7
    (.sib 4 none 0 (.d8 0x40)) (by decide +kernel) (by decide +kernel) (by decide +kernel) )
  sha1_run_then (mov_r32_m32_low_effect_step 0x102676 7 (.base 7 (.d8 0x18)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) )
  sha1_run_then (bswap_r32_effect_step 0x102679 0xcf (by decide +kernel))
  sha1_run_then (mov_r64_r64_effect_step 0x10267b 0x49 0xf8 (by unfold RexWPrefix; decide +kernel)
    (by decide +kernel) )
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step 0x10267e 0x48
    (by unfold RexWPrefix; decide +kernel) 7 (.sib 4 none 0 (.d8 0x20)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) )
  sha1_run_then (rol_r32_imm8_effect_step 0x102683 0xc2 0x1e (by decide +kernel) (by decide +kernel)
    )
  sha1_run_then (mov_r32_r32_effect_step 0x102686 0xd7 (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x102688 0xf7 (by decide +kernel))
  sha1_run_then (and_r32_r32_effect_step 0x10268a 0xcf (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x10268c 0xf7 (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x10268e 0x44 0xc0
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) )
  sha1_run_then (add_r32_r32_effect_step 0x102691 0xf8 (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x102693 0x44 0xd7
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) )
  sha1_run_then (rol_r32_imm8_effect_step 0x102696 0xc7 0x5 (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x102699 0xc7 (by decide +kernel))
  sha1_run_then (add_r32_imm32_effect_step 0x10269b 0xc7 0x5a827999 (by decide +kernel)
    (by decide +kernel) )
  sha1_run_finish [effect007]

set_option maxHeartbeats 800000 in
private theorem effect007_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (he : (effect007 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  sha1_norm at hs
  have hfoot : ∀ c ∈ (effect007 s).components, c ∈ [.mem (stack + 32) 8] ++ scratchComponents stack
    := by
    unfold effect007
    iterate 15 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [addR32Imm32Effect_components, addR32R32Effect_components, andR32R32Effect_components,
        bswapR32Effect_components, movM64R64Effect_components, movR32M32LowEffect_components,
        movR32R32Effect_components, movR64M64Effect_components, movR64R64Effect_components,
        rolR32Effect_components, xorR32R32Effect_components, scratchComponents,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_imp,
        forall_and, forall_eq, or_true, true_or]
    all_goals sha1_norm [hs]
  apply (he.agrees.mono hfoot).widen
  · intro c hc hn
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | hc
    · cases hn
    · exact hc
  · intro a c hc hCov
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | hc
    · exact scratchComponents_stack (Or.inl (by decide +kernel)) hCov
    · exact ⟨c, hc, hCov⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
private theorem effect007_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut007 stack input H M))
    (he : (effect007 s).Holds s t) :
    Write.AllHold t (cut008 stack input H M) := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hin6 : (Operand.mem (input + 24) : Operand 32).read s =
      bswapSpec (scheduleWord M 6) := by
    rw [scheduleWord_initial M 6 (by decide +kernel)]
    exact hf.words 6
  sha1_norm at hin6
  have hfull : ∀ w ∈ (effect007 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect007
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  simp only [cut007, Write.AllHold] at hw
  obtain ⟨h0,h1,h2,h6,h10,h12,h15,hM4,hM8,hM56,hM64,hM88,hM116,hM120,hM124,hM144,hM152⟩ := hw
  sha1_norm at hs h0 h1 h2 h6 h10 h12 h15 hM4 hM8 hM56 hM64 hM88 hM116 hM120 hM124 hM144 hM152
  simp only [cut008, Write.AllHold, ← ho.read_reg, ← ho.read_mem]
  sha1_norm
    [effect007,hs,hin6,h0,h1,h2,h6,h10,h12,h15,hM4,hM8,hM56,hM64,hM88,
      hM116,hM120,hM124,hM144,hM152,
    movR32M32LowEffect, leaSpec, bswap32_bswap32,
    read32_memStore64_low, extractLsb'_zero_eq_setWidth,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
    BitVec.shiftLeft_zero, BitVec.add_zero]
  have hWork := workingAfter_step_a_values M H 2 (by decide +kernel)
  simp only [Nat.reduceAdd, sha1_f_choice (t := ⟨6, by decide⟩) (by decide),
    sha1_K_choice (t := ⟨6, by decide⟩) (by decide)] at hWork
  rw [sha1Ch_eq, BitVec.and_comm _ (_ ^^^ _), BitVec.xor_comm] at hWork
  change (workingAfter M H 7).a = (workingAfter M H 6).a.rotateLeft 5 +
    (((workingAfter M H 4).a.rotateLeft 30 ^^^ (workingAfter M H 3).a.rotateLeft 30) &&&
      (workingAfter M H 5).a ^^^ (workingAfter M H 3).a.rotateLeft 30) +
    (workingAfter M H 2).a.rotateLeft 30 + (0x5a827999#32) +
    scheduleWord M 6 at hWork
  rw [hWork]
  ac_rfl

set_option maxHeartbeats 800000 in
theorem segment007 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x102671 0x1026a1 cut007 cut008 := by
  have hout : ∀ d : Nat, d ≤ bytes007.length →
      0x102671 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      simp only [bytes007, List.length_cons, List.length_nil] at hd <;>
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  apply Segment.of_block (fun _ _ _ _ ↦ effect007)
    (fun stack input H M ↦ block007 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 0x2671) bytes007,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact he.rip.trans (by rfl)
  · intro stack input H M s t _ hf _ he
    exact effect007_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect007_words hf hw he

def bytes008 : List UInt8 :=
  [0x48, 0x8b, 0x44, 0x24, 0x40, 0x8b, 0x40, 0x1c, 0xf, 0xc8, 0x49, 0x89, 0xc1, 0x48, 0x89, 0x44,
    0x24, 0x28, 0xc1, 0xc1, 0x1e, 0x89, 0xf8, 0xc1, 0xc0, 0x5, 0x41, 0x89, 0xc8, 0x41, 0x31, 0xd0,
    0x45, 0x21, 0xd0, 0x41, 0x31, 0xd0, 0x44, 0x1, 0xce, 0x44, 0x1, 0xc6, 0x1, 0xf0, 0x5, 0x99,
    0x79, 0x82, 0x5a]

set_option maxHeartbeats 800000 in
def effect008 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    ((movR64M64Effect 0x1026a1 0 (.sib 4 none 0 (.d8 0x40)))) (movR32M32LowEffect 0x1026a6 0 (.base
    0 (.d8 0x1c)))) (bswapR32Effect 0x1026a9 2 0)) (movR64R64Effect 0x1026ab 9 0)) (movM64R64Effect
    0x1026ae 0 (.sib 4 none 0 (.d8 0x28)))) (rolR32Effect 0x1026b3 3 1 30)) (movR32R32Effect
    0x1026b6 2 0 7)) (rolR32Effect 0x1026b8 3 0 5)) (movR32R32Effect 0x1026bb 3 8 1))
    (xorR32R32Effect 0x1026be 3 8 2)) (andR32R32Effect 0x1026c1 3 8 10)) (xorR32R32Effect 0x1026c4 3
    8 2)) (addR32R32Effect 0x1026c7 3 6 9)) (addR32R32Effect 0x1026ca 3 6 8)) (addR32R32Effect
    0x1026cd 2 0 6)) (addEaxImm32Effect 0x1026cf 0x5a827999)

set_option maxHeartbeats 1600000 in
private theorem block008 [Bindings] (boundary : ReturnBoundary)
    (stack input : BitVec 64) (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes008.length → 0x1026a1 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x1026a1 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut008 stack input H M))
      (codeRange 0x1026a1 bytes008) effect008 := by
  unfold bytes008 at hout ⊢
  sha1_run_begin (mov_r64_m64_effect_step 0x1026a1 0x48 (by unfold RexWPrefix; decide +kernel) 0
    (.sib 4 none 0 (.d8 0x40)) (by decide +kernel) (by decide +kernel) (by decide +kernel) )
  sha1_run_then (mov_r32_m32_low_effect_step 0x1026a6 0 (.base 0 (.d8 0x1c)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) )
  sha1_run_then (bswap_r32_effect_step 0x1026a9 0xc8 (by decide +kernel))
  sha1_run_then (mov_r64_r64_effect_step 0x1026ab 0x49 0xc1 (by unfold RexWPrefix; decide +kernel)
    (by decide +kernel) )
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step 0x1026ae 0x48
    (by unfold RexWPrefix; decide +kernel) 0 (.sib 4 none 0 (.d8 0x28)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) )
  sha1_run_then (rol_r32_imm8_effect_step 0x1026b3 0xc1 0x1e (by decide +kernel) (by decide +kernel)
    )
  sha1_run_then (mov_r32_r32_effect_step 0x1026b6 0xf8 (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x1026b8 0xc0 0x5 (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x1026bb 0x41 0xc8
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) )
  sha1_run_then (xor_r32_r32_rex_effect_step 0x1026be 0x41 0xd0
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) )
  sha1_run_then (and_r32_r32_rex_effect_step 0x1026c1 0x45 0xd0
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) )
  sha1_run_then (xor_r32_r32_rex_effect_step 0x1026c4 0x41 0xd0
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) )
  sha1_run_then (add_r32_r32_rex_effect_step 0x1026c7 0x44 0xce
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) )
  sha1_run_then (add_r32_r32_rex_effect_step 0x1026ca 0x44 0xc6
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) )
  sha1_run_then (add_r32_r32_effect_step 0x1026cd 0xf0 (by decide +kernel))
  sha1_run_then (add_eax_imm32_effect_step 0x1026cf 0x5a827999)
  sha1_run_finish [effect008]

set_option maxHeartbeats 800000 in
private theorem effect008_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (he : (effect008 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  sha1_norm at hs
  have hfoot : ∀ c ∈ (effect008 s).components, c ∈ [.mem (stack + 40) 8] ++ scratchComponents stack
    := by
    unfold effect008
    iterate 15 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [addEaxImm32Effect_components, addR32R32Effect_components, andR32R32Effect_components,
        bswapR32Effect_components, movM64R64Effect_components, movR32M32LowEffect_components,
        movR32R32Effect_components, movR64M64Effect_components, movR64R64Effect_components,
        rolR32Effect_components, xorR32R32Effect_components, scratchComponents,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_imp,
        forall_and, forall_eq, or_true, true_or]
    all_goals sha1_norm [hs]
  apply (he.agrees.mono hfoot).widen
  · intro c hc hn
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | hc
    · cases hn
    · exact hc
  · intro a c hc hCov
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | hc
    · exact scratchComponents_stack (Or.inl (by decide +kernel)) hCov
    · exact ⟨c, hc, hCov⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
private theorem effect008_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut008 stack input H M))
    (he : (effect008 s).Holds s t) :
    Write.AllHold t (cut009 stack input H M) := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hin7 : (Operand.mem (input + 28) : Operand 32).read s =
      bswapSpec (scheduleWord M 7) := by
    rw [scheduleWord_initial M 7 (by decide +kernel)]
    exact hf.words 7
  sha1_norm at hin7
  have hfull : ∀ w ∈ (effect008 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect008
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  simp only [cut008, Write.AllHold] at hw
  obtain ⟨h1,h2,h6,h7,h10,h12,h15,hM4,hM8,hM32,hM56,hM64,hM88,hM116,hM120,hM124,hM144,hM152⟩ := hw
  sha1_norm at hs h1 h2 h6 h7 h10 h12 h15 hM4 hM8 hM32 hM56 hM64 hM88 hM116 hM120 hM124 hM144 hM152
  simp only [cut009, Write.AllHold, ← ho.read_reg, ← ho.read_mem]
  sha1_norm
    [effect008,hs,hin7,h1,h2,h6,h7,h10,h12,h15,hM4,hM8,hM32,hM56,hM64,hM88,
      hM116,hM120,hM124,hM144,hM152,
    movR32M32LowEffect, leaSpec, bswap32_bswap32,
    read32_memStore64_low, extractLsb'_zero_eq_setWidth,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
    BitVec.shiftLeft_zero, BitVec.add_zero]
  have hWork := workingAfter_step_a_values M H 3 (by decide +kernel)
  simp only [Nat.reduceAdd, sha1_f_choice (t := ⟨7, by decide⟩) (by decide),
    sha1_K_choice (t := ⟨7, by decide⟩) (by decide)] at hWork
  rw [sha1Ch_eq, BitVec.and_comm _ (_ ^^^ _), BitVec.xor_comm] at hWork
  change (workingAfter M H 8).a = (workingAfter M H 7).a.rotateLeft 5 +
    (((workingAfter M H 5).a.rotateLeft 30 ^^^ (workingAfter M H 4).a.rotateLeft 30) &&&
      (workingAfter M H 6).a ^^^ (workingAfter M H 4).a.rotateLeft 30) +
    (workingAfter M H 3).a.rotateLeft 30 + (0x5a827999#32) +
    scheduleWord M 7 at hWork
  rw [hWork]
  ac_rfl

set_option maxHeartbeats 800000 in
theorem segment008 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x1026a1 0x1026d4 cut008 cut009 := by
  have hout : ∀ d : Nat, d ≤ bytes008.length →
      0x1026a1 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      simp only [bytes008, List.length_cons, List.length_nil] at hd <;>
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  apply Segment.of_block (fun _ _ _ _ ↦ effect008)
    (fun stack input H M ↦ block008 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 0x26a1) bytes008,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact he.rip.trans (by rfl)
  · intro stack input H M s t _ hf _ he
    exact effect008_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect008_words hf hw he

def bytes009 : List UInt8 :=
  [0x41, 0xc1, 0xc2, 0x1e, 0x44, 0x89, 0xd6, 0x31, 0xce, 0x21, 0xfe, 0x4c, 0x8b, 0x44, 0x24, 0x40,
    0x45, 0x8b, 0x70, 0x20, 0x41, 0xf, 0xce, 0x31, 0xce, 0x44, 0x1, 0xf2, 0x1, 0xf2, 0x89, 0xc6,
    0xc1, 0xc6, 0x5, 0x1, 0xd6, 0x81, 0xc6, 0x99, 0x79, 0x82, 0x5a]

set_option maxHeartbeats 800000 in
def effect009 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq ((rolR32Effect 0x1026d4 4 10 30))
    (movR32R32Effect 0x1026d8 3 6 10)) (xorR32R32Effect 0x1026db 2 6 1)) (andR32R32Effect 0x1026dd 2
    6 7)) (movR64M64Effect 0x1026df 8 (.sib 4 none 0 (.d8 0x40)))) (movR32M32Effect 0x1026e4 14
    (.base 8 (.d8 0x20)))) (bswapR32Effect 0x1026e8 3 14)) (xorR32R32Effect 0x1026eb 2 6 1))
    (addR32R32Effect 0x1026ed 3 2 14)) (addR32R32Effect 0x1026f0 2 2 6)) (movR32R32Effect 0x1026f2 2
    6 0)) (rolR32Effect 0x1026f4 3 6 5)) (addR32R32Effect 0x1026f7 2 6 2)) (addR32Imm32Effect
    0x1026f9 6 6 0x5a827999)

set_option maxHeartbeats 1600000 in
private theorem block009 [Bindings] (boundary : ReturnBoundary)
    (stack input : BitVec 64) (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes009.length → 0x1026d4 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x1026d4 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut009 stack input H M))
      (codeRange 0x1026d4 bytes009) effect009 := by
  unfold bytes009 at hout ⊢
  sha1_run_begin (rol_r32_imm8_rex_effect_step 0x1026d4 0x41 0xc2 0x1e
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel) )
  sha1_run_then (mov_r32_r32_rex_effect_step 0x1026d8 0x44 0xd6
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) )
  sha1_run_then (xor_r32_r32_effect_step 0x1026db 0xce (by decide +kernel))
  sha1_run_then (and_r32_r32_effect_step 0x1026dd 0xfe (by decide +kernel))
  sha1_run_then (mov_r64_m64_effect_step 0x1026df 0x4c (by unfold RexWPrefix; decide +kernel) 0
    (.sib 4 none 0 (.d8 0x40)) (by decide +kernel) (by decide +kernel) (by decide +kernel) )
  sha1_run_then (mov_r32_m32_effect_step 0x1026e4 0x45 (by unfold RexNoWPrefix; decide +kernel) 6
    (.base 8 (.d8 0x20)) (by decide +kernel) (by decide +kernel) (by decide +kernel) )
  sha1_run_then (bswap_r32_rex_effect_step 0x1026e8 0x41 (by unfold RexNoWPrefix; decide +kernel)
    0xce (by decide +kernel) )
  sha1_run_then (xor_r32_r32_effect_step 0x1026eb 0xce (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x1026ed 0x44 0xf2
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) )
  sha1_run_then (add_r32_r32_effect_step 0x1026f0 0xf2 (by decide +kernel))
  sha1_run_then (mov_r32_r32_effect_step 0x1026f2 0xc6 (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x1026f4 0xc6 0x5 (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x1026f7 0xd6 (by decide +kernel))
  sha1_run_then (add_r32_imm32_effect_step 0x1026f9 0xc6 0x5a827999 (by decide +kernel)
    (by decide +kernel) )
  sha1_run_finish [effect009]

set_option maxHeartbeats 800000 in
private theorem effect009_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (he : (effect009 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  sha1_norm at hs
  have hfoot : ∀ c ∈ (effect009 s).components, c ∈ scratchComponents stack := by
    unfold effect009
    iterate 13 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [addR32Imm32Effect_components, addR32R32Effect_components, andR32R32Effect_components,
        bswapR32Effect_components, movR32M32Effect_components, movR32R32Effect_components,
        movR64M64Effect_components, rolR32Effect_components, xorR32R32Effect_components,
        scratchComponents,
        List.mem_cons, List.not_mem_nil, or_false, or_imp,
        forall_and, forall_eq, or_true, true_or]
    all_goals sha1_norm [hs]
  exact he.agrees.mono hfoot

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
private theorem effect009_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut009 stack input H M))
    (he : (effect009 s).Holds s t) :
    Write.AllHold t (cut010 stack input H M) := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hin8 : (Operand.mem (input + 32) : Operand 32).read s =
      bswapSpec (scheduleWord M 8) := by
    rw [scheduleWord_initial M 8 (by decide +kernel)]
    exact hf.words 8
  sha1_norm at hin8
  have hfull : ∀ w ∈ (effect009 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect009
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  simp only [cut009, Write.AllHold] at hw
  obtain ⟨h0,h1,h2,h7,h10,h12,h15,hM4,hM8,hM32,hM40,hM56,hM64,hM88,hM116,hM120,hM124,hM144,hM152⟩ :=
    hw
  sha1_norm at hs h0 h1 h2 h7 h10 h12 h15 hM4 hM8 hM32 hM40 hM56 hM64 hM88 hM116 hM120 hM124 hM144
  sha1_norm at hM152
  simp only [cut010, Write.AllHold, ← ho.read_reg, ← ho.read_mem]
  sha1_norm
    [effect009,hs,hin8,h0,h1,h2,h7,h10,h12,h15,hM4,hM8,hM32,hM40,hM56,hM64,hM88,
      hM116,hM120,hM124,hM144,hM152,
    movR32M32LowEffect, leaSpec, bswap32_bswap32,
    read32_memStore64_low, extractLsb'_zero_eq_setWidth,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
    BitVec.shiftLeft_zero, BitVec.add_zero]
  have hWork := workingAfter_step_a_values M H 4 (by decide +kernel)
  simp only [Nat.reduceAdd, sha1_f_choice (t := ⟨8, by decide⟩) (by decide),
    sha1_K_choice (t := ⟨8, by decide⟩) (by decide)] at hWork
  rw [sha1Ch_eq, BitVec.and_comm _ (_ ^^^ _), BitVec.xor_comm] at hWork
  change (workingAfter M H 9).a = (workingAfter M H 8).a.rotateLeft 5 +
    (((workingAfter M H 6).a.rotateLeft 30 ^^^ (workingAfter M H 5).a.rotateLeft 30) &&&
      (workingAfter M H 7).a ^^^ (workingAfter M H 5).a.rotateLeft 30) +
    (workingAfter M H 4).a.rotateLeft 30 + (0x5a827999#32) +
    scheduleWord M 8 at hWork
  rw [hWork]
  ac_rfl

set_option maxHeartbeats 800000 in
theorem segment009 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x1026d4 0x1026ff cut009 cut010 := by
  have hout : ∀ d : Nat, d ≤ bytes009.length →
      0x1026d4 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      simp only [bytes009, List.length_cons, List.length_nil] at hd <;>
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  apply Segment.of_block (fun _ _ _ _ ↦ effect009)
    (fun stack input H M ↦ block009 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 0x26d4) bytes009,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact he.rip.trans (by rfl)
  · intro stack input H M s t _ hf _ he
    exact effect009_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect009_words hf hw he

theorem segments005_014 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x1025f2 0x1027f8 cut005 cut015 := by
  have h0 := segment005 boundary hOutside
  have h1 := h0.seq (segment006 boundary hOutside)
  have h2 := h1.seq (segment007 boundary hOutside)
  have h3 := h2.seq (segment008 boundary hOutside)
  have h4 := h3.seq (segment009 boundary hOutside)
  exact h4.seq (segments010_014 boundary hOutside)

end Sha1.Proofs.Compress.Machine
