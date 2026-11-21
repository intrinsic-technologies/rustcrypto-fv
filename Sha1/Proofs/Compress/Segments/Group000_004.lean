import Sha1.Proofs.Compress.Machine.Run
import Sha1.Proofs.Compress.Segments.Segment003
import Sha1.Proofs.Compress.Rounds.Scalar
import Sha1.Proofs.Common.Instructions.MovStore.Triple
import X86Proofs.Instructions.Mov.Generated.RM.Triple
import X86Proofs.Instructions.Bswap.Generated.R.Triple
import X86Proofs.Instructions.Lea.Generated.RM.Triple
import X86Proofs.Instructions.Add.Generated.Imm32.Triple

namespace Sha1.Proofs.Compress.Machine
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Spec.Program
open Sha1.Proofs.Compress.Rounds

def bytes000 : List UInt8 :=
  [0x44, 0x89, 0x5c, 0x24, 0x74, 0x4c, 0x89, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x89, 0x74,
    0x24, 0x40, 0x89, 0xd3, 0x89, 0xc2, 0x89, 0x44, 0x24, 0x7c]

def effect000 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq ((movM32R32Effect 0x102530 11 (.sib 4
    none 0 (.d8 0x74)))) (movM64R64Effect 0x102535 8 (.sib 4 none 0 (.d32 0x98)))) (movM64R64Effect
    0x10253d 6 (.sib 4 none 0 (.d8 0x40)))) (movR32R32Effect 0x102542 2 3 2)) (movR32R32Effect
    0x102544 2 2 0)) (movM32R32LowEffect 0x102546 0 (.sib 4 none 0 (.d8 0x7c)))

set_option maxHeartbeats 800000 in
theorem block000 [Bindings] (boundary : ReturnBoundary) (stack input : BitVec 64)
    (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes000.length →
      0x102530 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x102530 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut000 stack input H M))
      (codeRange 0x102530 bytes000) effect000 := by
  unfold bytes000 at hout ⊢
  sha1_run_begin (Sha1.Proofs.Common.Instructions.MovStore.mov_m32_r32_effect_step 0x102530 0x44
    (by unfold RexNoWPrefix; decide +kernel) 3 (.sib 4 none 0 (.d8 0x74)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step 0x102535 0x4c
    (by unfold RexWPrefix; decide +kernel) 0 (.sib 4 none 0 (.d32 0x98)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step 0x10253d 0x48
    (by unfold RexWPrefix; decide +kernel) 6 (.sib 4 none 0 (.d8 0x40)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_effect_step 0x102542 0xd3 (by decide +kernel))
  sha1_run_then (mov_r32_r32_effect_step 0x102544 0xc2 (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m32_r32_low_effect_step 0x102546 0
    (.sib 4 none 0 (.d8 0x7c)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_finish [effect000]

def bytes001 : List UInt8 :=
  [0x44, 0x8b, 0x3e, 0x8b, 0x46, 0x04, 0x41, 0x0f, 0xcf, 0x0f, 0xc8, 0x41, 0x89, 0xc4, 0x89, 0x44,
    0x24, 0x58, 0x8b, 0x6e, 0x08, 0x0f, 0xcd, 0x8b, 0x46, 0x0c, 0x0f, 0xc8, 0x49, 0x89, 0xc1, 0x48,
    0x89, 0x44, 0x24, 0x38, 0x8b, 0x46, 0x10, 0x0f, 0xc8, 0x41, 0x89, 0xc6, 0x89, 0x44, 0x24, 0x08]

def effect001 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    ((movR32M32Effect 0x10254a 15 (.base 6 .none))) (movR32M32LowEffect 0x10254d 0 (.base 6 (.d8
    0x4)))) (bswapR32Effect 0x102550 3 15)) (bswapR32Effect 0x102553 2 0)) (movR32R32Effect 0x102555
    3 12 0)) (movM32R32LowEffect 0x102558 0 (.sib 4 none 0 (.d8 0x58)))) (movR32M32LowEffect
    0x10255c 5 (.base 6 (.d8 0x8)))) (bswapR32Effect 0x10255f 2 5)) (movR32M32LowEffect 0x102561 0
    (.base 6 (.d8 0xc)))) (bswapR32Effect 0x102564 2 0)) (movR64R64Effect 0x102566 9 0))
    (movM64R64Effect 0x102569 0 (.sib 4 none 0 (.d8 0x38)))) (movR32M32LowEffect 0x10256e 0 (.base 6
    (.d8 0x10)))) (bswapR32Effect 0x102571 2 0)) (movR32R32Effect 0x102573 3 14 0))
    (movM32R32LowEffect 0x102576 0 (.sib 4 none 0 (.d8 0x8)))

set_option maxHeartbeats 800000 in
theorem block001 [Bindings] (boundary : ReturnBoundary) (stack input : BitVec 64)
    (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes001.length →
      0x10254a + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x10254a ∧ FrameData stack input M s ∧
        Write.AllHold s (cut001 stack input H M))
      (codeRange 0x10254a bytes001) effect001 := by
  unfold bytes001 at hout ⊢
  sha1_run_begin (mov_r32_m32_effect_step 0x10254a 0x44 (by unfold RexNoWPrefix; decide +kernel) 7
    (.base 6 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_m32_low_effect_step 0x10254d 0 (.base 6 (.d8 0x4)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel))
  sha1_run_then (bswap_r32_rex_effect_step 0x102550 0x41 (by unfold RexNoWPrefix; decide +kernel)
    0xcf (by decide +kernel))
  sha1_run_then (bswap_r32_effect_step 0x102553 0xc8 (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x102555 0x41 0xc4
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m32_r32_low_effect_step 0x102558 0
    (.sib 4 none 0 (.d8 0x58)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_m32_low_effect_step 0x10255c 5 (.base 6 (.d8 0x8)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel))
  sha1_run_then (bswap_r32_effect_step 0x10255f 0xcd (by decide +kernel))
  sha1_run_then (mov_r32_m32_low_effect_step 0x102561 0 (.base 6 (.d8 0xc)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel))
  sha1_run_then (bswap_r32_effect_step 0x102564 0xc8 (by decide +kernel))
  sha1_run_then (mov_r64_r64_effect_step 0x102566 0x49 0xc1 (by unfold RexWPrefix; decide +kernel)
    (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step 0x102569 0x48
    (by unfold RexWPrefix; decide +kernel) 0 (.sib 4 none 0 (.d8 0x38)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_m32_low_effect_step 0x10256e 0 (.base 6 (.d8 0x10)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel))
  sha1_run_then (bswap_r32_effect_step 0x102571 0xc8 (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x102573 0x41 0xc6
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m32_r32_low_effect_step 0x102576 0
    (.sib 4 none 0 (.d8 0x8)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_finish [effect001]

def bytes002 : List UInt8 :=
  [0x44, 0x89, 0xd8, 0xc1, 0xc0, 0x05, 0x89, 0xd9, 0x44, 0x31, 0xd1, 0x44, 0x21, 0xc1, 0x44, 0x31,
    0xd1, 0x44, 0x89, 0x54, 0x24, 0x78, 0x01, 0xd0, 0x01, 0xc8, 0x44, 0x89, 0xc2, 0xc1, 0xc2, 0x1e,
    0x41, 0x8d, 0x3c, 0x07, 0x81, 0xc7, 0x99, 0x79, 0x82, 0x5a]

def effect002 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq (Effect.seq (Effect.seq ((movR32R32Effect 0x10257a 3 0 11))
    (rolR32Effect 0x10257d 3 0 5)) (movR32R32Effect 0x102580 2 1 3)) (xorR32R32Effect 0x102582 3 1
    10)) (andR32R32Effect 0x102585 3 1 8)) (xorR32R32Effect 0x102588 3 1 10)) (movM32R32Effect
    0x10258b 10 (.sib 4 none 0 (.d8 0x78)))) (addR32R32Effect 0x102590 2 0 2)) (addR32R32Effect
    0x102592 2 0 1)) (movR32R32Effect 0x102594 3 2 8)) (rolR32Effect 0x102597 3 2 30)) (leaR32Effect
    0x10259a 4 7 (.sib 15 (some 0) 0 .none))) (addR32Imm32Effect 0x10259e 6 7 0x5a827999)

set_option maxHeartbeats 800000 in
theorem block002 [Bindings] (boundary : ReturnBoundary) (stack input : BitVec 64)
    (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes002.length →
      0x10257a + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x10257a ∧ FrameData stack input M s ∧
        Write.AllHold s (cut002 stack input H M))
      (codeRange 0x10257a bytes002) effect002 := by
  unfold bytes002 at hout ⊢
  sha1_run_begin (mov_r32_r32_rex_effect_step 0x10257a 0x44 0xd8
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x10257d 0xc0 0x5 (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_effect_step 0x102580 0xd9 (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102582 0x44 0xd1
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (and_r32_r32_rex_effect_step 0x102585 0x44 0xc1
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102588 0x44 0xd1
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m32_r32_effect_step 0x10258b 0x44
    (by unfold RexNoWPrefix; decide +kernel) 2 (.sib 4 none 0 (.d8 0x78)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x102590 0xd0 (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x102592 0xc8 (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x102594 0x44 0xc2
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x102597 0xc2 0x1e (by decide +kernel)
    (by decide +kernel))
  sha1_run_then (lea_r32_rex_effect_step 0x10259a 0x41 (by unfold RexNoWPrefix; decide +kernel) 7
    (.sib 15 (some 0) 0 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_imm32_effect_step 0x10259e 0xc7 0x5a827999 (by decide +kernel)
    (by decide +kernel))
  sha1_run_finish [effect002]

attribute [local irreducible] Standards.NIST.SHA1.messageSchedule

set_option maxHeartbeats 800000 in
theorem effect000_words {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut000 stack input H M))
    (he : (effect000 s).Holds s t) :
    Write.AllHold t (cut001 stack input H M) := by
  have hfull : ∀ w ∈ (effect000 s).writes, w.Full := by x86_norm [effect000]
  have ho := he.obsAfter hfull true
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  x86_norm at hs
  simp only [cut000, Write.AllHold] at hw
  obtain ⟨h0,h2,h6,h8,h10,h11⟩ := hw
  x86_norm at h0 h2 h6 h8 h10 h11
  simp only [cut001, Write.AllHold, ← ho.read_reg, ← ho.read_mem]
  x86_norm [effect000, hs]
  simp only [h0,h2,h6,h8,h10,h11]
  simp (config := {decide := true}) only [Operand.read,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    true_and]
  rw [read32_memStore64_low]
  change BitVec.setWidth 32 s.GPR[gprIndex 8#5] = H[1]
  exact h8

set_option maxHeartbeats 800000 in
theorem effect001_words {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut001 stack input H M))
    (he : (effect001 s).Holds s t) :
    Write.AllHold t (cut002 stack input H M) := by
  have hfull : ∀ w ∈ (effect001 s).writes, w.Full := by x86_norm [effect001]
  have ho := he.obsAfter hfull true
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  x86_norm at hs
  simp only [cut001, Write.AllHold] at hw
  obtain ⟨h2,h3,h6,h8,h10,h11,hM64,hM116,hM124,hM152⟩ := hw
  x86_norm at h2 h3 h6 h8 h10 h11 hM64 hM116 hM124 hM152
  have h0 := hf.words 0
  have h1 := hf.words 1
  have hW2 := hf.words 2
  have hW3 := hf.words 3
  have hW4 := hf.words 4
  simp only [cut002, Write.AllHold, ← ho.read_reg, ← ho.read_mem]
  x86_norm [effect001,hs,h6]
  simp only [h2,h3,h8,h10,h11,hM64,hM116,hM124,hM152]
  have hload (mem : Ram) (offset : Nat) {n : Nat} (v : BitVec n)
      (j : Nat) (hOffset : offset + n / 8 ≤ 160) (hJ : j + 4 ≤ 64) :
      memLoad (memStore mem (stack + BitVec.ofNat 64 offset) v)
        (input + BitVec.ofNat 64 j) 32 =
        memLoad mem (input + BitVec.ofNat 64 j) 32 := by
    apply memLoad_memStore_of_rangeApart
    exact (by
      intro i hi k hk heq
      apply hf.apart (offset + i) (by omega) (j + k) (by omega)
      simpa only [BitVec.ofNat_add, ← BitVec.add_assoc] using heq)
  have h88_8 := fun (mem : Ram) (v : BitVec 32) => hload mem 88 v 8 (by decide) (by decide)
  have h88_12 := fun (mem : Ram) (v : BitVec 32) => hload mem 88 v 12 (by decide) (by decide)
  have h88_16 := fun (mem : Ram) (v : BitVec 32) => hload mem 88 v 16 (by decide) (by decide)
  have h56_16 := fun (mem : Ram) (v : BitVec 64) => hload mem 56 v 16 (by decide) (by decide)
  simp only [h88_8,h88_12,h56_16]
  x86_norm [hs,h6]
  simp only [h88_16, read32_memStore64_low]
  x86_norm [hs,h6]
  simp (config := {decide := true}) only [BitVec.setWidth_setWidth_of_le,
    BitVec.setWidth_eq, ← BitVec.setWidth_eq_extractLsb']
  change (Operand.mem (input + 0) : Operand 32).read s = bswapSpec M[0] at h0
  change (Operand.mem (input + 4) : Operand 32).read s = bswapSpec M[1] at h1
  change (Operand.mem (input + 8) : Operand 32).read s = bswapSpec M[2] at hW2
  change (Operand.mem (input + 12) : Operand 32).read s = bswapSpec M[3] at hW3
  change (Operand.mem (input + 16) : Operand 32).read s = bswapSpec M[4] at hW4
  simp only [BitVec.ofNat_eq_ofNat] at h0 h1 hW2 hW3 hW4
  simp only [h0,h1,hW2,hW3,hW4]
  simp only [bswap32_bswap32, scheduleWord_initial M 0 (by decide),
    scheduleWord_initial M 1 (by decide), scheduleWord_initial M 2 (by decide),
    scheduleWord_initial M 3 (by decide), scheduleWord_initial M 4 (by decide)]
  repeat' apply And.intro
  all_goals rfl

set_option maxHeartbeats 800000 in
theorem effect002_words {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut002 stack input H M))
    (he : (effect002 s).Holds s t) :
    Write.AllHold t (cut003 stack input H M) := by
  have hfull : ∀ w ∈ (effect002 s).writes, w.Full := by
    x86_norm [effect002]
  have ho := he.obsAfter hfull true
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  x86_norm at hs
  simp only [cut002, Write.AllHold] at hw
  obtain ⟨h2, h3, h5, h8, h9, h10, h11, h12, h14, h15,
    hM8, hM56, hM64, hM88, hM116, hM124, hM152⟩ := hw
  x86_norm at h2 h3 h5 h8 h9 h10 h11 h12 h14 h15
  x86_norm at hM8 hM56 hM64 hM88 hM116 hM124 hM152
  simp only [cut003, Write.AllHold, ← ho.read_reg, ← ho.read_mem]
  x86_norm [effect002, hs]
  simp only [h2, h3, h5, h8, h9, h10, h11, h12, h14, h15,
    hM8, hM56, hM64, hM88, hM116, hM124, hM152]
  have hWork : (workingAfter M H 1).a = H[0].rotateLeft 5 +
      Standards.NIST.SHA2.SHA256.Ch H[1] H[2] H[3] + H[4] + 0x5a827999 +
      scheduleWord M 0 := by
    rw [workingAfter_step M H 0 (by decide), workingAfter_zero]
    change Standards.NIST.SHA1.ROTL 5 H[0] +
      Standards.NIST.SHA2.SHA256.Ch H[1] H[2] H[3] + H[4] + 0x5a827999 +
      scheduleWord M 0 = _
    rw [sha1Rotl_eq_rotateLeft 5 _ (by decide)]
  rw [hWork]
  generalize hA : H[0] = a at ⊢
  generalize hB : H[1] = b at ⊢
  generalize hC : H[2] = c at ⊢
  generalize hD : H[3] = d at ⊢
  generalize hE : H[4] = e at ⊢
  generalize hW : scheduleWord M 0 = w at h15 ⊢
  simp (config := {decide := true}) only [Operand.read, leaSpec,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
    BitVec.shiftLeft_zero, BitVec.add_zero] at h15 ⊢
  simp only [h15, sha1Ch_eq, true_and, and_true]
  simp only [BitVec.ofNat_eq_ofNat]
  ac_rfl

set_option maxHeartbeats 800000 in
theorem effect000_agrees {stack input : BitVec 64} {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (he : (effect000 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  x86_norm at hs
  have ha := he.agrees
  x86_norm [effect000,hs] at ha
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all (config := {decide := true}) only
      [Component.isMem, scratchComponents, x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hCov.elim
      | exact scratchComponents_stack (Or.inl (by decide)) hCov
      | exact scratchComponents_stack (Or.inr ⟨by decide, by decide⟩) hCov

set_option maxHeartbeats 800000 in
theorem effect001_agrees {stack input : BitVec 64} {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (he : (effect001 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  x86_norm at hs
  have ha := he.agrees
  x86_norm [effect001,hs] at ha
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all (config := {decide := true}) only
      [Component.isMem, scratchComponents, x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hCov.elim
      | exact scratchComponents_stack (Or.inl (by decide)) hCov
      | exact scratchComponents_stack (Or.inr ⟨by decide, by decide⟩) hCov

theorem effect002_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (he : (effect002 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  x86_norm at hs
  have ha := he.agrees
  x86_norm [effect002, hs, leaR32Effect] at ha
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all (config := {decide := true}) only [Component.isMem, scratchComponents,
      x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hCov.elim
    exact scratchComponents_stack (Or.inl (by decide)) hCov

theorem effect000_rip {s t : RamState} (he : (effect000 s).Holds s t) :
    t.RIP = 0x10254a := by
  exact he.rip.trans (by x86_norm [effect000])

theorem effect001_rip {s t : RamState} (he : (effect001 s).Holds s t) :
    t.RIP = 0x10257a := by
  exact he.rip.trans (by x86_norm [effect001])

theorem effect002_rip {s t : RamState} (he : (effect002 s).Holds s t) :
    t.RIP = 0x1025a4 := by
  exact he.rip.trans (by x86_norm [effect002])

theorem segment000 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x102530 0x10254a cut000 cut001 := by
  have hout : ∀ d : Nat, d ≤ bytes000.length →
      0x102530 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      simp only [bytes000, List.length_cons, List.length_nil] at hd <;>
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  apply Segment.of_block (fun _ _ _ _ => effect000)
    (fun stack input H M => block000 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 0x2530) bytes000,
      x ∈ Extracted.programImage
    exact program_text_subset 0x2530 (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect000_rip he
  · intro stack input H M s t _ hf _ he
    exact effect000_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect000_words hf hw he

theorem segment001 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x10254a 0x10257a cut001 cut002 := by
  have hout : ∀ d : Nat, d ≤ bytes001.length →
      0x10254a + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      simp only [bytes001, List.length_cons, List.length_nil] at hd <;>
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  apply Segment.of_block (fun _ _ _ _ => effect001)
    (fun stack input H M => block001 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 0x254a) bytes001,
      x ∈ Extracted.programImage
    exact program_text_subset 0x254a (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect001_rip he
  · intro stack input H M s t _ hf _ he
    exact effect001_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect001_words hf hw he

theorem segment002 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x10257a 0x1025a4 cut002 cut003 := by
  have hout : ∀ d : Nat, d ≤ bytes002.length →
      0x10257a + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      simp only [bytes002, List.length_cons, List.length_nil] at hd <;>
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  apply Segment.of_block (fun _ _ _ _ => effect002)
    (fun stack input H M => block002 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 0x257a) bytes002,
      x ∈ Extracted.programImage
    exact program_text_subset 0x257a (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect002_rip he
  · intro stack input H M s t _ hf _ he
    exact effect002_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect002_words hf hw he

end Sha1.Proofs.Compress.Machine

namespace Sha1.Proofs.Compress.Machine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Spec.Program
open Standards.NIST.SHA1
open Sha1.Proofs.Compress.Rounds

attribute [local irreducible] workingAfter scheduleWord messageSchedule

def bytes003 : List UInt8 :=
  [0x89, 0xf8, 0xc1, 0xc0, 0x05, 0x89, 0xd1, 0x31, 0xd9, 0x44, 0x21, 0xd9, 0x31, 0xd9, 0x48, 0x89,
    0x9c, 0x24, 0x90, 0x00, 0x00, 0x00, 0x44, 0x01, 0xd1, 0x44, 0x01, 0xe1, 0x01, 0xc8, 0x05, 0x99,
    0x79, 0x82, 0x5a]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem block003 [Bindings] (boundary : ReturnBoundary) (stack input : BitVec 64)
    (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes003.length →
      0x1025a4 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x1025a4 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut003 stack input H M))
      (codeRange 0x1025a4 bytes003) effect003 := by
  have hRaw : AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x1025a4 ∧ FrameData stack input M s)
      (codeRange 0x1025a4 bytes003) effect003 := by
    unfold bytes003 at hout ⊢
    sha1_run_begin (mov_r32_r32_effect_step 0x1025a4 0xf8 (by decide +kernel))
    sha1_run_then (rol_r32_imm8_effect_step 0x1025a6 0xc0 0x5 (by decide +kernel)
      (by decide +kernel))
    sha1_run_then (mov_r32_r32_effect_step 0x1025a9 0xd1 (by decide +kernel))
    sha1_run_then (xor_r32_r32_effect_step 0x1025ab 0xd9 (by decide +kernel))
    sha1_run_then (and_r32_r32_rex_effect_step 0x1025ad 0x44 0xd9
      (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
    sha1_run_then (xor_r32_r32_effect_step 0x1025b0 0xd9 (by decide +kernel))
    sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step 0x1025b2 0x48
      (by unfold RexWPrefix; decide +kernel) 3 (.sib 4 none 0 (.d32 0x90)) (by decide +kernel)
      (by decide +kernel) (by decide +kernel))
    sha1_run_then (add_r32_r32_rex_effect_step 0x1025ba 0x44 0xd1
      (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
    sha1_run_then (add_r32_r32_rex_effect_step 0x1025bd 0x44 0xe1
      (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
    sha1_run_then (add_r32_r32_effect_step 0x1025c0 0xc8 (by decide +kernel))
    sha1_run_then (add_eax_imm32_effect_step 0x1025c2 0x5a827999)
    sha1_run_finish [effect003]
  intro s hr hc hp
  exact hRaw s hr hc ⟨hp.1, hp.2.1⟩

theorem effect003_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (he : (effect003 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hfoot : ∀ c ∈ (effect003 s).components,
      c ∈ [.mem ((Operand.reg 4 : Operand 64).read s + 144) 8,
        .reg 0, .reg 1, .flags, .rip] := by
    unfold effect003
    iterate 10 apply components_seq_of
    all_goals simp (config := {decide := true}) only
      [movM64R64Effect_components, movR32R32Effect_components,
        rolR32Effect_components, xorR32R32Effect_components,
        andR32R32Effect_components, addR32R32Effect_components,
        addEaxImm32Effect_components, List.mem_cons, List.not_mem_nil,
        or_false, or_imp, forall_and, forall_eq, or_true]
    all_goals x86_norm
  have ha := he.agrees.mono hfoot
  rw [hs] at ha
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all (config := {decide := true}) only
      [Component.isMem, scratchComponents, x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hCov.elim
      | exact scratchComponents_stack (Or.inr ⟨by decide, by decide⟩) hCov

theorem segment003 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x1025a4 0x1025c7 cut003 cut004 := by
  have hout : ∀ d : Nat, d ≤ bytes003.length →
      0x1025a4 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      simp only [bytes003, List.length_cons, List.length_nil] at hd <;>
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  apply Segment.of_block (fun _ _ _ _ => effect003)
    (fun stack input H M => block003 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 0x25a4) bytes003,
      x ∈ Extracted.programImage
    exact program_text_subset 0x25a4 (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect003_rip he
  · intro stack input H M s t _ hf _ he
    exact effect003_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect003_words hf hw he

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Spec.Program
open Sha1.Proofs.Compress.Rounds

end Sha1.Proofs.Compress.Machine

namespace Sha1.Proofs.Compress.Machine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Spec.Program
open Standards.NIST.SHA1
open Sha1.Proofs.Compress.Rounds

attribute [local irreducible] workingAfter scheduleWord messageSchedule

def bytes004 : List UInt8 :=
  [0x44, 0x89, 0xd9, 0xc1, 0xc1, 0x1e, 0x89, 0xce, 0x31, 0xd6, 0x21, 0xfe, 0x31, 0xd6, 0x49, 0x89,
    0xec, 0x01, 0xde, 0x01, 0xee, 0x41, 0x89, 0xc0, 0x41, 0xc1, 0xc0, 0x05, 0x44, 0x01, 0xc6, 0x81,
    0xc6, 0x99, 0x79, 0x82, 0x5a, 0xc1, 0xc7, 0x1e, 0x41, 0x89, 0xf8]

set_option maxHeartbeats 800000 in
def effect004 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq ((movR32R32Effect
    0x1025c7 3 1 11)) (rolR32Effect 0x1025ca 3 1 30)) (movR32R32Effect 0x1025cd 2 6 1))
    (xorR32R32Effect 0x1025cf 2 6 2)) (andR32R32Effect 0x1025d1 2 6 7)) (xorR32R32Effect 0x1025d3 2
    6 2)) (movR64R64Effect 0x1025d5 12 5)) (addR32R32Effect 0x1025d8 2 6 3)) (addR32R32Effect
    0x1025da 2 6 5)) (movR32R32Effect 0x1025dc 3 8 0)) (rolR32Effect 0x1025df 4 8 5))
    (addR32R32Effect 0x1025e3 3 6 8)) (addR32Imm32Effect 0x1025e6 6 6 0x5a827999)) (rolR32Effect
    0x1025ec 3 7 30)) (movR32R32Effect 0x1025ef 3 8 7)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem block004 [Bindings] (boundary : ReturnBoundary) (stack input : BitVec 64)
    (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes004.length →
      0x1025c7 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x1025c7 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut004 stack input H M))
      (codeRange 0x1025c7 bytes004) effect004 := by
  have hRaw : AdvancesBlock boundary (fun s ↦ s.RIP = 0x1025c7 ∧ True)
      (codeRange 0x1025c7 bytes004) effect004 := by
    unfold bytes004 at hout ⊢
    sha1_run_begin (mov_r32_r32_rex_effect_step 0x1025c7 0x44 0xd9
      (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
    sha1_run_then (rol_r32_imm8_effect_step 0x1025ca 0xc1 0x1e (by decide +kernel)
      (by decide +kernel))
    sha1_run_then (mov_r32_r32_effect_step 0x1025cd 0xce (by decide +kernel))
    sha1_run_then (xor_r32_r32_effect_step 0x1025cf 0xd6 (by decide +kernel))
    sha1_run_then (and_r32_r32_effect_step 0x1025d1 0xfe (by decide +kernel))
    sha1_run_then (xor_r32_r32_effect_step 0x1025d3 0xd6 (by decide +kernel))
    sha1_run_then (mov_r64_r64_effect_step 0x1025d5 0x49 0xec (by unfold RexWPrefix; decide +kernel)
      (by decide +kernel))
    sha1_run_then (add_r32_r32_effect_step 0x1025d8 0xde (by decide +kernel))
    sha1_run_then (add_r32_r32_effect_step 0x1025da 0xee (by decide +kernel))
    sha1_run_then (mov_r32_r32_rex_effect_step 0x1025dc 0x41 0xc0
      (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
    sha1_run_then (rol_r32_imm8_rex_effect_step 0x1025df 0x41 0xc0 0x5
      (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
    sha1_run_then (add_r32_r32_rex_effect_step 0x1025e3 0x44 0xc6
      (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
    sha1_run_then (add_r32_imm32_effect_step 0x1025e6 0xc6 0x5a827999 (by decide +kernel)
      (by decide +kernel))
    sha1_run_then (rol_r32_imm8_effect_step 0x1025ec 0xc7 0x1e (by decide +kernel)
      (by decide +kernel))
    sha1_run_then (mov_r32_r32_rex_effect_step 0x1025ef 0x41 0xf8
      (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
    sha1_run_finish [effect004]
  intro s hr hc hp
  exact hRaw s hr hc ⟨hp.1, True.intro⟩

private def genericCut004 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), (A 2)⟩,
    ⟨(.reg 2 : Operand 32), (H[1]).rotateLeft 30⟩,
    ⟨(.reg 3 : Operand 32), H[2]⟩,
    ⟨(.reg 5 : Operand 32), W 2⟩,
    ⟨(.reg 7 : Operand 32), (A 1)⟩,
    ⟨(.reg 9 : Operand 32), W 3⟩,
    ⟨(.reg 11 : Operand 32), H[0]⟩,
    ⟨(.reg 14 : Operand 32), W 4⟩,
    ⟨(.reg 15 : Operand 32), W 0⟩,
    ⟨(.mem (stack + 8) : Operand 32), W 4⟩,
    ⟨(.mem (stack + 56) : Operand 32), W 3⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 88) : Operand 32), W 1⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

private def genericCut005 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), (A 2)⟩,
    ⟨(.reg 1 : Operand 32), (H[0]).rotateLeft 30⟩,
    ⟨(.reg 2 : Operand 32), (H[1]).rotateLeft 30⟩,
    ⟨(.reg 6 : Operand 32), (A 3)⟩,
    ⟨(.reg 7 : Operand 32), ((A 1)).rotateLeft 30⟩,
    ⟨(.reg 8 : Operand 32), ((A 1)).rotateLeft 30⟩,
    ⟨(.reg 9 : Operand 32), (W 3)⟩,
    ⟨(.reg 12 : Operand 32), (W 2)⟩,
    ⟨(.reg 14 : Operand 32), (W 4)⟩,
    ⟨(.reg 15 : Operand 32), (W 0)⟩,
    ⟨(.mem (stack + 8) : Operand 32), (W 4)⟩,
    ⟨(.mem (stack + 56) : Operand 32), (W 3)⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 88) : Operand 32), (W 1)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

theorem effect004_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (_hf : FrameData stack input M s)
    (he : (effect004 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hfoot : ∀ c ∈ (effect004 s).components, c ∈ [.reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6,
    .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] :=
    by
    unfold effect004
    iterate 14 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [addR32Imm32Effect_components, addR32R32Effect_components, andR32R32Effect_components,
        movR32R32Effect_components, movR64R64Effect_components, rolR32Effect_components,
        xorR32R32Effect_components, List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and,
        forall_eq]
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose]
  have ha := he.agrees.mono hfoot
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl
    all_goals simp_all (config := {decide := true, implicitDefEqProofs := false}) only
      [scratchComponents, x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl
    all_goals first
      | exact hCov.elim

theorem effect004_rip {s t : RamState}
    (he : (effect004 s).Holds s t) :
    t.RIP = 0x1025f2 := by
  exact he.rip.trans (by rfl)

section Words004
set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem genericWords004 {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32)
    {s t : RamState}
    (hWork : A 3 = (A 2).rotateLeft 5 +
      Standards.NIST.SHA2.SHA256.Ch (A 1) (H[0].rotateLeft 30) (H[1].rotateLeft 30) +
      0x5a827999 + W 2 + H[2])
    (hw : Write.AllHold s (genericCut004 stack input H A W))
    (he : (effect004 s).Holds s t) :
    Write.AllHold t (genericCut005 stack input H A W) := by
  have hfull : ∀ wr ∈ (effect004 s).writes, wr.Full := by
    apply Effect.Local.full
    unfold effect004
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  simp only [genericCut004, Write.AllHold] at hw
  obtain ⟨h0,h2,h3,h5,h7,h9,h11,h14,h15,
    hM8,hM56,hM64,hM88,hM116,hM120,hM124,hM144,hM152⟩ := hw
  sha1_norm at h0 h2 h3 h5 h7 h9 h11 h14 h15
  sha1_norm at hM8 hM56 hM64 hM88 hM116 hM120 hM124 hM144 hM152
  simp only [genericCut005, Write.AllHold, ← ho.read_reg, ← ho.read_mem]
  simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose, effect004, h0,
    h2, h3, h5, h7, h9, h11, h14,
    h15, hM8, hM56, hM64, hM88, hM116, hM120, hM124, hM144, hM152]
  rw [hWork]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [sha1Ch_eq, BitVec.xor_comm, BitVec.and_comm,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
  generalize hR : (A 2).rotateLeft 5 = r at ⊢
  generalize hC : H[1].rotateLeft 30 ^^^
      (A 1 &&& (H[0].rotateLeft 30 ^^^ H[1].rotateLeft 30)) = c at ⊢
  generalize hE : H[2] = e at ⊢
  generalize hW : W 2 = w at ⊢
  generalize hK : (0x5a827999 : BitVec 32) = k at ⊢
  ac_rfl

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
theorem effect004_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16}
    {s t : RamState}
    (_hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut004 stack input H M))
    (he : (effect004 s).Holds s t) :
    Write.AllHold t (cut005 stack input H M) := by
  have hWork : (workingAfter M H 3).a =
      (workingAfter M H 2).a.rotateLeft 5 +
        Standards.NIST.SHA2.SHA256.Ch (workingAfter M H 1).a
          (H[0].rotateLeft 30) (H[1].rotateLeft 30) +
        0x5a827999 + scheduleWord M 2 + H[2] := by
    rw [workingAfter_step M H 2 (by decide +kernel)]
    rw [sha1_step_a_choice ⟨2, by decide⟩ (messageSchedule M)[2]
      (workingAfter M H 2) (by decide)]
    have hSched : (messageSchedule M)[2] = scheduleWord M ⟨2, by decide⟩ := by
      unfold scheduleWord
      rfl
    rw [hSched]
    rw [workingAfter_step_b M H 1 (by decide +kernel),
      workingAfter_step_c M H 1 (by decide +kernel),
      workingAfter_step_b M H 0 (by decide +kernel),
      workingAfter_step_d M H 1 (by decide +kernel),
      workingAfter_step_c M H 0 (by decide +kernel),
      workingAfter_step_e M H 1 (by decide +kernel),
      workingAfter_step_d M H 0 (by decide +kernel),
      workingAfter_zero]
    simp only [WorkingVariables.ofHashValue]
    simp only [sha1Rotl_eq_rotateLeft 5 _ (by decide),
      sha1Rotl_eq_rotateLeft 30 _ (by decide)]
    simp [Standards.NIST.SHA1.K]
  exact genericWords004 (fun n ↦ (workingAfter M H n).a) (scheduleWord M) hWork hw he

end Words004

theorem segment004 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x1025c7 0x1025f2
      cut004 cut005 := by
  have hout : ∀ d : Nat, d ≤ bytes004.length →
      0x1025c7 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      simp only [bytes004, List.length_cons, List.length_nil] at hd <;>
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  apply Segment.of_block (fun _ _ _ _ => effect004)
    (fun stack input H M => block004 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64
      0x25c7) bytes004,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect004_rip he
  · intro stack input H M s t _ hf _ he
    exact effect004_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect004_words hf hw he

end Sha1.Proofs.Compress.Machine
