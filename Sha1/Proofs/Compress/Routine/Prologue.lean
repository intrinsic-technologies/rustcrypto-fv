import Sha1.Proofs.Compress.Routine.Interface
import Sha1.Proofs.Compress.Routine.Frame
import Sha1.Proofs.Compress.Machine.Segment
import Sha1.Proofs.Common.Instructions.MovStore.Stack
import X86Proofs.Instructions.Sub.Generated.Imm32.Triple
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple
import X86Proofs.Program.Entry
import Sha1.Proofs.Common.Instructions.MovStore.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Mov.Generated.RM.Triple
import X86Proofs.Instructions.NopMem.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Shl.Generated.R.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple

namespace Sha1.Proofs.Compress.Routine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Proofs.Refine
open Sha1.Spec Sha1.Spec.Program Standards.NIST
open Sha1.Proofs.Compress.Machine

attribute [local x86_compose] pushAddr_eq_read BitVec.sub_eq_add_neg nopMemLen

private def saveBytes : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53,
   0x48, 0x81, 0xec, 0xa0, 0, 0, 0]

private def saveEffect : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (pushR64Effect 0x1024e9 1 5) (pushR64Effect 0x1024ea 2 15))
    (pushR64Effect 0x1024ec 2 14)) (pushR64Effect 0x1024ee 2 13))
    (pushR64Effect 0x1024f0 2 12)) (pushR64Effect 0x1024f2 1 3))
    (subR64Imm32Effect 0x1024f3 4 160)

private theorem rangeApart_slice_left {a p : BitVec 64} {len total offset count : Nat}
    (h : RangeApart a len p total) (hb : offset + count ≤ len) :
    RangeApart (a + BitVec.ofNat 64 offset) count p total := by
  intro i hi j hj he
  apply h (offset + i) (by omega) j hj
  simpa only [BitVec.ofNat_add, BitVec.add_assoc] using he

private def SavePre (stack : BitVec 64) (s : RamState) : Prop :=
  s.RIP = 0x1024e9 ∧ (Operand.reg 4 : Operand 64).read s = stack + 208 ∧
    Machine.MemWritable s stack 216 ∧ RangeApart stack 208 0x1024e9 17

macro "save_slot " hP:ident " [" off:term "," coff:term "," clen:term "]" : tactic => `(tactic| (
  have hs := ($hP).2.1
  have hw := ($hP).2.2.1
  have ha := ($hP).2.2.2
  sha1_norm at hs
  sha1_norm [pushAddr_eq_read, hs]
  first
  | exact memoryWritable_slice hw $off 8 (by decide +kernel)
  | exact rangeApart_slice_left (offset := $off) (count := 8) ha (by decide +kernel)
  | (have hc := RangeApart.sub
        (rangeApart_slice_left (offset := $off) (count := 8) ha
          (by decide +kernel)) $coff $clen (by decide +kernel)
     sha1_norm at hc
     exact hc)))

macro "save_mid" "[" off:term "," coff:term "," clen:term "]" : tactic => `(tactic| (
  intro s s' hP hH hO
  refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_⟩
  · first
    | exact hH.rip_of (by sha1_norm)
    | (refine storePre_of_holds hH (hO true) (by sha1_norm)
        (by x86_addr_obs) ?_ ?_ <;> save_slot hP [$off, $coff, $clen])
  · first
    | (solve | apply Effect.Avoids.of_noMem; simp [Component.Covers])
    | (apply Effect.avoids_codeRange
       sha1_norm
       try simp only [x86_pre_simp]
       save_slot hP [$off, $coff, $clen])))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 300000 in
private theorem save_advances [Bindings] (boundary : ReturnBoundary) (stack : BitVec 64)
    (hne : ∀ i < 18, (0x1024e9 : BitVec 64) + BitVec.ofNat 64 i ≠ boundary.rip) :
    AdvancesBlock boundary (SavePre stack) (codeRange 0x1024e9 saveBytes) saveEffect := by
  sha1_run_begin_manual (Sha1.Proofs.Common.Instructions.MovStore.push_r64_effect_step
    0x1024e9 0x55 (by decide))
  case pre =>
    intro s hP
    refine ⟨hP.1, ?_, ?_⟩ <;> save_slot hP [200, 0, 1]
  case av =>
    intro s hP
    apply Effect.avoids_codeRange
    sha1_norm
    try simp only [x86_pre_simp]
    save_slot hP [200, 0, 17]
  sha1_run_then_manual (Sha1.Proofs.Common.Instructions.MovStore.push_r64_rex_effect_step
    0x1024ea 0x41 0x57 (by unfold RexPrefix; decide) (by decide))
  case mid => save_mid [192, 1, 2]
  sha1_run_then_manual (Sha1.Proofs.Common.Instructions.MovStore.push_r64_rex_effect_step
    0x1024ec 0x41 0x56 (by unfold RexPrefix; decide) (by decide))
  case mid => save_mid [184, 3, 2]
  sha1_run_then_manual (Sha1.Proofs.Common.Instructions.MovStore.push_r64_rex_effect_step
    0x1024ee 0x41 0x55 (by unfold RexPrefix; decide) (by decide))
  case mid => save_mid [176, 5, 2]
  sha1_run_then_manual (Sha1.Proofs.Common.Instructions.MovStore.push_r64_rex_effect_step
    0x1024f0 0x41 0x54 (by unfold RexPrefix; decide) (by decide))
  case mid => save_mid [168, 7, 2]
  sha1_run_then_manual (Sha1.Proofs.Common.Instructions.MovStore.push_r64_effect_step
    0x1024f2 0x53 (by decide))
  case mid => save_mid [160, 9, 1]
  sha1_run_then_manual (sub_r64_imm32_effect_step 0x1024f3 0x48 0xec 160
    (by unfold RexWPrefix; decide) (by decide) (by decide))
  case mid => save_mid [160, 10, 7]
  sha1_run_finish [saveEffect]

private def setupBytes : List UInt8 :=
  [0x48, 0x89, 0xd0, 0x48, 0xc1, 0xe0, 0x06, 0x48, 0x01, 0xf0,
   0x48, 0x89, 0x84, 0x24, 0x88, 0, 0, 0]

private def setupEffect : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (movR64R64Effect 0x1024fa 0 2)
    (shlR64Effect 0x1024fd 4 0 6)) (addR64R64Effect 0x102501 0 6))
    (movM64R64Effect 0x102504 0 (.sib 4 none 0 (.d32 136)))

private def SetupPre (stack : BitVec 64) (s : RamState) : Prop :=
  s.RIP = 0x1024fa ∧ (Operand.reg 4 : Operand 64).read s = stack ∧
    Machine.MemWritable s stack 216 ∧ RangeApart stack 208 0x1024fa 18

set_option maxRecDepth 4096 in
set_option maxHeartbeats 300000 in
private theorem setup_advances [Bindings] (boundary : ReturnBoundary) (stack : BitVec 64)
    (hne : ∀ i < 19, (0x1024fa : BitVec 64) + BitVec.ofNat 64 i ≠ boundary.rip) :
    AdvancesBlock boundary (SetupPre stack) (codeRange 0x1024fa setupBytes) setupEffect := by
  sha1_run_begin (mov_r64_r64_effect_step 0x1024fa 0x48 0xd0
    (by unfold RexWPrefix; decide) (by decide))
  sha1_run_then (shl_r64_imm8_effect_step 0x1024fd 0x48 0xe0 6
    (by unfold RexWPrefix; decide) (by decide) (by decide))
  sha1_run_then (add_r64_r64_effect_step 0x102501 0x48 0xf0
    (by unfold RexWPrefix; decide) (by decide))
  sha1_run_then_manual (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step
    0x102504 0x48 (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d32 136))
      (by decide) (by decide) (by decide))
  case mid => save_mid [136, 10, 8]
  sha1_run_finish [setupEffect]

private def loadInitialBytes : List UInt8 :=
  [0x44, 0x8b, 0x1f, 0x44, 0x8b, 0x47, 4, 0x8b, 0x57, 8,
   0x44, 0x8b, 0x57, 12, 0x48, 0x89, 0xbc, 0x24, 0x80, 0, 0, 0,
   0x8b, 0x47, 16, 0x66, 0x66, 0x2e, 0x0f, 0x1f, 0x84, 0, 0, 0, 0, 0]

private def loadInitialEffect : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (movR32M32Effect 0x10250c 11 (.base 7 .none))
    (movR32M32Effect 0x10250f 8 (.base 7 (.d8 4))))
    (movR32M32LowEffect 0x102513 2 (.base 7 (.d8 8))))
    (movR32M32Effect 0x102516 10 (.base 7 (.d8 12))))
    (movM64R64Effect 0x10251a 7 (.sib 4 none 0 (.d32 128))))
    (movR32M32LowEffect 0x102522 0 (.base 7 (.d8 16))))
    (fun _ ↦ nopEffect 0x102525 11)

private def LoadInitialPre (stack out : BitVec 64) (s : RamState) : Prop :=
  (s.RIP = 0x10250c ∧ (Operand.reg 4 : Operand 64).read s = stack ∧
    Machine.MemWritable s stack 216 ∧ RangeApart stack 208 0x10250c 36) ∧
    (Operand.reg 7 : Operand 64).read s = out ∧ MemReadable s out 20

macro "load_initial_mid " off:term : tactic => `(tactic| (
  intro s s' hP hH hO
  refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_⟩
  · have hOut := hP.2.1
    sha1_norm at hOut
    refine LoadPre.of_holds hH (hO true) (by sha1_norm) (by x86_addr_obs) ?_
    sha1_norm [hOut]
    have hr := hP.2.2
    first
    | with_reducible_and_instances
        (exact memReadable_slice hr $off 4 (by decide +kernel))
    | with_reducible_and_instances
        (simpa only [BitVec.add_zero] using memReadable_slice hr $off 4 (by decide +kernel))
  · apply Effect.Avoids.of_noMem
    simp [Component.Covers]))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 300000 in
private theorem loadInitial_advances [Bindings] (boundary : ReturnBoundary) (stack out : BitVec 64)
    (hne : ∀ i < 37, (0x10250c : BitVec 64) + BitVec.ofNat 64 i ≠ boundary.rip) :
    AdvancesBlock boundary (LoadInitialPre stack out) (codeRange 0x10250c loadInitialBytes)
      loadInitialEffect := by
  sha1_run_begin_manual (mov_r32_m32_effect_step 0x10250c 0x44
    (by unfold RexNoWPrefix; decide) 3 (.base 7 .none) (by decide) (by decide) (by decide))
  case pre =>
    intro s hP
    refine ⟨hP.1.1, ?_⟩
    have hOut := hP.2.1
    sha1_norm at hOut
    sha1_norm [hOut]
    simpa only [BitVec.add_zero] using memReadable_slice hP.2.2 0 4 (by decide)
  case av =>
    intro s hP
    apply Effect.Avoids.of_noMem
    simp [Component.Covers]
  sha1_run_then_manual (mov_r32_m32_effect_step 0x10250f 0x44
    (by unfold RexNoWPrefix; decide) 0 (.base 7 (.d8 4))
    (by decide) (by decide) (by decide))
  case mid => load_initial_mid 4
  sha1_run_then_manual (mov_r32_m32_low_effect_step 0x102513 2 (.base 7 (.d8 8))
    (by decide) (by decide) (by decide))
  case mid => load_initial_mid 8
  sha1_run_then_manual (mov_r32_m32_effect_step 0x102516 0x44
    (by unfold RexNoWPrefix; decide) 2 (.base 7 (.d8 12))
    (by decide) (by decide) (by decide))
  case mid => load_initial_mid 12
  sha1_run_then_manual (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step
    0x10251a 0x48 (by unfold RexWPrefix; decide) 7 (.sib 4 none 0 (.d32 128))
      (by decide) (by decide) (by decide))
  case mid =>
    intro s s' hP hH hO
    have hCore := hP.1
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_⟩
    · refine storePre_of_holds hH (hO true) (by sha1_norm) (by x86_addr_obs) ?_ ?_ <;>
        save_slot hCore [128, 14, 8]
    · apply Effect.avoids_codeRange
      sha1_norm
      try simp only [x86_pre_simp]
      save_slot hCore [128, 14, 8]
  sha1_run_then_manual (mov_r32_m32_low_effect_step 0x102522 0 (.base 7 (.d8 16))
    (by decide) (by decide) (by decide))
  case mid => load_initial_mid 16
  sha1_run_then_manual (show StepEffect (fun s ↦ s.RIP = (0x102525 : BitVec 64))
      (codeRange 0x102525 [0x66, 0x66, 0x2e, 0x0f, 0x1f, 0x84, 0, 0, 0, 0, 0])
      (fun _ ↦ nopEffect 0x102525 11) from
    nop_m_effect_step 0x102525 [0x66, 0x66, 0x2e] (by decide) (by decide)
      (.sib 0 (some 0) 0 (.d32 0)) (by decide) (by decide) (by decide))
  case mid =>
    intro s s' hP hH hO
    refine ⟨hH.rip_of (by sha1_norm), ?_⟩
    apply Effect.Avoids.of_noMem
    simp [Component.Covers]

  sha1_run_finish [loadInitialEffect]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 300000 in
private theorem saveEffect_writes (stack : BitVec 64) (s : RamState)
    (hs : (Operand.reg 4 : Operand 64).read s = stack + 208) :
    (saveEffect s).writes =
      [⟨(.mem (stack + 200) : Operand 64), (Operand.reg 5 : Operand 64).read s⟩,
       ⟨(.mem (stack + 192) : Operand 64), (Operand.reg 15 : Operand 64).read s⟩,
       ⟨(.mem (stack + 184) : Operand 64), (Operand.reg 14 : Operand 64).read s⟩,
       ⟨(.mem (stack + 176) : Operand 64), (Operand.reg 13 : Operand 64).read s⟩,
       ⟨(.mem (stack + 168) : Operand 64), (Operand.reg 12 : Operand 64).read s⟩,
       ⟨(.mem (stack + 160) : Operand 64), (Operand.reg 3 : Operand 64).read s⟩,
       ⟨(.reg 4 : Operand 64), stack⟩] := by
  sha1_norm at hs
  sha1_norm [saveEffect, hs]
  simp only [BitVec.add_zero]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 300000 in
private theorem loadInitialEffect_writes (stack out : BitVec 64) (s : RamState)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hout : (Operand.reg 7 : Operand 64).read s = out) :
    (loadInitialEffect s).writes =
      [⟨(.reg 11 : Operand 64), (memLoad s.external out 32).setWidth 64⟩,
       ⟨(.reg 8 : Operand 64), (memLoad s.external (out + 4) 32).setWidth 64⟩,
       ⟨(.reg 2 : Operand 64), (memLoad s.external (out + 8) 32).setWidth 64⟩,
       ⟨(.reg 10 : Operand 64), (memLoad s.external (out + 12) 32).setWidth 64⟩,
       ⟨(.mem (stack + 128) : Operand 64), out⟩,
       ⟨(.reg 0 : Operand 64),
         (memLoad (memStore s.external (stack + 128) out) (out + 16) 32).setWidth 64⟩] := by
  sha1_norm at hs hout
  sha1_norm [loadInitialEffect, hs, hout]
  simp only [BitVec.add_zero, Operand.write]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 300000 in
private theorem save_words {stack : BitVec 64} {s t : RamState}
    (hs : (Operand.reg 4 : Operand 64).read s = stack + 208)
    (he : (saveEffect s).Holds s t) :
    (Operand.reg 4 : Operand 64).read t = stack ∧
    ∀ i : Fin 6,
      memLoad t.external (stack + BitVec.ofNat 64 (160 + 8 * i.val)) 64 =
        (Operand.reg (#[3, 12, 13, 14, 15, 5][i.val]) : Operand 64).read s := by
  have hwEq := saveEffect_writes stack s hs
  generalize heq : saveEffect s = e at he
  have hw := he.writes
  rw [← heq, hwEq] at hw
  simp only [Write.AllHold] at hw
  refine ⟨hw.2.2.2.2.2.2, ?_⟩
  intro ⟨i, hi⟩
  have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hw.2.2.2.2.2.1
  · exact hw.2.2.2.2.1
  · exact hw.2.2.2.1
  · exact hw.2.2.1
  · exact hw.2.1
  · exact hw.1

set_option maxRecDepth 4096 in
set_option maxHeartbeats 300000 in
private theorem setup_words {stack : BitVec 64} {s t : RamState}
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (he : (setupEffect s).Holds s t) :
    memLoad t.external (stack + 136) 64 =
      ((Operand.reg 2 : Operand 64).read s <<< 6) + (Operand.reg 6 : Operand 64).read s := by
  have hw := he.writes
  sha1_norm at hs
  sha1_norm [setupEffect, hs] at hw
  exact hw.2

private theorem memLoad_of_agrees {cs : List Component} {s t : RamState}
    {a : BitVec 64} {n : Nat} (ha : AgreesExcept cs s t)
    (h : ∀ i < n / 8, ∀ c ∈ cs, ¬ c.Covers (a + BitVec.ofNat 64 i)) :
    memLoad t.external a n = memLoad s.external a n := by
  apply memLoad_congr
  intro i hi
  change (t.external[a + BitVec.ofNat 64 i]?).getD 0 =
    (s.external[a + BitVec.ofNat 64 i]?).getD 0
  rw [ha.byte (h i hi)]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 300000 in
set_option backward.isDefEq.respectTransparency false in
private theorem loadInitial_words {stack out : BitVec 64} {H : Vector (BitVec 32) 5}
    {s t : RamState} (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hout : (Operand.reg 7 : Operand 64).read s = out)
    (hap : RangeApart (stack + 128) 8 (out + 16) 4)
    (hw : ∀ i : Fin 5, memLoad s.external (out + BitVec.ofNat 64 (4 * i.val)) 32 = H[i])
    (he : (loadInitialEffect s).Holds s t) :
    Machine.LoopRegisters H t ∧ memLoad t.external (stack + 128) 64 = out := by
  have hwEq := loadInitialEffect_writes stack out s hs hout
  generalize heq : loadInitialEffect s = e at he
  have hew := he.writes
  rw [← heq, hwEq] at hew
  simp only [Write.AllHold] at hew
  have hl : memLoad (memStore s.external (stack + 128) out) (out + 16) 32 = H[4] :=
    (memLoad_memStore_of_rangeApart _ _ _ _ _ hap).trans (hw 4)
  have h11 := congrArg (fun v : BitVec 64 ↦ v.setWidth 32) hew.1
  have h8 := congrArg (fun v : BitVec 64 ↦ v.setWidth 32) hew.2.1
  have h2 := congrArg (fun v : BitVec 64 ↦ v.setWidth 32) hew.2.2.1
  have h10 := congrArg (fun v : BitVec 64 ↦ v.setWidth 32) hew.2.2.2.1
  have h0 := congrArg (fun v : BitVec 64 ↦ v.setWidth 32) hew.2.2.2.2.2
  simp only [Operand.setWidth_read_reg64,
    BitVec.setWidth_setWidth_of_le (w := 32) (k := 32) (l := 64) _ (by decide),
    BitVec.setWidth_eq] at h11 h8 h2 h10 h0
  refine ⟨⟨h11.trans ?_, h8.trans ?_, h2.trans ?_, h10.trans ?_, h0.trans hl⟩,
    hew.2.2.2.2.1⟩
  · have hzero := hw (⟨0, by decide⟩ : Fin 5)
    sha1_norm [Fin.getElem_fin] at hzero ⊢
    simpa only [BitVec.add_zero] using hzero
  · exact hw 1
  · exact hw 2
  · exact hw 3


private def changes (base : BitVec 64) (len : Nat) : List Component :=
  [.mem base len, .reg 0, .reg 2, .reg 4, .reg 8, .reg 10, .reg 11, .flags, .rip]

private theorem covers_subrange {base x : BitVec 64} {offset len total : Nat}
    (h : (Component.mem (base + BitVec.ofNat 64 offset) len).Covers x)
    (hb : offset + len ≤ total) : (Component.mem base total).Covers x := by
  obtain ⟨i, hi, he⟩ := h
  refine ⟨offset + i, by omega, ?_⟩
  simpa only [BitVec.ofNat_add, BitVec.add_assoc] using he

private theorem changes_memLoad {base addr : BitVec 64} {len n : Nat} {s t : RamState}
    (ha : AgreesExcept (changes base len) s t) (hap : RangeApart base len addr (n / 8)) :
    memLoad t.external addr n = memLoad s.external addr n := by
  apply memLoad_of_agrees ha
  intro i hi comp hc hcov
  simp only [changes, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcov.elim
  obtain ⟨j, hj, he⟩ := hcov
  exact hap j hj i hi he.symm

set_option maxRecDepth 4096 in
set_option maxHeartbeats 300000 in
private theorem save_agrees {stack : BitVec 64} {s t : RamState}
    (hs : (Operand.reg 4 : Operand 64).read s = stack + 208)
    (he : (saveEffect s).Holds s t) : AgreesExcept (changes stack 208) s t := by
  have ha := he.agrees
  sha1_norm at hs
  have hc : (saveEffect s).components =
      [.mem (stack + 200) 8, .mem (stack + 192) 8, .mem (stack + 184) 8,
       .mem (stack + 176) 8, .mem (stack + 168) 8, .mem (stack + 160) 8,
       .reg 4, .flags, .rip] := by sha1_norm [saveEffect, hs]
  rw [hc] at ha
  apply ha.widen
  · intro comp hm hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [Component.isMem, changes]
  · intro x comp hm hcov
    refine ⟨.mem stack 208, by simp [changes], ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcov.elim
    all_goals exact covers_subrange hcov (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 300000 in
private theorem setup_agrees {stack : BitVec 64} {s t : RamState}
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (he : (setupEffect s).Holds s t) : AgreesExcept (changes (stack + 136) 8) s t := by
  have ha := he.agrees
  sha1_norm at hs
  have hc : (setupEffect s).components = [.reg 0, .mem (stack + 136) 8, .flags, .rip] := by
    sha1_norm [setupEffect, hs]
  rw [hc] at ha
  exact ha.mono (by
    intro comp hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl <;> simp [changes])

set_option maxRecDepth 4096 in
set_option maxHeartbeats 300000 in
private theorem loadInitial_agrees {stack : BitVec 64} {s t : RamState}
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (he : (loadInitialEffect s).Holds s t) :
    AgreesExcept (changes (stack + 128) 8) s t := by
  have ha := he.agrees
  sha1_norm at hs
  have hc : (loadInitialEffect s).components =
      [.reg 11, .reg 8, .reg 2, .reg 10, .mem (stack + 128) 8, .reg 0, .rip] := by
    sha1_norm [loadInitialEffect, hs]
  rw [hc] at ha
  exact ha.mono (by
    intro c hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [changes])

private theorem changes_widen {base : BitVec 64} {offset len total : Nat} {s t : RamState}
    (ha : AgreesExcept (changes (base + BitVec.ofNat 64 offset) len) s t)
    (hb : offset + len ≤ total) : AgreesExcept (changes base total) s t := by
  apply ha.widen
  · intro comp hm hn
    simp only [changes, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [Component.isMem, changes]
  · intro x comp hm hcov
    refine ⟨.mem base total, by simp [changes], ?_⟩
    simp only [changes, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcov.elim
    exact covers_subrange hcov hb

private theorem changes_trans {base : BitVec 64} {len : Nat} {s t u : RamState}
    (ha : AgreesExcept (changes base len) s t) (hb : AgreesExcept (changes base len) t u) :
    AgreesExcept (changes base len) s u :=
  (ha.trans hb).mono (by intro c hc; exact (List.mem_append.mp hc).elim id id)

private theorem stack_code_apart {c : Context} {bindings : Bindings} (hv : c.Valid bindings)
    {p : BitVec 64} {len : Nat} (hp : ∀ i < len, InProgram (p + BitVec.ofNat 64 i)) :
    RangeApart c.stack 208 p len := by
  have hin : InRegion c.stackRegion c.stack 208 := by
    simpa only [BitVec.reduceOfNat, BitVec.add_zero] using
      hv.stack_inRegion (off := 0) (len := 208) (by decide)
  intro i hi j hj he
  exact hv.outputContract.stack.avoids _ (Common.StoreRegion.contains_byte hin hi)
    (.inl (he.symm ▸ hp j hj))

private theorem changes_code {c : Context} {bindings : Bindings} (hv : c.Valid bindings)
    {s t : RamState} (ha : AgreesExcept (changes c.stack 208) s t)
    (hc : CodeIn Extracted.programImage s) : CodeIn Extracted.programImage t := by
  have hin : InRegion c.stackRegion c.stack 208 := by
    simpa only [BitVec.reduceOfNat, BitVec.add_zero] using
      hv.stack_inRegion (off := 0) (len := 208) (by decide)
  apply CodeIn.of_agreesExcept ha _ hc
  intro x hx comp hm hcov
  simp only [changes, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcov.elim
  obtain ⟨i, hi, he⟩ := hcov
  exact hv.outputContract.stack.avoids _ (Common.StoreRegion.contains_byte hin hi)
    (.inl (he ▸ ⟨x.2, hx⟩))

private theorem stack_output_apart {c : Context} {bindings : Bindings} (hv : c.Valid bindings) :
    RangeApart c.stack 208 (c.initial.regValue .rdi) 20 := by
  have hin : InRegion c.stackRegion c.stack 208 := by
    simpa only [BitVec.reduceOfNat, BitVec.add_zero] using
      hv.stack_inRegion (off := 0) (len := 208) (by decide)
  have hb : (c.initial.regValue .rdi).toNat + 20 < 2 ^ 32 :=
    hv.call.outputInMemory.2.1
  have hout : InRegion (Compress.outputRegion c.initial) (c.initial.regValue .rdi) 20 :=
    ⟨Nat.le_refl _, Nat.le_refl _, by omega⟩
  intro i hi j hj he
  exact hv.call.separation.1 _ (Common.StoreRegion.contains_byte hout hj)
    (he ▸ Common.StoreRegion.contains_byte hin hi)


theorem enter_nonempty (bindings : Bindings) (boundary : ReturnBoundary)
    (hBoundary : Machine.OutsideCompression boundary.rip)
    (c : Context) (h : c.Valid bindings)
    (hcount : 0 < c.count) :
    ∃ n s, @Advances bindings boundary n c.initial s ∧
      @ReadyToStep bindings s ∧ CodeIn Extracted.programImage s ∧ s.RIP = 0x1024e9 ∧
      AgreesExcept [.flags, .rip] c.initial s := by
  letI := bindings
  have entryReady : ReadyToStep c.initial := h.ready
  have entryCode : CodeIn Extracted.programImage c.initial := h.code
  have hne (pc : BitVec 64) (hl : 0x1024e0 ≤ pc.toNat) (hh : pc.toNat < 0x1036df) :
      pc ≠ boundary.rip := outsideCompression_ne hBoundary hl hh
  have ht : ∃ n s, Advances boundary n c.initial s ∧
      ReadyToStep s ∧ CodeIn Extracted.programImage s ∧ s.RIP = 0x1024e0 ∧
      AgreesExcept [.flags, .rip] c.initial s := by
    rcases h.entry with he | he
    · have hc : CodeIn (codeRange 0x100000 (0xe9 :: immBytes 32 (0x24db : BitVec 32)))
          c.initial := program_text_slice entryCode 0 5 (by decide +kernel)
      obtain ⟨s, ha, hr, hf⟩ :=
        (jmp_rel32_effect_step 0x100000 0x24db (by decide +kernel)).advances
          entryReady hc he (hne _ (by decide) (by decide))
      have hag : AgreesExcept [.flags, .rip] c.initial s :=
        hf.agrees.mono (by simp [jmpEffect_components])
      exact ⟨1, s, ha, hr,
        CodeIn.of_external_eq (hag.external (by simp [Component.Covers])) entryCode,
        hf.rip, hag⟩
    · exact ⟨0, c.initial, (advances_zero _ _ _).2 rfl, entryReady, entryCode, he,
        AgreesExcept.refl _ _⟩
  obtain ⟨n, s, ha, hr, hc, hp, hag⟩ := ht
  have htest : CodeIn (codeRange 0x1024e0 [0x48, 0x85, 0xd2]) s :=
    program_text_slice hc 0x24e0 3 (by decide +kernel)
  obtain ⟨t, hb, hrt, he⟩ :=
    (test_r64_r64_effect_step 0x1024e0 0x48 0xd2
      (by unfold RexWPrefix; decide) (by decide)).advances hr htest hp
      (hne _ (by change 0x1024e0 ≤ 0x1024e3; decide)
        (by change 0x1024e3 < 0x1036df; decide))
  have hagt : AgreesExcept [.flags, .rip] c.initial t :=
    (hag.trans he.agrees).mono (by simp [testR64R64Effect_components])
  have hn : (Operand.reg 2 : Operand 64).read s ≠ 0 := by
    rw [hag.read (by decide)]
    intro hz
    have hh := h.call.blockCountArgumentMatchesBlocks
    change 64 * ((Operand.reg 2 : Operand 64).read c.initial).toNat = c.blocks.size at hh
    rw [hz] at hh
    have hs : c.blocks.size = 0 := by simpa using hh.symm
    simp only [Context.count, hs, Nat.zero_div, Nat.lt_irrefl] at hcount
  have hz : condHolds 4 (StatusFlags.ofRFLAGS t.RFLAGS) = false := by
    have hf := he.flags
    change (testFlags ((Operand.reg 2 : Operand 64).read s &&&
      (Operand.reg 2 : Operand 64).read s)).Allows (StatusFlags.ofRFLAGS t.RFLAGS) at hf
    have hzf := hf.2.2.2.1
    change (StatusFlags.ofRFLAGS t.RFLAGS).ZF = false
    change (StatusFlags.ofRFLAGS t.RFLAGS).ZF =
      (((Operand.reg 2 : Operand 64).read s &&& (Operand.reg 2 : Operand 64).read s) == 0) at hzf
    rw [BitVec.and_self] at hzf
    exact hzf.trans (beq_eq_false_iff_ne.mpr hn)
  have hct := CodeIn.of_external_eq (hagt.external (by simp [Component.Covers])) entryCode
  have hbranch : CodeIn (codeRange 0x1024e3
      (0x0f :: jccOpcode32 4 :: immBytes 32 (0x11f5 : BitVec 32))) t :=
    program_text_slice hct 0x24e3 6 (by decide +kernel)
  obtain ⟨u, hd, hru, heu⟩ := (jcc_rel32_effect_step 0x1024e3 4 0x11f5).advances
    hrt hbranch ⟨he.rip, fun _ ↦ by decide⟩ (by
      simp only [jccEffect, branchEffect, hz, Bool.false_eq_true, ↓reduceIte]
      exact hne _ (by decide) (by decide))
  have hf := jccEffect_not_taken hz heu
  have hagu : AgreesExcept [.flags, .rip] c.initial u :=
    (hagt.trans hf.agrees).mono (by simp [nopEffect_components])
  exact ⟨n + 1 + 1, u, (ha.trans hb).trans hd, hru,
    CodeIn.of_external_eq (hagu.external (by simp [Component.Covers])) entryCode,
    hf.rip, hagu⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 300000 in
set_option backward.isDefEq.respectTransparency false in
theorem prologueAdvanceCorrect : PrologueAdvanceCorrect := by
  intro bindings boundary c hv hBoundary hn
  letI := bindings
  obtain ⟨n0, s0, ha0, hr0, hc0, hp0, hag0⟩ := enter_nonempty bindings boundary hBoundary c hv hn
  have hcInit : CodeIn Extracted.programImage c.initial :=
    CodeIn.of_external_eq (hag0.external (by simp [Component.Covers])).symm hc0
  have hsp0 : (Operand.reg 4 : Operand 64).read s0 = c.stack + 208 := by
    rw [hag0.read (by decide)]
    change c.sp = c.sp - 208 + 208
    exact (BitVec.sub_add_cancel _ _).symm
  have hw0 : Machine.MemWritable s0 c.stack 216 :=
    hv.stack_writable.of_external_eq (hag0.external (by simp [Component.Covers]))
  have hne (base : BitVec 64) (len : Nat)
      (hl : 0x1024e0 ≤ base.toNat) (hh : base.toNat + len ≤ 0x1036df) :
      ∀ i < len, base + BitVec.ofNat 64 i ≠ (boundary).rip := by
    intro i hi
    apply outsideCompression_ne hBoundary
    all_goals
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      have hb := base.isLt
      omega
  have hap : RangeApart c.stack 208 0x1024e9 71 :=
    stack_code_apart hv (program_text_range 0x24e9 71 (by decide +kernel))
  have hsaveCode : CodeIn (codeRange 0x1024e9 saveBytes) s0 :=
    program_text_slice hc0 0x24e9 17 (by decide +kernel)
  obtain ⟨n1, s1, ha1, hr1, _, he1⟩ :=
    save_advances (boundary) c.stack
      (hne _ 18 (by decide) (by decide)) s0 hr0 hsaveCode
      ⟨hp0, hsp0, hw0, hap.sub0 17 (by decide)⟩
  obtain ⟨hsp1, hsaved⟩ := save_words hsp0 he1
  have hag1 := save_agrees hsp0 he1
  have hag01 : AgreesExcept (changes c.stack 208) c.initial s1 :=
    changes_trans (hag0.mono (by simp [changes])) hag1
  have hc1 := changes_code hv hag01 hcInit
  have hw1 := memWritable_of_holds he1 hw0
  have hap2 : RangeApart c.stack 208 0x1024fa 18 := by
    have ht := hap.sub 17 18 (by decide)
    sha1_norm at ht
    exact ht
  have hsetupCode : CodeIn (codeRange 0x1024fa setupBytes) s1 :=
    program_text_slice hc1 0x24fa 18 (by decide +kernel)
  have hp1 : s1.RIP = 0x1024fa := by
    have ht := he1.rip
    sha1_norm [saveEffect] at ht
    exact ht
  obtain ⟨n2, s2, ha2, hr2, _, he2⟩ :=
    setup_advances (boundary) c.stack
      (hne _ 19 (by decide) (by decide)) s1 hr1 hsetupCode
      ⟨hp1, hsp1, hw1, hap2⟩
  have hag2 := setup_agrees hsp1 he2
  have hag2' : AgreesExcept (changes c.stack 208) s1 s2 :=
    changes_widen (offset := 136) hag2 (by decide)
  have hag02 := changes_trans hag01 hag2'
  have hc2 := changes_code hv hag02 hcInit
  have hsp2 : (Operand.reg 4 : Operand 64).read s2 = c.stack :=
    (he2.agrees.read (by sha1_norm [setupEffect])).trans hsp1
  have hout2 : (Operand.reg 7 : Operand 64).read s2 = c.initial.regValue .rdi :=
    hag02.read (by simp [changes])
  have hw2 := memWritable_of_holds he2 hw1
  have houtReadable : MemReadable s2 (c.initial.regValue .rdi) 20 := by
    refine ⟨Nat.le_of_lt hv.call.outputInMemory.2.1, ?_⟩
    intro i hi
    apply hag02.grow
    exact Option.isSome_iff_exists.mpr
      (hv.outputContract.output.allocated _ (by
        change (c.initial.regValue .rdi).toNat ≤
          (c.initial.regValue .rdi + BitVec.ofNat 64 i).toNat ∧
          (c.initial.regValue .rdi + BitVec.ofNat 64 i).toNat <
            (c.initial.regValue .rdi).toNat + 20
        have hb : (c.initial.regValue .rdi).toNat + 20 < 2 ^ 32 :=
          hv.call.outputInMemory.2.1
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
        omega))
  have hwords2 : ∀ i : Fin 5,
      memLoad s2.external (c.initial.regValue .rdi + BitVec.ofNat 64 (4 * i.val)) 32 = c.H[i] := by
    intro i
    apply Eq.trans (changes_memLoad hag02
      ((stack_output_apart hv).sub (4 * i.val) 4 (by have := i.isLt; omega)))
    exact stateBytes_words hv.call.outputInMemory.2.2 i
  have hap3 : RangeApart c.stack 208 0x10250c 36 := by
    have ht := hap.sub 35 36 (by decide)
    sha1_norm at ht
    exact ht
  have hloadCode : CodeIn (codeRange 0x10250c loadInitialBytes) s2 :=
    program_text_slice hc2 0x250c 36 (by decide +kernel)
  have hp2 : s2.RIP = 0x10250c := by
    have ht := he2.rip
    sha1_norm [setupEffect] at ht
    exact ht
  obtain ⟨n3, s3, ha3, hr3, _, he3⟩ :=
    loadInitial_advances (boundary) c.stack (c.initial.regValue .rdi)
      (hne _ 37 (by decide) (by decide)) s2 hr2 hloadCode
      ⟨⟨hp2, hsp2, hw2, hap3⟩, hout2, houtReadable⟩
  have hag3 := loadInitial_agrees hsp2 he3
  have hag3' : AgreesExcept (changes c.stack 208) s2 s3 :=
    changes_widen (offset := 128) hag3 (by decide)
  have hag03 := changes_trans hag02 hag3'
  have hapOut : RangeApart (c.stack + 128) 8 (c.initial.regValue .rdi + 16) 4 :=
    (rangeApart_slice_left (offset := 128) (count := 8) (stack_output_apart hv)
      (by decide)).sub 16 4 (by decide)
  obtain ⟨hregs, hout⟩ := loadInitial_words hsp2 hout2 hapOut hwords2 he3
  have hsp3 : stackPtr s3 = c.stack :=
    (he3.agrees.read (by sha1_norm [loadInitialEffect])).trans hsp2
  have hslots12 : AgreesExcept (changes (c.stack + 128) 16) s1 s3 := by
    have h2 : AgreesExcept (changes ((c.stack + 128) + BitVec.ofNat 64 8) 8) s1 s2 := by
      have ht := hag2
      sha1_norm at ht ⊢
      exact ht
    have h3 : AgreesExcept (changes ((c.stack + 128) + BitVec.ofNat 64 0) 8) s2 s3 := by
      simpa only [BitVec.add_zero] using hag3
    exact changes_trans (changes_widen h2 (by decide)) (changes_widen h3 (by decide))
  have savedFinal : ∀ i : Fin 6,
      memLoad s3.external (c.stack + BitVec.ofNat 64 (160 + 8 * i.val)) 64 =
        (Operand.reg (#[3, 12, 13, 14, 15, 5][i.val]) : Operand 64).read c.initial := by
    intro i
    rw [changes_memLoad hslots12 (RangeApart.offsets c.stack (a := 128) (b := 160 + 8 * i.val)
      (by decide) (by have := i.isLt; omega) (.inl (by omega))), hsaved i]
    exact hag0.read (by decide +revert)
  have endFinal : memLoad s3.external (c.stack + 136) 64 = c.input c.count := by
    have ht := changes_memLoad (n := 64) hag3
      (RangeApart.offsets c.stack (a := 128) (b := 136)
        (by decide) (by decide) (.inl (by decide)))
    have hsetup := setup_words hsp1 he2
    sha1_norm at ht hsetup ⊢
    rw [ht, hsetup]
    have h2 : (Operand.reg 2 : Operand 64).read s1 = c.initial.regValue .rdx :=
      (he1.agrees.read (by sha1_norm [saveEffect])).trans (hag0.read (by decide))
    have h6 : (Operand.reg 6 : Operand 64).read s1 = c.initial.regValue .rsi :=
      hag01.read (by simp [changes])
    sha1_norm at h2 h6
    rw [h2, h6]
    change ((c.initial.regValue .rdx) <<< 6) + c.initial.regValue .rsi = c.input c.count
    have hc : 64 * c.count = c.blocks.size := by
      have hh := hv.call.blockCountArgumentMatchesBlocks
      dsimp only [Context.count]
      omega
    have hn2 : (c.initial.regValue .rdx).toNat = c.count := by
      have hh := hv.call.blockCountArgumentMatchesBlocks
      omega
    have hr : c.initial.regValue .rdx = BitVec.ofNat 64 c.count := by
      rw [← hn2, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [hr, BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 64 c.count * BitVec.ofNat 64 64 + c.initial.regValue .rsi =
      c.initial.regValue .rsi + BitVec.ofNat 64 (64 * c.count)
    rw [← BitVec.ofNat_mul, Nat.mul_comm c.count 64, BitVec.add_comm]

  have retFinal : memLoad s3.external c.sp 64 = memLoad c.initial.external c.sp 64 := by
    have hp : c.sp = c.stack + 208 := by
      change c.sp = c.sp - 208 + 208
      exact (BitVec.sub_add_cancel _ _).symm
    rw [hp]
    have hapRet : RangeApart c.stack 208 (c.stack + 208) 8 := by
      have ht := RangeApart.offsets c.stack (a := 0) (len := 208) (b := 208) (count := 8)
        (by decide) (by decide) (.inl (by decide))
      sha1_norm at ht ⊢
      simpa only [BitVec.add_zero] using ht
    exact changes_memLoad hag03 hapRet

  refine ⟨n0 + n1 + n2 + n3, s3, ((ha0.trans ha1).trans ha2).trans ha3, hr3,
    changes_code hv hag03 hcInit, ?_, ?_, ?_⟩
  · have ht := he3.rip
    sha1_norm [loadInitialEffect] at ht
    exact ht
  · refine ⟨⟨hsp3, memWritable_of_holds he3 hw2, hv.ramWriteFrame_of_agrees hag03,
      savedFinal, hout, endFinal, retFinal, hag03.rest,
      hag03.directionFlagClear (by simp [changes]) hv.call.directionFlagUnset⟩, hregs, ?_,
      hag03.mono (by simp [changes, frameComponents, Machine.scratchComponents])⟩
    have hi := hag03.agree (.reg 6) (by simp [changes]) rfl
    simp only [Component.Agrees, gprIndex, Fin.getElem_fin] at hi
    simp only [Context.input, State.regValue, Syntax.Reg.fin, Nat.mul_zero]
    sha1_norm [Fin.getElem_fin] at hi ⊢
    exact hi.trans (@BitVec.add_zero 64 (c.initial.GPR[6])).symm
  · exact hag03.mono (by simp [changes, frameComponents, Machine.scratchComponents])


theorem prologueCorrect : PrologueCorrect := by
  intro bindings c hv hn
  obtain ⟨n, s, ha, hr, hc, hp, hat, _⟩ :=
    prologueAdvanceCorrect bindings (returnBoundary c.initial) c hv hv.outside hn
  exact ⟨n, s, ha, hr, hc, hp, hat⟩

end Sha1.Proofs.Compress.Routine
