import Hkdf.Proofs.NewExpand.Extract.Initialize.Pads.Frame
import Hkdf.Proofs.Key.Hash.Initialize.Payload
import Hkdf.Proofs.Common.EffectCompose.Memory
import Hkdf.Proofs.Common.EffectCompose.Advance
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Extract.Initialize.Pads

open Hkdf.Spec.Program Hkdf.Proofs.Common Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.SHA256
open Hkdf.Proofs.Common.Field (AdvanceTriple)
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def IVRegisters (s : RamState) : Prop :=
  s.regValue .r12 = 0x5be0cd191f83d9ab ∧
  s.regValue .r13 = 0x9b05688c510e527f ∧
  s.regValue .rbp = 0xa54ff53a3c6ef372 ∧
  s.regValue .rbx = 0xbb67ae856a09e667

private def setupStart (outer : Bool) : BitVec 64 := if outer then 0x10fb8e else 0x10fb0e

private def setupEnd (outer : Bool) : BitVec 64 := if outer then 0x10fbba else 0x10fb5f

private def setupOffset (outer : Bool) : Nat := if outer then 40 else 0

private def setupOffsets (outer : Bool) : List Nat :=
  if outer then [64,56,48,40,72] else [24,16,8,0,32]

private def setupBytes (outer : Bool) : List UInt8 :=
  if outer then
    [0x4c,0x89,0x64,0x24,0x40, 0x4c,0x89,0x6c,0x24,0x38,
     0x48,0x89,0x6c,0x24,0x30, 0x48,0x89,0x5c,0x24,0x28,
     0x48,0xc7,0x44,0x24,0x48,0x01,0x00,0x00,0x00,
     0x48,0x8d,0x7c,0x24,0x28, 0x48,0x8d,0x74,0x24,0x78,
     0xba,0x01,0x00,0x00,0x00]
  else
    [0x49,0xbc,0xab,0xd9,0x83,0x1f,0x19,0xcd,0xe0,0x5b,
     0x4c,0x89,0x64,0x24,0x18,
     0x49,0xbd,0x7f,0x52,0x0e,0x51,0x8c,0x68,0x05,0x9b,
     0x4c,0x89,0x6c,0x24,0x10,
     0x48,0xbd,0x72,0xf3,0x6e,0x3c,0x3a,0xf5,0x4f,0xa5,
     0x48,0x89,0x6c,0x24,0x08,
     0x48,0xbb,0x67,0xe6,0x09,0x6a,0x85,0xae,0x67,0xbb,
     0x48,0x89,0x1c,0x24, 0x48,0xc7,0x44,0x24,0x20,0x01,0x00,0x00,0x00,
     0x48,0x89,0xe7, 0x48,0x8d,0x74,0x24,0x78, 0xba,0x01,0x00,0x00,0x00]

private structure SetupPre (outer : Bool) (s : RamState) : Prop where
  rip : s.RIP = setupStart outer
  writable : ∀ offset ∈ setupOffsets outer,
    MemWritable s (rspOf s + BitVec.ofNat 64 offset) 8
  codeApart : ∀ offset ∈ setupOffsets outer,
    RangeApart (rspOf s + BitVec.ofNat 64 offset) 8 (setupStart outer) (setupBytes outer).length

private def setupEffect (outer : Bool) (s : RamState) : Effect :=
  { rip := setupEnd outer
    writes :=
      (if outer then [] else
        [⟨(.reg 12 : Operand 64), 0x5be0cd191f83d9ab⟩,
         ⟨(.reg 13 : Operand 64), 0x9b05688c510e527f⟩,
         ⟨(.reg 5 : Operand 64), 0xa54ff53a3c6ef372⟩,
         ⟨(.reg 3 : Operand 64), 0xbb67ae856a09e667⟩]) ++
      [⟨(.mem (rspOf s + (if outer then 64 else 24)) : Operand 64),
          if outer then (.reg 12 : Operand 64).read s else 0x5be0cd191f83d9ab⟩,
       ⟨(.mem (rspOf s + (if outer then 56 else 16)) : Operand 64),
          if outer then (.reg 13 : Operand 64).read s else 0x9b05688c510e527f⟩,
       ⟨(.mem (rspOf s + (if outer then 48 else 8)) : Operand 64),
          if outer then (.reg 5 : Operand 64).read s else 0xa54ff53a3c6ef372⟩,
       ⟨(.mem (rspOf s + BitVec.ofNat 64 (setupOffset outer)) : Operand 64),
          if outer then (.reg 3 : Operand 64).read s else 0xbb67ae856a09e667⟩,
       ⟨(.mem (rspOf s + (if outer then 72 else 32)) : Operand 64), 1⟩,
       ⟨(.reg 7 : Operand 64), rspOf s + BitVec.ofNat 64 (setupOffset outer)⟩,
       ⟨(.reg 6 : Operand 64), rspOf s + 120⟩,
       ⟨(.reg 2 : Operand 64), 1⟩] }

attribute [local x86_compose] setupStart setupEnd setupOffset setupOffsets

local macro "pad_setup_store " slot:num ", " delta:num ", " len:num ", " total:num ", " next:num
    " against " outside:term : tactic => `(tactic| (
  case mid =>
    intro s t hPre hEffect hObs
    refine ⟨StorePre.of_holds hEffect (hObs true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · have writable := hPre.writable $slot (by decide)
      x86_norm [BitVec.add_zero] at writable ⊢
      exact writable
    · x86_norm
      intro i hi j hj
      have separate := hPre.codeApart $slot (by decide) i hi ($delta + j) (by
        change $delta + j < $total
        change j < $len at hj
        omega)
      x86_norm at separate
      simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, ← BitVec.add_assoc,
        BitVec.reduceAdd] using separate
    · apply Effect.Local.avoids (by x86_local) (hObs true)
      apply Effect.avoids_codeRange
      have apart := hPre.codeApart $slot (by decide)
      x86_norm [BitVec.add_zero] at apart ⊢
      exact apart
    · exact boundary_ne_program $outside (inProgram_of_textOffset $next (by decide))))

local macro "pad_setup_next " next:num " against " outside:term : tactic => `(tactic| (
  case mid =>
    intro s t hPre hEffect hObs
    exact ⟨hEffect.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program $outside (inProgram_of_textOffset $next (by decide))⟩))

set_option maxHeartbeats 1500000 in
private theorem setup_inner_run [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (SetupPre false)
      (codeRange (setupStart false) (setupBytes false))
      (Effect.post (setupEffect false)) := by
  advance_begin (mov_r64_imm64_effect_step 0x10fb0e 0x49 0xbc (by simp [RexWPrefix])
    (by decide) 0x5be0cd191f83d9ab)
  try (case sub => exact codeRange_slice_subset 0x10fb0e (setupBytes false) 0 10)
  case next =>
    exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xfb18 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10fb18 0x4c (by simp [RexWPrefix]) 4
    (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10fb0e (setupBytes false) 10 5)
  pad_setup_store 24, 10, 5, 81, 0xfb1d against outside
  advance_then (mov_r64_imm64_effect_step 0x10fb1d 0x49 0xbd (by simp [RexWPrefix])
    (by decide) 0x9b05688c510e527f)
  try (case sub => exact codeRange_slice_subset 0x10fb0e (setupBytes false) 15 10)
  pad_setup_next 0xfb27 against outside
  advance_then (mov_m64_r64_effect_step 0x10fb27 0x4c (by simp [RexWPrefix]) 5
    (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10fb0e (setupBytes false) 25 5)
  pad_setup_store 16, 25, 5, 81, 0xfb2c against outside
  advance_then (mov_r64_imm64_effect_step 0x10fb2c 0x48 0xbd (by simp [RexWPrefix])
    (by decide) 0xa54ff53a3c6ef372)
  try (case sub => exact codeRange_slice_subset 0x10fb0e (setupBytes false) 30 10)
  pad_setup_next 0xfb36 against outside
  advance_then (mov_m64_r64_effect_step 0x10fb36 0x48 (by simp [RexWPrefix]) 5
    (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10fb0e (setupBytes false) 40 5)
  pad_setup_store 8, 40, 5, 81, 0xfb3b against outside
  advance_then (mov_r64_imm64_effect_step 0x10fb3b 0x48 0xbb (by simp [RexWPrefix])
    (by decide) 0xbb67ae856a09e667)
  try (case sub => exact codeRange_slice_subset 0x10fb0e (setupBytes false) 45 10)
  pad_setup_next 0xfb45 against outside
  advance_then (mov_m64_r64_effect_step 0x10fb45 0x48 (by simp [RexWPrefix]) 3
    (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10fb0e (setupBytes false) 55 4)
  pad_setup_store 0, 55, 4, 81, 0xfb49 against outside
  advance_then (mov_m64_imm32_effect_step 0x10fb49 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl 1)
  try (case sub => exact codeRange_slice_subset 0x10fb0e (setupBytes false) 59 9)
  pad_setup_store 32, 59, 9, 81, 0xfb52 against outside
  advance_then (mov_r64_r64_effect_step 0x10fb52 0x48 0xe7 (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x10fb0e (setupBytes false) 68 3)
  pad_setup_next 0xfb55 against outside
  advance_then (lea_r64_effect_step 0x10fb55 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d8 120)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10fb0e (setupBytes false) 71 5)
  pad_setup_next 0xfb5a against outside
  advance_then (mov_r32_imm32_effect_step 0x10fb5a 0xba (by decide) 1)
  try (case sub => exact codeRange_slice_subset 0x10fb0e (setupBytes false) 76 5)
  pad_setup_next 0xfb5f against outside
  advance_finish [setupEffect, BitVec.add_zero]

set_option maxHeartbeats 1500000 in
private theorem setup_outer_run [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (SetupPre true)
      (codeRange (setupStart true) (setupBytes true))
      (Effect.post (setupEffect true)) := by
  have extendedSource :
      gprNumber (0#1) (rexR (76 : UInt8).toBitVec) (4#3) = (12#5) ∧
      gprNumber (0#1) (rexR (76 : UInt8).toBitVec) (5#3) = (13#5) ∧
      gprNumber (0#1) (rexR (72 : UInt8).toBitVec) (5#3) = (5#5) ∧
      gprNumber (0#1) (rexR (72 : UInt8).toBitVec) (3#3) = (3#5) := by decide +kernel
  advance_begin (mov_m64_r64_effect_step 0x10fb8e 0x4c (by simp [RexWPrefix]) 4
    (.sib 4 none 0 (.d8 64)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10fb8e (setupBytes true) 0 5)
  case pre =>
    intro s h
    refine ⟨h.rip, h.writable 64 (by decide), ?_⟩
    intro i hi j hj
    exact h.codeApart 64 (by decide) i hi j (by change j < 44; change j < 5 at hj; omega)
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm
    exact h.codeApart 64 (by decide)
  case next =>
    exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xfb93 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10fb93 0x4c (by simp [RexWPrefix]) 5
    (.sib 4 none 0 (.d8 56)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10fb8e (setupBytes true) 5 5)
  pad_setup_store 56, 5, 5, 44, 0xfb98 against outside
  advance_then (mov_m64_r64_effect_step 0x10fb98 0x48 (by simp [RexWPrefix]) 5
    (.sib 4 none 0 (.d8 48)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10fb8e (setupBytes true) 10 5)
  pad_setup_store 48, 10, 5, 44, 0xfb9d against outside
  advance_then (mov_m64_r64_effect_step 0x10fb9d 0x48 (by simp [RexWPrefix]) 3
    (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10fb8e (setupBytes true) 15 5)
  pad_setup_store 40, 15, 5, 44, 0xfba2 against outside
  advance_then (mov_m64_imm32_effect_step 0x10fba2 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d8 72)) (by decide +kernel) rfl rfl 1)
  try (case sub => exact codeRange_slice_subset 0x10fb8e (setupBytes true) 20 9)
  pad_setup_store 72, 20, 9, 44, 0xfbab against outside
  advance_then (lea_r64_effect_step 0x10fbab 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10fb8e (setupBytes true) 29 5)
  pad_setup_next 0xfbb0 against outside
  advance_then (lea_r64_effect_step 0x10fbb0 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d8 120)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10fb8e (setupBytes true) 34 5)
  pad_setup_next 0xfbb5 against outside
  advance_then (mov_r32_imm32_effect_step 0x10fbb5 0xba (by decide) 1)
  try (case sub => exact codeRange_slice_subset 0x10fb8e (setupBytes true) 39 5)
  pad_setup_next 0xfbba against outside
  apply AdvanceTriple.block_end
  intro s t _ effect
  apply effect.weaken
  · x86_norm [setupEffect]
    repeat constructor <;> rfl
  · x86_norm [setupEffect]
    simp only [extendedSource.1, extendedSource.2.1, extendedSource.2.2.1, extendedSource.2.2.2, and_self]
  · intro i
    cases i <;> x86_norm [setupEffect]
  · x86_norm [setupEffect]

private theorem setup_components (outer : Bool) (s : RamState) :
    (setupEffect outer s).components =
      (if outer then [] else [.reg 12, .reg 13, .reg 5, .reg 3]) ++
      ([24,16,8,0,32] : List Nat).map (fun i =>
        .mem (rspOf s + BitVec.ofNat 64 (setupOffset outer) + BitVec.ofNat 64 i) 8) ++
      [.reg 7, .reg 6, .reg 2, .rip] := by
  cases outer <;> simp [setupEffect, setupOffset, Effect.components, Write.component,
    Operand.component, BitVec.add_assoc, BitVec.reduceAdd]

private theorem setup_agrees {s t : RamState} (outer : Bool)
    (effect : (setupEffect outer s).Holds s t) :
    AgreesExcept [.reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 12, .reg 13,
      .mem (rspOf s + BitVec.ofNat 64 (setupOffset outer)) 40, .rip] s t := by
  refine ⟨?_, ?_, effect.agrees.rest, effect.agrees.grow⟩
  · intro c missing noMem
    apply effect.agrees.agree c ?_ noMem
    rw [setup_components]
    intro member
    simp only [List.mem_append, List.mem_map] at member
    rcases member with (member | ⟨i, _, rfl⟩) | member
    · apply missing
      cases outer
      · simp only [Bool.false_eq_true, ite_false, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl <;> simp
      · exact (List.not_mem_nil member).elim
    · exact Bool.noConfusion noMem
    · apply missing
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> simp
  · intro a outside
    apply effect.agrees.memory a
    intro c member covered
    rw [setup_components] at member
    simp only [List.mem_append, List.mem_map] at member
    rcases member with (member | ⟨i, hi, rfl⟩) | member
    · cases outer
      · simp only [Bool.false_eq_true, ite_false, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl <;> exact covered.elim
      · exact (List.not_mem_nil member).elim
    · obtain ⟨j, hj, address⟩ := covered
      refine outside (.mem (rspOf s + BitVec.ofNat 64 (setupOffset outer)) 40)
        (by simp) ⟨i+j, ?_, ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        omega
      · rw [BitVec.ofNat_add, ← BitVec.add_assoc]
        exact address
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> exact covered.elim

private theorem setup_payload {t : RamState} {address : BitVec 64}
    (readable : MemReadable t address 40)
    (w0 : memLoad t.external address 64 = 0xbb67ae856a09e667)
    (w1 : memLoad t.external (address + 8) 64 = 0xa54ff53a3c6ef372)
    (w2 : memLoad t.external (address + 16) 64 = 0x9b05688c510e527f)
    (w3 : memLoad t.external (address + 24) 64 = 0x5be0cd191f83d9ab)
    (count : memLoad t.external (address + 32) 64 = 1) :
    HashStateAt t address initialHash ∧ loadBytes t.external (address + 32) 8 = .ok 1 := by
  refine ⟨Hkdf.Proofs.Key.Hash.Initialize.hashStateAt_initialHash_of_packedWords
    ⟨by have low := readable.low; omega, fun i hi => readable.mem i (by omega)⟩ ?_, ?_⟩
  · intro j hj
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
    · simpa only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, List.getElem!_cons_zero] using w0
    · exact w1
    · exact w2
    · exact w3
  · have bytes := Bytes.of_memLoad (n := 64) (m := t.external) (a := address + 32) (by
      intro i hi
      change (t.external[address + BitVec.ofNat 64 32 + BitVec.ofNat 64 i]?).isSome
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact readable.mem (32+i) (by omega))
    rw [count] at bytes
    exact bytes.loadBytes64

private theorem setup_results {s t : RamState} (outer : Bool)
    (effect : (setupEffect outer s).Holds s t)
    (readable : MemReadable t (rspOf s + BitVec.ofNat 64 (setupOffset outer)) 40)
    (iv : outer = true → IVRegisters s) :
    t.regValue .rdi = rspOf s + BitVec.ofNat 64 (setupOffset outer) ∧
      t.regValue .rsi = rspOf s + 120 ∧ t.regValue .rdx = 1 ∧
      HashStateAt t (rspOf s + BitVec.ofNat 64 (setupOffset outer)) initialHash ∧
      loadBytes t.external (rspOf s + BitVec.ofNat 64 (setupOffset outer) + 32) 8 = .ok 1 ∧
      IVRegisters t := by
  cases outer
  · rcases effect.writes with ⟨r12, r13, rbp, rbx, w3, w2, w1, w0, count, dest, src, blocks⟩
    simp only [setupOffset, Bool.false_eq_true, ite_false, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at readable ⊢
    have w0' : memLoad t.external (rspOf s) 64 = 0xbb67ae856a09e667 := by
      rw [← BitVec.add_zero (rspOf s)]
      exact w0
    have dest' : t.regValue .rdi = rspOf s := by
      rw [← BitVec.add_zero (rspOf s)]
      exact dest
    obtain ⟨hash, length⟩ := setup_payload readable w0' w1 w2 w3 count
    exact ⟨dest', src, blocks, hash, length, r12, r13, rbp, rbx⟩
  · rcases effect.writes with ⟨w3, w2, w1, w0, count, dest, src, blocks⟩
    obtain ⟨r12, r13, rbp, rbx⟩ := iv rfl
    have readReg (r : BitVec 5) (missing : .reg r ∉ (setupEffect true s).components) :
        (Operand.reg r : Operand 64).read t = (Operand.reg r : Operand 64).read s :=
      effect.agrees.read missing
    have ivT : IVRegisters t := by
      simp only [IVRegisters]
      refine ⟨(readReg 12 ?_).trans r12, (readReg 13 ?_).trans r13,
        (readReg 5 ?_).trans rbp, (readReg 3 ?_).trans rbx⟩
      all_goals rw [setup_components]; simp
    have offset : BitVec.ofNat 64 (setupOffset true) = 40 := rfl
    rw [offset] at readable ⊢
    obtain ⟨hash, length⟩ := setup_payload readable (w0.trans rbx)
      (by rw [BitVec.add_assoc, show (40 : BitVec 64) + 8 = 48 by decide]; exact w1.trans rbp)
      (by rw [BitVec.add_assoc, show (40 : BitVec 64) + 16 = 56 by decide]; exact w2.trans r13)
      (by rw [BitVec.add_assoc, show (40 : BitVec 64) + 24 = 64 by decide]; exact w3.trans r12)
      (by rw [BitVec.add_assoc, show (40 : BitVec 64) + 32 = 72 by decide]; exact count)
    exact ⟨dest, src, blocks, hash, length, ivT⟩

theorem setup [Bindings] (outer : Bool) {initial s : RamState} {boundary : ReturnBoundary}
    {salt : Option ByteArray} {ikm : ByteArray}
    (pre : ExtractPre initial boundary salt ikm) (state : Frame initial s boundary)
    (rip : s.RIP = if outer then 0x10fb8e else 0x10fb0e)
    (iv : outer = true → IVRegisters s) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      t.RIP = (if outer then 0x10fbba else 0x10fb5f) ∧
      AgreesExcept [.reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 12, .reg 13,
        .mem (base initial + (if outer then 40 else 0)) 40, .rip] s t ∧
      t.regValue .rdi = base initial + (if outer then 40 else 0) ∧
      t.regValue .rsi = base initial + 120 ∧ t.regValue .rdx = 1 ∧
      HashStateAt t (base initial + (if outer then 40 else 0)) initialHash ∧
      loadBytes t.external (base initial + (if outer then 40 else 0) + 32) 8 = .ok 1 ∧
      IVRegisters t := by
  have stack := pre.call.stack
  have separate : (Stack.region initial 2264).Avoids InProgram :=
    fun a ha hp => pre.call.stackAvoid a ha (.inl hp)
  have rsp : rspOf s = base initial := state.rsp
  have offsets (i : Nat) (hi : i ∈ setupOffsets outer) : i ≤ 72 ∧ i % 8 = 0 := by
    cases outer <;> simp only [setupOffsets, Bool.false_eq_true, ite_false, ite_true,
      List.mem_cons, List.not_mem_nil, or_false] at hi
    all_goals rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide
  have writable (i : Nat) (hi : i ∈ setupOffsets outer) :
      MemWritable s (rspOf s + BitVec.ofNat 64 i) 8 := by
    obtain ⟨bound, aligned⟩ := offsets i hi
    rw [rsp, base_add initial (by omega : i ≤ 456)]
    exact CallFrame.stack_writable8 stack pre.call.stackAvoid state.allocated (by omega) (by omega)
  have noCode (i : Nat) (hi : i ∈ setupOffsets outer) :
      RangeApart (rspOf s + BitVec.ofNat 64 i) 8 (setupStart outer) (setupBytes outer).length := by
    have bound := (offsets i hi).1
    rw [rsp, base_add initial (by omega : i ≤ 456)]
    cases outer
    · exact CallFrame.stack_codeApart stack separate (codeOffset := 0xfb0e)
        (by omega) (by omega) (by decide)
    · exact CallFrame.stack_codeApart stack separate (codeOffset := 0xfb8e)
        (by omega) (by omega) (by decide)
  have bytes : CodeIn (codeRange (setupStart outer) (setupBytes outer)) s := by
    cases outer
    · exact programText_slice (programLoaded_codeIn state.loaded) 0xfb0e (setupBytes false)
        (by decide) (by decide +kernel)
    · exact programText_slice (programLoaded_codeIn state.loaded) 0xfb8e (setupBytes true)
        (by decide) (by decide +kernel)
  have run : AdvanceTriple boundary (SetupPre outer)
      (codeRange (setupStart outer) (setupBytes outer)) (Effect.post (setupEffect outer)) := by
    cases outer
    · exact setup_inner_run boundary pre.call.outerBoundary
    · exact setup_outer_run boundary pre.call.outerBoundary
  obtain ⟨fuel, t, advances, ready, _, effect⟩ := run s
    (supportedMachine_readyToStep state.machine) bytes ⟨rip, writable, noCode⟩
  have offsetBound : setupOffset outer ≤ 40 := by cases outer <;> decide
  have readable : MemReadable t (rspOf s + BitVec.ofNat 64 (setupOffset outer)) 40 := by
    apply MemReadable.of_holds effect
    rw [rsp, base_add initial (by omega : setupOffset outer ≤ 456)]
    exact CallFrame.stack_readable stack state.allocated (by omega) (by omega)
  have offset : BitVec.ofNat 64 (setupOffset outer) = (if outer then 40 else 0) := by
    cases outer <;> rfl
  have agrees := setup_agrees outer effect
  have results := setup_results outer effect readable iv
  rw [rsp, offset] at agrees results
  exact ⟨fuel, t, advances, ready, effect.rip, agrees, results⟩

end Hkdf.Proofs.NewExpand.Extract.Initialize.Pads
