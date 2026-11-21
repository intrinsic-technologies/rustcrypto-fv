import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.EffectCompose.Memory
import Hkdf.Proofs.Common.EffectCompose.Advance
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Finalize.Suffix.Rekey.Stages

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.Field (AdvanceTriple)

def setupStart (outer : Bool) : BitVec 64 := if outer then 0x10e17e else 0x10e0ee

def setupEnd (outer : Bool) : BitVec 64 := if outer then 0x10e1aa else 0x10e154

def setupOffsets (outer : Bool) : List Nat :=
  if outer then [32,24,16,8,40] else [272,264,256,248,280]

def setupBytes (outer : Bool) : List UInt8 :=
  if outer then [0x4c,0x89,0x74,0x24,0x20,0x4c,0x89,0x7c,0x24,0x18,0x4c,0x89,0x64,0x24,0x10,0x4c,0x89,0x6c,0x24,0x8,0x48,0xc7,0x44,0x24,0x28,0x1,0x0,0x0,0x0,0x48,0x8d,0x7c,0x24,0x8,0x48,0x8d,0x74,0x24,0x48,0xba,0x1,0x0,0x0,0x0]
  else [0x49,0xbe,0xab,0xd9,0x83,0x1f,0x19,0xcd,0xe0,0x5b,0x4c,0x89,0xb4,0x24,0x10,0x1,0x0,0x0,0x49,0xbf,0x7f,0x52,0xe,0x51,0x8c,0x68,0x5,0x9b,0x4c,0x89,0xbc,0x24,0x8,0x1,0x0,0x0,0x49,0xbc,0x72,0xf3,0x6e,0x3c,0x3a,0xf5,0x4f,0xa5,0x4c,0x89,0xa4,0x24,0x0,0x1,0x0,0x0,0x49,0xbd,0x67,0xe6,0x9,0x6a,0x85,0xae,0x67,0xbb,0x4c,0x89,0xac,0x24,0xf8,0x0,0x0,0x0,0x48,0xc7,0x84,0x24,0x18,0x1,0x0,0x0,0x1,0x0,0x0,0x0,0x48,0x8d,0xbc,0x24,0xf8,0x0,0x0,0x0,0x48,0x8d,0x74,0x24,0x48,0xba,0x1,0x0,0x0,0x0]

structure SetupPre (outer : Bool) (s : RamState) : Prop where
  rip : s.RIP = setupStart outer
  writable : ∀ offset ∈ setupOffsets outer,
    MemWritable s (rspOf s + BitVec.ofNat 64 offset) 8
  codeApart : ∀ offset ∈ setupOffsets outer,
    RangeApart (rspOf s + BitVec.ofNat 64 offset) 8 (setupStart outer) (setupBytes outer).length

def setupEffect (outer : Bool) (s : RamState) : Effect :=
  { rip := setupEnd outer
    writes :=
      (if outer then [] else [
        ⟨(.reg 14 : Operand 64), 0x5be0cd191f83d9ab⟩,
        ⟨(.reg 15 : Operand 64), 0x9b05688c510e527f⟩,
        ⟨(.reg 12 : Operand 64), 0xa54ff53a3c6ef372⟩,
        ⟨(.reg 13 : Operand 64), 0xbb67ae856a09e667⟩]) ++
      [⟨(.mem (rspOf s + (if outer then 32 else 272)) : Operand 64),
          if outer then (.reg 14 : Operand 64).read s else 0x5be0cd191f83d9ab⟩,
       ⟨(.mem (rspOf s + (if outer then 24 else 264)) : Operand 64),
          if outer then (.reg 15 : Operand 64).read s else 0x9b05688c510e527f⟩,
       ⟨(.mem (rspOf s + (if outer then 16 else 256)) : Operand 64),
          if outer then (.reg 12 : Operand 64).read s else 0xa54ff53a3c6ef372⟩,
       ⟨(.mem (rspOf s + (if outer then 8 else 248)) : Operand 64),
          if outer then (.reg 13 : Operand 64).read s else 0xbb67ae856a09e667⟩,
       ⟨(.mem (rspOf s + (if outer then 40 else 280)) : Operand 64), 1⟩,
       ⟨(.reg 7 : Operand 64), rspOf s + (if outer then 8 else 248)⟩,
       ⟨(.reg 6 : Operand 64), rspOf s + 72⟩,
       ⟨(.reg 2 : Operand 64), 1⟩] }

def copyBytes : List UInt8 :=
  [0x48,0x8b,0x44,0x24,0x28,0x48,0x89,0x84,0x24,0x68,0x1,0x0,0x0,0x48,0x8b,0x44,0x24,0x20,0x48,0x89,0x84,0x24,0x60,0x1,0x0,0x0,0x48,0x8b,0x44,0x24,0x18,0x48,0x89,0x84,0x24,0x58,0x1,0x0,0x0,0x48,0x8b,0x44,0x24,0x8,0x48,0x8b,0x4c,0x24,0x10,0x48,0x89,0x8c,0x24,0x50,0x1,0x0,0x0,0x48,0x89,0x84,0x24,0x48,0x1,0x0,0x0,0x48,0x8b,0x84,0x24,0xf8,0x0,0x0,0x0,0x48,0x8b,0x8c,0x24,0x0,0x1,0x0,0x0,0x48,0x89,0x84,0x24,0x20,0x1,0x0,0x0,0x48,0x89,0x8c,0x24,0x28,0x1,0x0,0x0,0x48,0x8b,0x84,0x24,0x8,0x1,0x0,0x0,0x48,0x89,0x84,0x24,0x30,0x1,0x0,0x0,0x48,0x8b,0x84,0x24,0x10,0x1,0x0,0x0,0x48,0x89,0x84,0x24,0x38,0x1,0x0,0x0,0x48,0x8b,0x84,0x24,0x18,0x1,0x0,0x0,0x48,0x89,0x84,0x24,0x40,0x1,0x0,0x0]

structure CopyPre (s : RamState) : Prop where
  rip : s.RIP = 0x10e1af
  readable : ∀ offset ∈ ([8,16,24,32,40,248,256,264,272,280] : List Nat),
    MemReadable s (rspOf s + BitVec.ofNat 64 offset) 8
  writable : ∀ offset ∈ ([288,296,304,312,320,328,336,344,352,360] : List Nat),
    MemWritable s (rspOf s + BitVec.ofNat 64 offset) 8
  codeApart : ∀ offset ∈ ([288,296,304,312,320,328,336,344,352,360] : List Nat),
    RangeApart (rspOf s + BitVec.ofNat 64 offset) 8 0x10e1af copyBytes.length

def copyEffect (s : RamState) : Effect :=
  { rip := 0x10e240
    writes := [
      ⟨(.reg 0 : Operand 64), memLoad s.external (rspOf s + 280) 64⟩,
      ⟨(.reg 1 : Operand 64), memLoad s.external (rspOf s + 256) 64⟩] ++
      ([0,1,2,3,4] : List Nat).flatMap fun i => [
        ⟨(.mem (rspOf s + BitVec.ofNat 64 (288+8*i)) : Operand 64),
          memLoad s.external (rspOf s + BitVec.ofNat 64 (248+8*i)) 64⟩,
        ⟨(.mem (rspOf s + BitVec.ofNat 64 (328+8*i)) : Operand 64),
          memLoad s.external (rspOf s + BitVec.ofNat 64 (8+8*i)) 64⟩] }

theorem setup_code (outer : Bool) {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (setupStart outer) (setupBytes outer)) s := by
  cases outer
  · exact programText_slice (programLoaded_codeIn loaded) 0xe0ee (setupBytes false)
      (by decide +kernel) (by decide +kernel)
  · exact programText_slice (programLoaded_codeIn loaded) 0xe17e (setupBytes true)
      (by decide +kernel) (by decide +kernel)

theorem copy_code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x10e1af copyBytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xe1af copyBytes
    (by decide +kernel) (by decide +kernel)

attribute [local x86_compose] setupStart setupEnd setupOffsets

macro "rekey_store_mid " slot:num ", " delta:num ", " len:num ", " total:num ", " next:num
    " using " member:term " against " hout:term : tactic => `(tactic| (
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable $slot $member
    · x86_norm
      intro a ha b hb
      have sep := hP.codeApart $slot $member a ha ($delta+b) (by
        change $delta + b < $total
        change b < $len at hb
        omega)
      x86_norm at sep
      simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat,
        ← BitVec.add_assoc, BitVec.reduceAdd] using sep
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart $slot $member
    · exact boundary_ne_program $hout (inProgram_of_textOffset $next (by decide))))

macro "rekey_load_mid " slot:num ", " next:num " against " hout:term : tactic => `(tactic| (
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable $slot (by simp)
    · apply Effect.Avoids.of_noMem
      x86_norm
      simp [Component.Covers]
    · exact boundary_ne_program $hout (inProgram_of_textOffset $next (by decide))))

macro "rekey_nomem_mid " next:num " against " hout:term : tactic => `(tactic| (
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program $hout (inProgram_of_textOffset $next (by decide))))

set_option maxHeartbeats 1500000 in
private theorem setup_false_run [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (SetupPre false)
      (codeRange (setupStart false) (setupBytes false))
      (Effect.post (setupEffect false)) := by
  advance_begin (mov_r64_imm64_effect_step 0x10e0ee 0x49 0xbe (by simp [RexWPrefix]) (by decide) 0x5be0cd191f83d9ab)
  try (case sub => exact codeRange_slice_subset 0x10e0ee (setupBytes false) 0 10)
  case next =>
    exact fun _ _ ↦ boundary_ne_program outside (inProgram_of_textOffset 0xe0f8 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10e0f8 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 272)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10e0ee (setupBytes false) 10 8)
  rekey_store_mid 272, 10, 8, 102, 0xe100 using (by simp [setupOffsets]) against outside
  advance_then (mov_r64_imm64_effect_step 0x10e100 0x49 0xbf (by simp [RexWPrefix]) (by decide) 0x9b05688c510e527f)
  try (case sub => exact codeRange_slice_subset 0x10e0ee (setupBytes false) 18 10)
  rekey_nomem_mid 0xe10a against outside
  advance_then (mov_m64_r64_effect_step 0x10e10a 0x4c (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 264)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10e0ee (setupBytes false) 28 8)
  rekey_store_mid 264, 28, 8, 102, 0xe112 using (by simp [setupOffsets]) against outside
  advance_then (mov_r64_imm64_effect_step 0x10e112 0x49 0xbc (by simp [RexWPrefix]) (by decide) 0xa54ff53a3c6ef372)
  try (case sub => exact codeRange_slice_subset 0x10e0ee (setupBytes false) 36 10)
  rekey_nomem_mid 0xe11c against outside
  advance_then (mov_m64_r64_effect_step 0x10e11c 0x4c (by simp [RexWPrefix]) 4 (.sib 4 none 0 (.d32 256)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10e0ee (setupBytes false) 46 8)
  rekey_store_mid 256, 46, 8, 102, 0xe124 using (by simp [setupOffsets]) against outside
  advance_then (mov_r64_imm64_effect_step 0x10e124 0x49 0xbd (by simp [RexWPrefix]) (by decide) 0xbb67ae856a09e667)
  try (case sub => exact codeRange_slice_subset 0x10e0ee (setupBytes false) 54 10)
  rekey_nomem_mid 0xe12e against outside
  advance_then (mov_m64_r64_effect_step 0x10e12e 0x4c (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d32 248)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10e0ee (setupBytes false) 64 8)
  rekey_store_mid 248, 64, 8, 102, 0xe136 using (by simp [setupOffsets]) against outside
  advance_then (mov_m64_imm32_effect_step 0x10e136 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 280)) (by decide +kernel) rfl rfl 1)
  try (case sub => exact codeRange_slice_subset 0x10e0ee (setupBytes false) 72 12)
  rekey_store_mid 280, 72, 12, 102, 0xe142 using (by simp [setupOffsets]) against outside
  advance_then (lea_r64_effect_step 0x10e142 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 248)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10e0ee (setupBytes false) 84 8)
  rekey_nomem_mid 0xe14a against outside
  advance_then (lea_r64_effect_step 0x10e14a 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 72)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10e0ee (setupBytes false) 92 5)
  rekey_nomem_mid 0xe14f against outside
  advance_then (mov_r32_imm32_effect_step 0x10e14f 0xba (by decide) 1)
  try (case sub => exact codeRange_slice_subset 0x10e0ee (setupBytes false) 97 5)
  rekey_nomem_mid 0xe154 against outside
  advance_finish [setupEffect]

set_option maxHeartbeats 1500000 in
private theorem setup_true_run [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (SetupPre true)
      (codeRange (setupStart true) (setupBytes true))
      (Effect.post (setupEffect true)) := by
  have sourceRegisters :
      gprNumber (0#1) (rexR (76#8)) (6#3) = (14#5) ∧
      gprNumber (0#1) (rexR (76#8)) (7#3) = (15#5) ∧
      gprNumber (0#1) (rexR (76#8)) (4#3) = (12#5) ∧
      gprNumber (0#1) (rexR (76#8)) (5#3) = (13#5) := by
    decide +kernel
  advance_begin (mov_m64_r64_effect_step 0x10e17e 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10e17e (setupBytes true) 0 5)
  case pre =>
    intro s h
    refine ⟨h.rip, h.writable 32 (by simp [setupOffsets]), ?_⟩
    intro a ha b hb
    exact h.codeApart 32 (by simp [setupOffsets]) a ha b (by change b < 44; change b < 5 at hb; omega)
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm
    exact h.codeApart 32 (by simp [setupOffsets])
  case next =>
    exact fun _ _ ↦ boundary_ne_program outside (inProgram_of_textOffset 0xe183 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10e183 0x4c (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10e17e (setupBytes true) 5 5)
  rekey_store_mid 24, 5, 5, 44, 0xe188 using (by simp [setupOffsets]) against outside
  advance_then (mov_m64_r64_effect_step 0x10e188 0x4c (by simp [RexWPrefix]) 4 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10e17e (setupBytes true) 10 5)
  rekey_store_mid 16, 10, 5, 44, 0xe18d using (by simp [setupOffsets]) against outside
  advance_then (mov_m64_r64_effect_step 0x10e18d 0x4c (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10e17e (setupBytes true) 15 5)
  rekey_store_mid 8, 15, 5, 44, 0xe192 using (by simp [setupOffsets]) against outside
  advance_then (mov_m64_imm32_effect_step 0x10e192 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl 1)
  try (case sub => exact codeRange_slice_subset 0x10e17e (setupBytes true) 20 9)
  rekey_store_mid 40, 20, 9, 44, 0xe19b using (by simp [setupOffsets]) against outside
  advance_then (lea_r64_effect_step 0x10e19b 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10e17e (setupBytes true) 29 5)
  rekey_nomem_mid 0xe1a0 against outside
  advance_then (lea_r64_effect_step 0x10e1a0 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 72)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10e17e (setupBytes true) 34 5)
  rekey_nomem_mid 0xe1a5 against outside
  advance_then (mov_r32_imm32_effect_step 0x10e1a5 0xba (by decide) 1)
  try (case sub => exact codeRange_slice_subset 0x10e17e (setupBytes true) 39 5)
  rekey_nomem_mid 0xe1aa against outside
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [setupEffect]
    all_goals (try (repeat constructor <;> rfl))
  · x86_norm [setupEffect]
    simp [sourceRegisters.1, sourceRegisters.2.1,
      sourceRegisters.2.2.1, sourceRegisters.2.2.2]
  · intro i; cases i <;> x86_norm [setupEffect]
    all_goals (try (repeat constructor <;> rfl))
  · x86_norm [setupEffect]
    all_goals (try (repeat constructor <;> rfl))

theorem setup_arguments {s t : RamState} (outer : Bool)
    (effect : (setupEffect outer s).Holds s t) :
    t.regValue .rdi = stackPtr s + (if outer then 8 else 248) ∧
    t.regValue .rsi = stackPtr s + 72 ∧ t.regValue .rdx = 1 := by
  cases outer
  · exact effect.writes.2.2.2.2.2.2.2.2.2
  · exact effect.writes.2.2.2.2.2

theorem setup_run [Bindings] (outer : Bool) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (SetupPre outer) (codeRange (setupStart outer) (setupBytes outer))
      (Effect.post (setupEffect outer)) := by
  cases outer
  · exact setup_false_run boundary outside
  · exact setup_true_run boundary outside

set_option maxHeartbeats 2500000 in
theorem copy_run [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary CopyPre (codeRange 0x10e1af copyBytes)
      (Effect.post copyEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x10e1af 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10e1af copyBytes 0 5)
  case pre => intro s h; exact ⟨h.rip, h.readable 40 (by simp)⟩
  case next =>
    exact fun _ _ ↦ boundary_ne_program outside (inProgram_of_textOffset 0xe1b4 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10e1b4 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 360)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10e1af copyBytes 5 8)
  rekey_store_mid 360, 5, 8, 145, 0xe1bc using (by simp) against outside
  advance_then (mov_r64_m64_effect_step 0x10e1bc 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10e1af copyBytes 13 5)
  rekey_load_mid 32, 0xe1c1 against outside
  advance_then (mov_m64_r64_effect_step 0x10e1c1 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 352)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10e1af copyBytes 18 8)
  rekey_store_mid 352, 18, 8, 145, 0xe1c9 using (by simp) against outside
  advance_then (mov_r64_m64_effect_step 0x10e1c9 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10e1af copyBytes 26 5)
  rekey_load_mid 24, 0xe1ce against outside
  advance_then (mov_m64_r64_effect_step 0x10e1ce 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 344)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10e1af copyBytes 31 8)
  rekey_store_mid 344, 31, 8, 145, 0xe1d6 using (by simp) against outside
  advance_then (mov_r64_m64_effect_step 0x10e1d6 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10e1af copyBytes 39 5)
  rekey_load_mid 8, 0xe1db against outside
  advance_then (mov_r64_m64_effect_step 0x10e1db 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10e1af copyBytes 44 5)
  rekey_load_mid 16, 0xe1e0 against outside
  advance_then (mov_m64_r64_effect_step 0x10e1e0 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 336)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10e1af copyBytes 49 8)
  rekey_store_mid 336, 49, 8, 145, 0xe1e8 using (by simp) against outside
  advance_then (mov_m64_r64_effect_step 0x10e1e8 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 328)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10e1af copyBytes 57 8)
  rekey_store_mid 328, 57, 8, 145, 0xe1f0 using (by simp) against outside
  advance_then (mov_r64_m64_effect_step 0x10e1f0 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 248)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10e1af copyBytes 65 8)
  rekey_load_mid 248, 0xe1f8 against outside
  advance_then (mov_r64_m64_effect_step 0x10e1f8 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 256)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10e1af copyBytes 73 8)
  rekey_load_mid 256, 0xe200 against outside
  advance_then (mov_m64_r64_effect_step 0x10e200 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 288)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10e1af copyBytes 81 8)
  rekey_store_mid 288, 81, 8, 145, 0xe208 using (by simp) against outside
  advance_then (mov_m64_r64_effect_step 0x10e208 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 296)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10e1af copyBytes 89 8)
  rekey_store_mid 296, 89, 8, 145, 0xe210 using (by simp) against outside
  advance_then (mov_r64_m64_effect_step 0x10e210 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 264)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10e1af copyBytes 97 8)
  rekey_load_mid 264, 0xe218 against outside
  advance_then (mov_m64_r64_effect_step 0x10e218 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 304)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10e1af copyBytes 105 8)
  rekey_store_mid 304, 105, 8, 145, 0xe220 using (by simp) against outside
  advance_then (mov_r64_m64_effect_step 0x10e220 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 272)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10e1af copyBytes 113 8)
  rekey_load_mid 272, 0xe228 against outside
  advance_then (mov_m64_r64_effect_step 0x10e228 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 312)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10e1af copyBytes 121 8)
  rekey_store_mid 312, 121, 8, 145, 0xe230 using (by simp) against outside
  advance_then (mov_r64_m64_effect_step 0x10e230 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 280)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10e1af copyBytes 129 8)
  rekey_load_mid 280, 0xe238 against outside
  advance_then (mov_m64_r64_effect_step 0x10e238 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 320)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x10e1af copyBytes 137 8)
  rekey_store_mid 320, 137, 8, 145, 0xe240 using (by simp) against outside
  advance_finish [copyEffect, List.flatMap_cons, List.flatMap_nil, State.regValue]

end Hkdf.Proofs.Standard.Finalize.Suffix.Rekey.Stages
