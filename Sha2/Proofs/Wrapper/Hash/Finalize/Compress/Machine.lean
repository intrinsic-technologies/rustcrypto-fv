import Sha2.Proofs.Common.EffectCompose.Memory
import Sha2.Proofs.Common.Field.Operations.Run.Compose
import Sha2.Proofs.Common.Machine.Code
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.MovLoad.Triple
import Sha2.Proofs.Common.EffectCompose.Advance
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Hash.Finalize.Compress

open Sha2.Spec Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field (AdvanceTriple)
open Sha2.Proofs.Common.Machine

structure FirstPre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  readable : MemReadable s (rspOf s + 56) 8
  writable : MemWritable s (rspOf s + 160) 8
  apart : RangeApart (rspOf s + 160) 8 p 13

def firstBytes : List UInt8 := [0x48,0x8b,0x44,0x24,0x38,0x48,0x89,0x84,0x24,0xa0,0,0,0]

def firstEffect (p : BitVec 64) (s : RamState) : Effect :=
  { rip := (p+13)
    writes := [⟨(.reg 0 : Operand 64), memLoad s.external (rspOf s + 56) 64⟩,
      ⟨(.mem (rspOf s + 160) : Operand 64), memLoad s.external (rspOf s + 56) 64⟩] }

theorem first_head [Bindings] (p : BitVec 64) (boundary : ReturnBoundary)
    (next : ∀ i : Nat, i ≤ 13 → p + BitVec.ofNat 64 i ≠ boundary.rip) :
    AdvanceTriple boundary (FirstPre p) (codeRange p firstBytes) (Effect.post (firstEffect p)) := by
  advance_begin (mov_r64_m64_effect_step p 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 56)) (by decide) rfl rfl)
  case pre => intro s h; exact ⟨h.rip, h.readable⟩
  case next => exact fun _ _ => next 5 (by decide)
  advance_then (mov_m64_r64_effect_step (p+5) 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 160)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset p firstBytes 5 8)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable
    · x86_norm
      intro i hi j hj he
      exact hP.apart i hi (5+j) (by omega) (by
        simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add, ← BitVec.add_assoc,
          BitVec.reduceAdd] using he)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart
    · x86_norm
      exact next 13 (by decide)
  advance_finish [firstEffect]

structure LastPre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  writable : ∀ i ∈ ([56,160] : List (BitVec 64)), MemWritable s (rspOf s + i) 8
  apart : ∀ i ∈ ([56,160] : List (BitVec 64)), RangeApart (rspOf s + i) 8 p 13

def lastBytes : List UInt8 := [0x4c,0x89,0x7c,0x24,0x38,0x4c,0x89,0xbc,0x24,0xa0,0,0,0]

def lastEffect (p : BitVec 64) (s : RamState) : Effect :=
  { rip := (p+13)
    writes := [⟨(.mem (rspOf s + 56) : Operand 64), s.regValue .r15⟩,
      ⟨(.mem (rspOf s + 160) : Operand 64), s.regValue .r15⟩] }

theorem last_head [Bindings] (p : BitVec 64) (boundary : ReturnBoundary)
    (next : ∀ i : Nat, i ≤ 13 → p + BitVec.ofNat 64 i ≠ boundary.rip) :
    AdvanceTriple boundary (LastPre p) (codeRange p lastBytes) (Effect.post (lastEffect p)) := by
  advance_begin (mov_m64_r64_effect_step p 0x4c (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d8 56)) (by decide) rfl rfl)
  case pre =>
    intro s h
    refine ⟨h.rip, h.writable 56 (by simp), ?_⟩
    intro i hi j hj he
    change j < 5 at hj
    exact h.apart 56 (by simp) i hi j (by omega) he
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm
    exact h.apart 56 (by simp)
  case next => exact fun _ _ => next 5 (by decide)
  advance_then (mov_m64_r64_effect_step (p+5) 0x4c (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d32 160)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset p lastBytes 5 8)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 160 (by simp)
    · x86_norm
      intro i hi j hj he
      exact hP.apart 160 (by simp) i hi (5+j) (by omega) (by
        simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add, ← BitVec.add_assoc,
          BitVec.reduceAdd] using he)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 160 (by simp)
    · x86_norm
      exact next 13 (by decide)
  advance_finish [lastEffect]

def setupBytes : List UInt8 := [0x48,0x8d,0x74,0x24,0x68,0xba,1,0,0,0,0x4c,0x89,0xf7]

def setupEffect (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p + 13
    writes := [⟨(.reg 6 : Operand 64), rspOf s + 104⟩,
      ⟨(.reg 2 : Operand 64), 1⟩,
      ⟨(.reg 7 : Operand 64), s.regValue .r14⟩] }

theorem setup [Bindings] (p : BitVec 64) (boundary : ReturnBoundary)
    (next : ∀ i : Nat, i ≤ 13 → p + BitVec.ofNat 64 i ≠ boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = p) (codeRange p setupBytes)
      (Effect.post (setupEffect p)) := by
  advance_begin (lea_r64_effect_step p 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d8 104)) (by decide) rfl rfl)
  case next => exact fun _ _ => next 5 (by decide)
  advance_then (mov_r32_imm32_effect_step (p+5) 0xba (by decide) 1)
  try (case sub => exact codeRange_slice_subset p setupBytes 5 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · x86_norm
      exact next 10 (by decide)
  advance_then (mov_r64_r64_effect_step (p+10) 0x4c 0xf7 (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset p setupBytes 10 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Avoids.of_noMem ?_ _, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · simp [Component.Covers]
    · x86_norm
      exact next 13 (by decide)
  advance_finish [setupEffect]

end Sha2.Proofs.Wrapper.Hash.Finalize.Compress
