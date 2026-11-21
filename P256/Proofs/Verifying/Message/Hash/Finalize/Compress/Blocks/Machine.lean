import P256.Proofs.Verifying.Message.Hash.Finalize.Compress.Blocks.CopyWords
import P256.Proofs.Common.EffectCompose.Advance
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash.Finalize.Compress.Blocks.Machine

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program

structure FirstPre (s : RamState) : Prop where
  rip : s.RIP = 0x10d77e
  readable : MemReadable s (rspOf s + 184) 8
  writable : MemWritable s (rspOf s + 56) 8
  apart : RangeApart (rspOf s + 56) 8 0x10d77e 13

def firstBytes : List UInt8 := [0x48,0x8b,0x84,0x24,0xb8,0x0,0x0,0x0,0x48,0x89,0x44,0x24,0x38]

def firstEffect (s : RamState) : Effect :=
  { rip := 0x10d78b
    writes := [⟨(.reg 0 : Operand 64), memLoad s.external (rspOf s + 184) 64⟩,
      ⟨(.mem (rspOf s + 56) : Operand 64), memLoad s.external (rspOf s + 184) 64⟩] }

theorem first_head [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary FirstPre (codeRange 0x10d77e firstBytes) (Effect.post firstEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x10d77e 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 184)) (by decide) rfl rfl)
  case pre => intro s h; exact ⟨h.rip, h.readable⟩
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xd786 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10d786 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 56)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d77e firstBytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable
    · x86_norm
      intro i hi j hj he
      exact hP.apart i hi (8+j) (by omega) (by
        simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add, ← BitVec.add_assoc,
          BitVec.reduceAdd] using he)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd78b (by decide))
  advance_finish [firstEffect]

structure LastPre (s : RamState) : Prop where
  rip : s.RIP = 0x10d857
  writable : ∀ i ∈ ([184,56] : List (BitVec 64)), MemWritable s (rspOf s + i) 8
  apart : ∀ i ∈ ([184,56] : List (BitVec 64)), RangeApart (rspOf s + i) 8 0x10d857 13

def lastBytes : List UInt8 := [0x4c,0x89,0xbc,0x24,0xb8,0x0,0x0,0x0,0x4c,0x89,0x7c,0x24,0x38]

def lastEffect (s : RamState) : Effect :=
  { rip := 0x10d864
    writes := [⟨(.mem (rspOf s + 184) : Operand 64), s.regValue .r15⟩,
      ⟨(.mem (rspOf s + 56) : Operand 64), s.regValue .r15⟩] }

theorem last_head [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary LastPre (codeRange 0x10d857 lastBytes) (Effect.post lastEffect) := by
  advance_begin (mov_m64_r64_effect_step 0x10d857 0x4c (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d32 184)) (by decide) rfl rfl)
  case pre =>
    intro s h
    refine ⟨h.rip, h.writable 184 (by simp), ?_⟩
    intro i hi j hj he
    change j < 8 at hj
    exact h.apart 184 (by simp) i hi j (by omega) he
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm
    exact h.apart 184 (by simp)
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xd85f (by decide))
  advance_then (mov_m64_r64_effect_step 0x10d85f 0x4c (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d8 56)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d857 lastBytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 56 (by simp)
    · x86_norm
      intro i hi j hj he
      exact hP.apart 56 (by simp) i hi (8+j) (by omega) (by
        simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add, ← BitVec.add_assoc,
          BitVec.reduceAdd] using he)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 56 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd864 (by decide))
  advance_finish [lastEffect]

def setupBytes : List UInt8 := [0x48,0x89,0xe6,0xba,0x1,0x0,0x0,0x0,0x48,0x89,0xdf]

def setupEffect (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p + 11
    writes := [⟨(.reg 6 : Operand 64), rspOf s⟩,
      ⟨(.reg 2 : Operand 64), 1⟩,
      ⟨(.reg 7 : Operand 64), s.regValue .rbx⟩] }

theorem setup [Bindings] (p : BitVec 64) (boundary : ReturnBoundary)
    (next : ∀ i : Nat, i ≤ 11 → p + BitVec.ofNat 64 i ≠ boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = p) (codeRange p setupBytes)
      (Effect.post (setupEffect p)) := by
  advance_begin (mov_r64_r64_effect_step p 0x48 0xe6 (by simp [RexWPrefix]) rfl)
  case next => exact fun _ _ => next 3 (by decide)
  advance_then (mov_r32_imm32_effect_step (p+3) 0xba (by decide) 1)
  try (case sub => exact codeRange_slice_subset p setupBytes 3 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · x86_norm
      exact next 8 (by decide)
  advance_then (mov_r64_r64_effect_step (p+8) 0x48 0xdf (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset p setupBytes 8 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Avoids.of_noMem ?_ _, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · simp [Component.Covers]
    · x86_norm
      exact next 11 (by decide)
  advance_finish [setupEffect]

end P256.Proofs.Verifying.Message.Hash.Finalize.Compress.Blocks.Machine
