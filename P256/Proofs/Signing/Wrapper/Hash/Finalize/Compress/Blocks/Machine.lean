import P256.Proofs.Signing.Wrapper.Hash.Finalize.Compress.Blocks.CopyWords
import P256.Proofs.Common.EffectCompose.Advance
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash.Finalize.Compress.Blocks.Machine

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program

structure FirstPre (s : RamState) : Prop where
  rip : s.RIP = 0x10289f
  readable : MemReadable s (rspOf s + 120) 8
  writable : MemWritable s (rspOf s + 56) 8
  apart : RangeApart (rspOf s + 56) 8 0x10289f 10

def firstBytes : List UInt8 := [0x48,0x8b,0x44,0x24,0x78,0x48,0x89,0x44,0x24,0x38]

def firstEffect (s : RamState) : Effect :=
  { rip := 0x1028a9
    writes := [⟨(.reg 0 : Operand 64), memLoad s.external (rspOf s + 120) 64⟩,
      ⟨(.mem (rspOf s + 56) : Operand 64), memLoad s.external (rspOf s + 120) 64⟩] }

theorem first_head [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary FirstPre (codeRange 0x10289f firstBytes) (Effect.post firstEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x10289f 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 120)) (by decide) rfl rfl)
  case pre => intro s h; exact ⟨h.rip, h.readable⟩
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0x28a4 (by decide))
  advance_then (mov_m64_r64_effect_step 0x1028a4 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 56)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10289f firstBytes 5 5
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
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x28a9 (by decide))
  advance_finish [firstEffect]

structure LastPre (s : RamState) : Prop where
  rip : s.RIP = 0x10294a
  writable : ∀ i ∈ ([120,56] : List (BitVec 64)), MemWritable s (rspOf s + i) 8
  apart : ∀ i ∈ ([120,56] : List (BitVec 64)), RangeApart (rspOf s + i) 8 0x10294a 10

def lastBytes : List UInt8 := [0x48,0x89,0x5c,0x24,0x78,0x48,0x89,0x5c,0x24,0x38]

def lastEffect (s : RamState) : Effect :=
  { rip := 0x102954
    writes := [⟨(.mem (rspOf s + 120) : Operand 64), s.regValue .rbx⟩,
      ⟨(.mem (rspOf s + 56) : Operand 64), s.regValue .rbx⟩] }

theorem last_head [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary LastPre (codeRange 0x10294a lastBytes) (Effect.post lastEffect) := by
  advance_begin (mov_m64_r64_effect_step 0x10294a 0x48 (by simp [RexWPrefix]) 3
    (.sib 4 none 0 (.d8 120)) (by decide) rfl rfl)
  case pre =>
    intro s h
    refine ⟨h.rip, h.writable 120 (by simp), ?_⟩
    intro i hi j hj he
    change j < 5 at hj
    exact h.apart 120 (by simp) i hi j (by omega) he
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm
    exact h.apart 120 (by simp)
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0x294f (by decide))
  advance_then (mov_m64_r64_effect_step 0x10294f 0x48 (by simp [RexWPrefix]) 3
    (.sib 4 none 0 (.d8 56)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10294a lastBytes 5 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 56 (by simp)
    · x86_norm
      intro i hi j hj he
      exact hP.apart 56 (by simp) i hi (5+j) (by omega) (by
        simpa only [rspOf, Operand.read, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add, ← BitVec.add_assoc,
          BitVec.reduceAdd] using he)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 56 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2954 (by decide))
  advance_finish [lastEffect]

def setupBytes : List UInt8 := [0x48,0x89,0xe6,0xba,0x1,0x0,0x0,0x0,0x4c,0x89,0xff]

def setupEffect (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p + 11
    writes := [⟨(.reg 6 : Operand 64), rspOf s⟩,
      ⟨(.reg 2 : Operand 64), 1⟩,
      ⟨(.reg 7 : Operand 64), s.regValue .r15⟩] }

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
  advance_then (mov_r64_r64_effect_step (p+8) 0x4c 0xff (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset p setupBytes 8 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Avoids.of_noMem ?_ _, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · simp [Component.Covers]
    · x86_norm
      exact next 11 (by decide)
  advance_finish [setupEffect]

end P256.Proofs.Signing.Wrapper.Hash.Finalize.Compress.Blocks.Machine
