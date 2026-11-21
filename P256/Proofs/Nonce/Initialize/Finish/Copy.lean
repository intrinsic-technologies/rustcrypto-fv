import P256.Proofs.Nonce.Initialize.State
import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose
import P256.Proofs.Common.Instructions.CrossPageStore.Range
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovLoad.Triple
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.Code

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Field.Montgomery.Schoolbook (memLoad_memStore_rangeApart)

def outputPointer (s : RamState) : BitVec 64 :=
  (Operand.reg 14 : Operand 64).read s

structure CopyPre (s : RamState) : Prop where
  rip : s.RIP = 0x107c1a
  readable : ∀ i ∈ ([8, 16, 24, 32, 40, 48, 56, 64] : List (BitVec 64)),
    MemReadable s ((Operand.reg 4 : Operand 64).read s + i) 8
  writable : ∀ i ∈ ([0, 8, 16, 24, 32, 40, 48, 56, 64] : List (BitVec 64)),
    P256.Proofs.Common.Instructions.CrossPageStore.Writable s (outputPointer s + i) 8
  codeApart : ∀ i ∈ ([0, 8, 16, 24, 32, 40, 48, 56, 64] : List (BitVec 64)),
    ∀ offset len : Nat, offset + len ≤ 118431 →
    RangeApart (outputPointer s + i) 8 (Extracted.textAddress + BitVec.ofNat 64 offset) len
  sourceApart : ∀ i ∈ ([0, 8, 16, 24, 32, 40, 48, 56, 64] : List (BitVec 64)),
    ∀ j ∈ ([8, 16, 24, 32, 40, 48, 56, 64] : List (BitVec 64)),
    RangeApart (outputPointer s + i) 8 ((Operand.reg 4 : Operand 64).read s + j) 8

def copyBytes : List UInt8 :=
  [0x48, 0x8b, 0x44, 0x24, 0x40, 0x49, 0x89, 0x46, 0x40, 0x48, 0x8b, 0x44, 0x24, 0x38, 0x49, 0x89, 0x46, 0x38, 0x48, 0x8b, 0x44, 0x24, 0x30, 0x49, 0x89, 0x46, 0x30, 0x48, 0x8b, 0x44, 0x24, 0x28, 0x49, 0x89, 0x46, 0x28, 0x48, 0x8b, 0x44, 0x24, 0x20, 0x49, 0x89, 0x46, 0x20, 0x48, 0x8b, 0x44, 0x24, 0x18, 0x49, 0x89, 0x46, 0x18, 0x48, 0x8b, 0x44, 0x24, 0x8, 0x48, 0x8b, 0x4c, 0x24, 0x10, 0x49, 0x89, 0x4e, 0x10, 0x49, 0x89, 0x46, 0x8, 0x4d, 0x89, 0x3e, 0x4c, 0x89, 0xf0]

def copyEffect (s : RamState) : Effect :=
  { rip := 0x107c68
    writes := [
      ⟨(.reg 0 : Operand 64), outputPointer s⟩,
      ⟨(.reg 1 : Operand 64), memLoad s.external ((Operand.reg 4 : Operand 64).read s + 16) 64⟩,
      ⟨(.mem (outputPointer s + 0) : Operand 64), (Operand.reg 15 : Operand 64).read s⟩,
      ⟨(.mem (outputPointer s + 8) : Operand 64), memLoad s.external ((Operand.reg 4 : Operand 64).read s + 8) 64⟩,
      ⟨(.mem (outputPointer s + 16) : Operand 64), memLoad s.external ((Operand.reg 4 : Operand 64).read s + 16) 64⟩,
      ⟨(.mem (outputPointer s + 24) : Operand 64), memLoad s.external ((Operand.reg 4 : Operand 64).read s + 24) 64⟩,
      ⟨(.mem (outputPointer s + 32) : Operand 64), memLoad s.external ((Operand.reg 4 : Operand 64).read s + 32) 64⟩,
      ⟨(.mem (outputPointer s + 40) : Operand 64), memLoad s.external ((Operand.reg 4 : Operand 64).read s + 40) 64⟩,
      ⟨(.mem (outputPointer s + 48) : Operand 64), memLoad s.external ((Operand.reg 4 : Operand 64).read s + 48) 64⟩,
      ⟨(.mem (outputPointer s + 56) : Operand 64), memLoad s.external ((Operand.reg 4 : Operand 64).read s + 56) 64⟩,
      ⟨(.mem (outputPointer s + 64) : Operand 64), memLoad s.external ((Operand.reg 4 : Operand 64).read s + 64) 64⟩] }

set_option maxHeartbeats 2000000 in
theorem copy_run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary CopyPre (codeRange 0x107c1a copyBytes)
      (Effect.post copyEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x107c1a 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 64)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.readable 64 (by simp)⟩
  case next => intro s hP; exact boundary_ne_program outside (inProgram_of_textOffset 0x7c1f (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x107c1f 0x49 (by simp [RexWPrefix]) 0
    (.base 14 (.d8 64)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107c1a copyBytes 5 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 64 (by simp)
    · x86_norm
      exact hP.codeApart 64 (by simp) 0x7c1f 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 64 (by simp) 0x7c1a 78 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x7c23 (by decide))
  advance_then (mov_r64_m64_effect_step 0x107c23 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 56)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107c1a copyBytes 9 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 56 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x7c28 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x107c28 0x49 (by simp [RexWPrefix]) 0
    (.base 14 (.d8 56)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107c1a copyBytes 14 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 56 (by simp)
    · x86_norm
      exact hP.codeApart 56 (by simp) 0x7c28 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 56 (by simp) 0x7c1a 78 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x7c2c (by decide))
  advance_then (mov_r64_m64_effect_step 0x107c2c 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 48)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107c1a copyBytes 18 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 48 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x7c31 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x107c31 0x49 (by simp [RexWPrefix]) 0
    (.base 14 (.d8 48)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107c1a copyBytes 23 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 48 (by simp)
    · x86_norm
      exact hP.codeApart 48 (by simp) 0x7c31 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 48 (by simp) 0x7c1a 78 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x7c35 (by decide))
  advance_then (mov_r64_m64_effect_step 0x107c35 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107c1a copyBytes 27 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 40 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x7c3a (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x107c3a 0x49 (by simp [RexWPrefix]) 0
    (.base 14 (.d8 40)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107c1a copyBytes 32 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 40 (by simp)
    · x86_norm
      exact hP.codeApart 40 (by simp) 0x7c3a 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 40 (by simp) 0x7c1a 78 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x7c3e (by decide))
  advance_then (mov_r64_m64_effect_step 0x107c3e 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107c1a copyBytes 36 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 32 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x7c43 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x107c43 0x49 (by simp [RexWPrefix]) 0
    (.base 14 (.d8 32)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107c1a copyBytes 41 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 32 (by simp)
    · x86_norm
      exact hP.codeApart 32 (by simp) 0x7c43 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 32 (by simp) 0x7c1a 78 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x7c47 (by decide))
  advance_then (mov_r64_m64_effect_step 0x107c47 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107c1a copyBytes 45 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 24 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x7c4c (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x107c4c 0x49 (by simp [RexWPrefix]) 0
    (.base 14 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107c1a copyBytes 50 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 24 (by simp)
    · x86_norm
      exact hP.codeApart 24 (by simp) 0x7c4c 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 24 (by simp) 0x7c1a 78 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x7c50 (by decide))
  advance_then (mov_r64_m64_effect_step 0x107c50 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107c1a copyBytes 54 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 8 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x7c55 (by decide))
  advance_then (mov_r64_m64_effect_step 0x107c55 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107c1a copyBytes 59 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 16 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x7c5a (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x107c5a 0x49 (by simp [RexWPrefix]) 1
    (.base 14 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107c1a copyBytes 64 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 16 (by simp)
    · x86_norm
      exact hP.codeApart 16 (by simp) 0x7c5a 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 16 (by simp) 0x7c1a 78 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x7c5e (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x107c5e 0x49 (by simp [RexWPrefix]) 0
    (.base 14 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107c1a copyBytes 68 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 8 (by simp)
    · x86_norm
      exact hP.codeApart 8 (by simp) 0x7c5e 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 8 (by simp) 0x7c1a 78 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x7c62 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x107c62 0x4d (by simp [RexWPrefix]) 15
    (.base 14 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107c1a copyBytes 72 3
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 0 (by simp)
    · x86_norm
      exact hP.codeApart 0 (by simp) 0x7c62 3 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 0 (by simp) 0x7c1a 78 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x7c65 (by decide))
  advance_then (mov_r64_r64_effect_step 0x107c65 0x4c 0xf0 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x107c1a copyBytes 75 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x7c68 (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  have hread (mem : Ram) (i j : BitVec 64) (v : BitVec 64)
      (hi : i ∈ ([0, 8, 16, 24, 32, 40, 48, 56, 64] : List (BitVec 64)))
      (hj : j ∈ ([8, 16, 24, 32, 40, 48, 56, 64] : List (BitVec 64))) :
      memLoad (memStore mem (outputPointer s + i) v) ((Operand.reg 4 : Operand 64).read s + j) 64 =
        memLoad mem ((Operand.reg 4 : Operand 64).read s + j) 64 :=
    memLoad_memStore_rangeApart _ _ _ _ _ (hP.sourceApart i hi j hj)
  have h64_56 := fun mem v => hread mem 64 56 v (by decide) (by decide)
  have h64_48 := fun mem v => hread mem 64 48 v (by decide) (by decide)
  have h64_40 := fun mem v => hread mem 64 40 v (by decide) (by decide)
  have h64_32 := fun mem v => hread mem 64 32 v (by decide) (by decide)
  have h64_24 := fun mem v => hread mem 64 24 v (by decide) (by decide)
  have h64_16 := fun mem v => hread mem 64 16 v (by decide) (by decide)
  have h64_8 := fun mem v => hread mem 64 8 v (by decide) (by decide)
  have h56_48 := fun mem v => hread mem 56 48 v (by decide) (by decide)
  have h56_40 := fun mem v => hread mem 56 40 v (by decide) (by decide)
  have h56_32 := fun mem v => hread mem 56 32 v (by decide) (by decide)
  have h56_24 := fun mem v => hread mem 56 24 v (by decide) (by decide)
  have h56_16 := fun mem v => hread mem 56 16 v (by decide) (by decide)
  have h56_8 := fun mem v => hread mem 56 8 v (by decide) (by decide)
  have h48_40 := fun mem v => hread mem 48 40 v (by decide) (by decide)
  have h48_32 := fun mem v => hread mem 48 32 v (by decide) (by decide)
  have h48_24 := fun mem v => hread mem 48 24 v (by decide) (by decide)
  have h48_16 := fun mem v => hread mem 48 16 v (by decide) (by decide)
  have h48_8 := fun mem v => hread mem 48 8 v (by decide) (by decide)
  have h40_32 := fun mem v => hread mem 40 32 v (by decide) (by decide)
  have h40_24 := fun mem v => hread mem 40 24 v (by decide) (by decide)
  have h40_16 := fun mem v => hread mem 40 16 v (by decide) (by decide)
  have h40_8 := fun mem v => hread mem 40 8 v (by decide) (by decide)
  have h32_24 := fun mem v => hread mem 32 24 v (by decide) (by decide)
  have h32_16 := fun mem v => hread mem 32 16 v (by decide) (by decide)
  have h32_8 := fun mem v => hread mem 32 8 v (by decide) (by decide)
  have h24_16 := fun mem v => hread mem 24 16 v (by decide) (by decide)
  have h24_8 := fun mem v => hread mem 24 8 v (by decide) (by decide)
  simp only [outputPointer, BitVec.ofNat_eq_ofNat] at h64_56 h64_48 h64_40 h64_32 h64_24 h64_16 h64_8 h56_48 h56_40 h56_32 h56_24 h56_16 h56_8 h48_40 h48_32 h48_24 h48_16 h48_8 h40_32 h40_24 h40_16 h40_8 h32_24 h32_16 h32_8 h24_16 h24_8
  apply hH.weaken
  · x86_norm [copyEffect, outputPointer]
  · x86_norm [copyEffect, outputPointer, h64_56, h64_48, h64_40, h64_32, h64_24, h64_16, h64_8, h56_48, h56_40, h56_32, h56_24, h56_16, h56_8, h48_40, h48_32, h48_24, h48_16, h48_8, h40_32, h40_24, h40_16, h40_8, h32_24, h32_16, h32_8, h24_16, h24_8]
    all_goals (repeat constructor <;> rfl)
  · intro i; cases i <;> x86_norm [copyEffect]
  · x86_norm [copyEffect, outputPointer]

end P256.Proofs.Nonce.Initialize.Finish
