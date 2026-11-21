import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Instructions.CrossPageStore
import P256.Proofs.Program.Code
import X86Proofs.Instructions.MovLoad.Triple
import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Output

open P256.Spec P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions.CrossPageStore (Writable)

private theorem outputY_write_reg_external (s : RamState) (r : BitVec 5) (v : BitVec 64) :
    ((Operand.reg r : Operand 64).write s v).external = s.external := rfl

private theorem outputY_write_mem_external (s : RamState) (a : BitVec 64) (v : BitVec 64) :
    ((Operand.mem a : Operand 64).write s v).external = memStore s.external a v := rfl

structure OutputYPre (s : RamState) : Prop where
  rip : s.RIP = 0x110cc7
  readable : ∀ off ∈ ([128, 136, 144, 152] : List Nat),
    MemReadable s ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 off) 8
  writable : ∀ off ∈ ([32, 40, 48, 56] : List Nat),
    Writable s ((Operand.reg 3 : Operand 64).read s + BitVec.ofNat 64 off) 8
  codeApart : ∀ off ∈ ([32, 40, 48, 56] : List Nat),
    ∀ pc len : Nat, pc + len ≤ 118431 →
      RangeApart ((Operand.reg 3 : Operand 64).read s + BitVec.ofNat 64 off) 8
        (P256.Spec.Program.Extracted.textAddress + BitVec.ofNat 64 pc) len
  sourceApart : ∀ i ∈ ([32, 40, 48, 56] : List Nat),
    ∀ j ∈ ([128, 136, 144, 152] : List Nat),
    RangeApart ((Operand.reg 3 : Operand 64).read s + BitVec.ofNat 64 i) 8
      ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 j) 8

def outputYBytes : List UInt8 := [0x48, 0x8b, 0x84, 0x24, 0x98, 0x0, 0x0, 0x0, 0x48, 0x89, 0x43, 0x38, 0x48, 0x8b, 0x84, 0x24, 0x90, 0x0, 0x0, 0x0, 0x48, 0x89, 0x43, 0x30, 0x48, 0x8b, 0x84, 0x24, 0x88, 0x0, 0x0, 0x0, 0x48, 0x89, 0x43, 0x28, 0x48, 0x8b, 0x84, 0x24, 0x80, 0x0, 0x0, 0x0, 0x48, 0x89, 0x43, 0x20]

def outputYEffect (s : RamState) : Effect :=
  { rip := 0x110cf7
    writes := [⟨(.mem ((Operand.reg 3 : Operand 64).read s + 32) : Operand 64), memLoad s.external ((Operand.reg 4 : Operand 64).read s + 128) 64⟩,
      ⟨(.mem ((Operand.reg 3 : Operand 64).read s + 40) : Operand 64), memLoad s.external ((Operand.reg 4 : Operand 64).read s + 136) 64⟩,
      ⟨(.mem ((Operand.reg 3 : Operand 64).read s + 48) : Operand 64), memLoad s.external ((Operand.reg 4 : Operand 64).read s + 144) 64⟩,
      ⟨(.mem ((Operand.reg 3 : Operand 64).read s + 56) : Operand 64), memLoad s.external ((Operand.reg 4 : Operand 64).read s + 152) 64⟩,
      ⟨(.reg 0 : Operand 64), memLoad s.external ((Operand.reg 4 : Operand 64).read s + 128) 64⟩] }

set_option maxHeartbeats 800000 in
theorem output_y [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary OutputYPre (codeRange 0x110cc7 outputYBytes)
      (Effect.post outputYEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x110cc7 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 152)) (by decide) rfl rfl)
  case pre =>
    intro s h
    refine ⟨h.rip, ?_⟩
    x86_norm
    exact h.readable 152 (by simp)
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0x10ccf (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x110ccf 0x48 (by simp [RexWPrefix])
    0 (.base 3 (.d8 56)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110cc7 outputYBytes 8 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 56 (by simp)
    · x86_norm
      exact hP.codeApart 56 (by simp) 0x10ccf 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 56 (by simp) 0x10cc7 48 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10cd3 (by decide))
  advance_then (mov_r64_m64_effect_step 0x110cd3 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 144)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110cc7 outputYBytes 12 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 144 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10cdb (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x110cdb 0x48 (by simp [RexWPrefix])
    0 (.base 3 (.d8 48)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110cc7 outputYBytes 20 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 48 (by simp)
    · x86_norm
      exact hP.codeApart 48 (by simp) 0x10cdb 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 48 (by simp) 0x10cc7 48 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10cdf (by decide))
  advance_then (mov_r64_m64_effect_step 0x110cdf 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 136)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110cc7 outputYBytes 24 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 136 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10ce7 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x110ce7 0x48 (by simp [RexWPrefix])
    0 (.base 3 (.d8 40)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110cc7 outputYBytes 32 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 40 (by simp)
    · x86_norm
      exact hP.codeApart 40 (by simp) 0x10ce7 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 40 (by simp) 0x10cc7 48 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10ceb (by decide))
  advance_then (mov_r64_m64_effect_step 0x110ceb 0x48 (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 128)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110cc7 outputYBytes 36 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 128 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10cf3 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x110cf3 0x48 (by simp [RexWPrefix])
    0 (.base 3 (.d8 32)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110cc7 outputYBytes 44 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 32 (by simp)
    · x86_norm
      exact hP.codeApart 32 (by simp) 0x10cf3 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 32 (by simp) 0x10cc7 48 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10cf7 (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  have hread (mem : Ram) (i j : Nat) (v : BitVec 64)
      (hi : i ∈ ([32, 40, 48, 56] : List Nat))
      (hj : j ∈ ([128, 136, 144, 152] : List Nat)) :
      memLoad (memStore mem ((Operand.reg 3 : Operand 64).read s + BitVec.ofNat 64 i) v)
        ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 j) 64 =
      memLoad mem ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 j) 64 :=
    P256.Proofs.Common.Field.Montgomery.Schoolbook.memLoad_memStore_rangeApart
      _ _ _ _ 64 (hP.sourceApart i hi j hj)
  have h56_144 := fun mem v => hread mem 56 144 v (by decide) (by decide)
  have h56_136 := fun mem v => hread mem 56 136 v (by decide) (by decide)
  have h56_128 := fun mem v => hread mem 56 128 v (by decide) (by decide)
  have h48_136 := fun mem v => hread mem 48 136 v (by decide) (by decide)
  have h48_128 := fun mem v => hread mem 48 128 v (by decide) (by decide)
  have h40_128 := fun mem v => hread mem 40 128 v (by decide) (by decide)
  simp only [BitVec.ofNat_eq_ofNat] at h56_144 h56_136 h56_128 h48_136 h48_128 h40_128
  apply hH.weaken
  · x86_norm [outputYEffect]
  · x86_norm [outputYEffect,
      h56_144, h56_136, h56_128, h48_136, h48_128, h40_128,
      outputY_write_reg_external, outputY_write_mem_external]
    all_goals (repeat constructor <;> rfl)
  · intro i; cases i <;> x86_norm [outputYEffect]
  · x86_norm [outputYEffect]
    repeat constructor <;> rfl

end P256.Proofs.Sec1.Affine.Uncompressed.Output
