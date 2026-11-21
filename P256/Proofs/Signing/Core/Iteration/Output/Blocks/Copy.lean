import P256.Proofs.Signing.Core.Iteration.Memory
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Instructions.CrossPageStore
import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose
import X86Proofs.Instructions.MovLoad.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Output.Blocks.Copy

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Program Common.Field
open Common.Field.Montgomery.Schoolbook

def destination (s : RamState) : BitVec 64 := (Operand.mem ((Operand.reg 4 : Operand 64).read s+72) : Operand 64).read s

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10d377
  readable : ∀ off ∈ ([72,552,560,568,576,584,592] : List Nat),
    MemReadable s ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 off) 8
  writable : ∀ off ∈ ([16,24,32,40,48,56] : List Nat),
    Common.Instructions.CrossPageStore.Writable s (destination s + BitVec.ofNat 64 off) 8
  apart : RangeApart (destination s) 64 ((Operand.reg 4 : Operand 64).read s) 600
  codeApart : ∀ off ∈ ([16,24,32,40,48,56] : List Nat), ∀ co cl : Nat,
    co+cl ≤ 118431 → RangeApart (destination s + BitVec.ofNat 64 off) 8
      (Extracted.textAddress + BitVec.ofNat 64 co) cl

def bytes : List UInt8 :=
  [72, 139, 132, 36, 80, 2, 0, 0, 76, 139, 124, 36, 72, 73, 137, 71, 56, 72, 139, 132, 36, 72, 2, 0, 0, 73, 137, 71, 48, 72, 139, 132, 36, 64, 2, 0, 0, 73, 137, 71, 40, 72, 139, 132, 36, 56, 2, 0, 0, 73, 137, 71, 32, 72, 139, 132, 36, 40, 2, 0, 0, 72, 139, 140, 36, 48, 2, 0, 0, 73, 137, 79, 24, 73, 137, 71, 16]

def effect (s : RamState) : Effect :=
  { rip := 0x10d3c4
    writes := [⟨(.reg 0 : Operand 64), (Operand.mem ((Operand.reg 4 : Operand 64).read s+552) : Operand 64).read s⟩,
      ⟨(.reg 15 : Operand 64), destination s⟩,
      ⟨(.reg 1 : Operand 64), (Operand.mem ((Operand.reg 4 : Operand 64).read s+560) : Operand 64).read s⟩,
      ⟨(.mem (destination s+56) : Operand 64), (Operand.mem ((Operand.reg 4 : Operand 64).read s+592) : Operand 64).read s⟩,
      ⟨(.mem (destination s+48) : Operand 64), (Operand.mem ((Operand.reg 4 : Operand 64).read s+584) : Operand 64).read s⟩,
      ⟨(.mem (destination s+40) : Operand 64), (Operand.mem ((Operand.reg 4 : Operand 64).read s+576) : Operand 64).read s⟩,
      ⟨(.mem (destination s+32) : Operand 64), (Operand.mem ((Operand.reg 4 : Operand 64).read s+568) : Operand 64).read s⟩,
      ⟨(.mem (destination s+24) : Operand 64), (Operand.mem ((Operand.reg 4 : Operand 64).read s+560) : Operand 64).read s⟩,
      ⟨(.mem (destination s+16) : Operand 64), (Operand.mem ((Operand.reg 4 : Operand 64).read s+552) : Operand 64).read s⟩] }

set_option maxHeartbeats 1200000 in
theorem correct [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10d377 bytes) (Effect.post effect) := by
  advance_begin (mov_r64_m64_effect_step 0x10d377 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 592)) (by decide) rfl rfl)
  case pre => intro s h; exact ⟨h.rip,h.readable 592 (by simp)⟩
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0xd37f (by decide))
  advance_then (mov_r64_m64_effect_step 0x10d37f 0x4c (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 72)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d377 bytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 72 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd384 (by decide))
  advance_then (Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10d384 0x49 (by simp [RexWPrefix]) 0 (.base 15 (.d8 56)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d377 bytes 13 4
  case mid =>
    intro s t hP hH hO
    refine ⟨Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 56 (by simp)
    · x86_norm
      exact hP.codeApart 56 (by simp) 0xd384 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 56 (by simp) 0xd377 77 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd388 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10d388 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 584)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d377 bytes 17 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 584 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd390 (by decide))
  advance_then (Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10d390 0x49 (by simp [RexWPrefix]) 0 (.base 15 (.d8 48)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d377 bytes 25 4
  case mid =>
    intro s t hP hH hO
    refine ⟨Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 48 (by simp)
    · x86_norm
      exact hP.codeApart 48 (by simp) 0xd390 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 48 (by simp) 0xd377 77 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd394 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10d394 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 576)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d377 bytes 29 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 576 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd39c (by decide))
  advance_then (Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10d39c 0x49 (by simp [RexWPrefix]) 0 (.base 15 (.d8 40)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d377 bytes 37 4
  case mid =>
    intro s t hP hH hO
    refine ⟨Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 40 (by simp)
    · x86_norm
      exact hP.codeApart 40 (by simp) 0xd39c 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 40 (by simp) 0xd377 77 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd3a0 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10d3a0 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 568)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d377 bytes 41 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 568 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd3a8 (by decide))
  advance_then (Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10d3a8 0x49 (by simp [RexWPrefix]) 0 (.base 15 (.d8 32)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d377 bytes 49 4
  case mid =>
    intro s t hP hH hO
    refine ⟨Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 32 (by simp)
    · x86_norm
      exact hP.codeApart 32 (by simp) 0xd3a8 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 32 (by simp) 0xd377 77 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd3ac (by decide))
  advance_then (mov_r64_m64_effect_step 0x10d3ac 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 552)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d377 bytes 53 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 552 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd3b4 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10d3b4 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 560)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d377 bytes 61 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 560 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd3bc (by decide))
  advance_then (Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10d3bc 0x49 (by simp [RexWPrefix]) 1 (.base 15 (.d8 24)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d377 bytes 69 4
  case mid =>
    intro s t hP hH hO
    refine ⟨Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 24 (by simp)
    · x86_norm
      exact hP.codeApart 24 (by simp) 0xd3bc 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 24 (by simp) 0xd377 77 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd3c0 (by decide))
  advance_then (Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10d3c0 0x49 (by simp [RexWPrefix]) 0 (.base 15 (.d8 16)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d377 bytes 73 4
  case mid =>
    intro s t hP hH hO
    refine ⟨Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 16 (by simp)
    · x86_norm
      exact hP.codeApart 16 (by simp) 0xd3c0 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 16 (by simp) 0xd377 77 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd3c4 (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  have hread (mem : Ram) (i j : Nat) (v : BitVec 64) (hi : i+8 ≤ 64) (hj : j+8 ≤ 600) :
      memLoad (memStore mem (destination s+BitVec.ofNat 64 i) v)
        ((Operand.reg 4 : Operand 64).read s+BitVec.ofNat 64 j) 64 = memLoad mem ((Operand.reg 4 : Operand 64).read s+BitVec.ofNat 64 j) 64 := by
    apply memLoad_memStore_rangeApart
    intro k hk l hl he
    apply hP.apart (i+k) (by omega) (j+l) (by omega)
    simpa only [BitVec.ofNat_eq_ofNat,BitVec.ofNat_add,BitVec.add_assoc] using he
  have h56_584 := fun mem v => hread mem 56 584 v (by decide) (by decide)
  have h56_576 := fun mem v => hread mem 56 576 v (by decide) (by decide)
  have h56_568 := fun mem v => hread mem 56 568 v (by decide) (by decide)
  have h56_552 := fun mem v => hread mem 56 552 v (by decide) (by decide)
  have h56_560 := fun mem v => hread mem 56 560 v (by decide) (by decide)
  have h48_584 := fun mem v => hread mem 48 584 v (by decide) (by decide)
  have h48_576 := fun mem v => hread mem 48 576 v (by decide) (by decide)
  have h48_568 := fun mem v => hread mem 48 568 v (by decide) (by decide)
  have h48_552 := fun mem v => hread mem 48 552 v (by decide) (by decide)
  have h48_560 := fun mem v => hread mem 48 560 v (by decide) (by decide)
  have h40_584 := fun mem v => hread mem 40 584 v (by decide) (by decide)
  have h40_576 := fun mem v => hread mem 40 576 v (by decide) (by decide)
  have h40_568 := fun mem v => hread mem 40 568 v (by decide) (by decide)
  have h40_552 := fun mem v => hread mem 40 552 v (by decide) (by decide)
  have h40_560 := fun mem v => hread mem 40 560 v (by decide) (by decide)
  have h32_584 := fun mem v => hread mem 32 584 v (by decide) (by decide)
  have h32_576 := fun mem v => hread mem 32 576 v (by decide) (by decide)
  have h32_568 := fun mem v => hread mem 32 568 v (by decide) (by decide)
  have h32_552 := fun mem v => hread mem 32 552 v (by decide) (by decide)
  have h32_560 := fun mem v => hread mem 32 560 v (by decide) (by decide)
  x86_norm [destination] at h56_584 h56_576 h56_568 h56_552 h56_560 h48_584 h48_576 h48_568 h48_552 h48_560 h40_584 h40_576 h40_568 h40_552 h40_560 h32_584 h32_576 h32_568 h32_552 h32_560
  apply hH.weaken
  · x86_norm [effect,destination]
  · x86_norm [effect,destination,BitVec.add_assoc,h56_584, h56_576, h56_568, h56_552, h56_560, h48_584, h48_576, h48_568, h48_552, h48_560, h40_584, h40_576, h40_568, h40_552, h40_560, h32_584, h32_576, h32_568, h32_552, h32_560]
    all_goals (repeat constructor <;> rfl)
  · intro i; cases i <;> x86_norm [effect,destination]
  · x86_norm [effect,destination]

end P256.Proofs.Signing.Core.Iteration.Output.Blocks.Copy
