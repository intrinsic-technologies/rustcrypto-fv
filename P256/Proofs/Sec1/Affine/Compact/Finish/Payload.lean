import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.Instructions.CrossPageStore
import P256.Proofs.Program.Code
import X86Proofs.Instructions.MovLoad.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Field.Montgomery.Schoolbook (memLoad_memStore_rangeApart)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Sec1.Affine.Compact.Finish.Payload

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

private theorem operand_write_reg_external (s : RamState) (r : BitVec 5) (v : BitVec 64) :
    ((Operand.reg r : Operand 64).write s v).external = s.external := rfl

private theorem operand_write_mem_external (s : RamState) (a : BitVec 64) (v : BitVec 64) :
    ((Operand.mem a : Operand 64).write s v).external = memStore s.external a v := rfl

structure CopyPre (s : RamState) : Prop where
  rip : s.RIP = 0x1105b7
  readable : ∀ i ∈ ([96,104,112,120,128,136,144,152] : List (BitVec 64)),
    MemReadable s ((Operand.reg 4 : Operand 64).read s + i) 8
  writable : ∀ i ∈ ([0,8,16,24,32,40,48,56] : List (BitVec 64)),
    P256.Proofs.Common.Instructions.CrossPageStore.Writable s ((Operand.reg 3 : Operand 64).read s + i) 8
  codeApart : ∀ i ∈ ([0,8,16,24,32,40,48,56] : List (BitVec 64)), ∀ offset len : Nat,
    offset + len ≤ 118431 → RangeApart ((Operand.reg 3 : Operand 64).read s + i) 8
      (Extracted.textAddress + BitVec.ofNat 64 offset) len
  sourceApart : ∀ i ∈ ([0,8,16,24,32,40,48,56] : List (BitVec 64)),
    ∀ j ∈ ([96,104,112,120,128,136,144,152] : List (BitVec 64)),
    RangeApart ((Operand.reg 3 : Operand 64).read s + i) 8
      ((Operand.reg 4 : Operand 64).read s + j) 8

def copyBytes : List UInt8 := [0x48,0x8b,0x8c,0x24,0x98,0x0,0x0,0x0,0x48,0x89,0x4b,0x38,0x48,0x8b,0x8c,0x24,0x90,0x0,0x0,0x0,0x48,0x89,0x4b,0x30,0x48,0x8b,0x8c,0x24,0x88,0x0,0x0,0x0,0x48,0x89,0x4b,0x28,0x48,0x8b,0x8c,0x24,0x80,0x0,0x0,0x0,0x48,0x89,0x4b,0x20,0x48,0x8b,0x4c,0x24,0x78,0x48,0x89,0x4b,0x18,0x48,0x8b,0x4c,0x24,0x70,0x48,0x89,0x4b,0x10,0x48,0x8b,0x4c,0x24,0x60,0x48,0x8b,0x54,0x24,0x68,0x48,0x89,0x53,0x8,0x48,0x89,0xb]

def copyEffect (s : RamState) : Effect :=
  { rip := 0x11060a
    writes := [
      ⟨(.reg 1 : Operand 64), (.mem ((Operand.reg 4 : Operand 64).read s + 96) : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (.mem ((Operand.reg 4 : Operand 64).read s + 104) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 3 : Operand 64).read s + 0) : Operand 64),
        (.mem ((Operand.reg 4 : Operand 64).read s + 96) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 3 : Operand 64).read s + 8) : Operand 64),
        (.mem ((Operand.reg 4 : Operand 64).read s + 104) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 3 : Operand 64).read s + 16) : Operand 64),
        (.mem ((Operand.reg 4 : Operand 64).read s + 112) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 3 : Operand 64).read s + 24) : Operand 64),
        (.mem ((Operand.reg 4 : Operand 64).read s + 120) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 3 : Operand 64).read s + 32) : Operand 64),
        (.mem ((Operand.reg 4 : Operand 64).read s + 128) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 3 : Operand 64).read s + 40) : Operand 64),
        (.mem ((Operand.reg 4 : Operand 64).read s + 136) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 3 : Operand 64).read s + 48) : Operand 64),
        (.mem ((Operand.reg 4 : Operand 64).read s + 144) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 3 : Operand 64).read s + 56) : Operand 64),
        (.mem ((Operand.reg 4 : Operand 64).read s + 152) : Operand 64).read s⟩
    ] }

set_option maxHeartbeats 3200000 in
theorem copy [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary CopyPre (codeRange 0x1105b7 copyBytes)
      (Effect.post copyEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x1105b7 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d32 152)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.readable 152 (by simp)⟩
  case next =>
    intro s hP
    exact boundary_ne_program hout (inProgram_of_textOffset 0x105bf (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1105bf 0x48 (by simp [RexWPrefix]) 1
    (.base 3 (.d8 56)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1105b7 copyBytes 8 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 56 (by simp)
    · x86_norm
      exact hP.codeApart 56 (by simp) 0x105bf 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 56 (by simp) 0x105b7 83 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x105c3 (by decide))
  advance_then (mov_r64_m64_effect_step 0x1105c3 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d32 144)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1105b7 copyBytes 12 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 144 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x105cb (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1105cb 0x48 (by simp [RexWPrefix]) 1
    (.base 3 (.d8 48)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1105b7 copyBytes 20 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 48 (by simp)
    · x86_norm
      exact hP.codeApart 48 (by simp) 0x105cb 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 48 (by simp) 0x105b7 83 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x105cf (by decide))
  advance_then (mov_r64_m64_effect_step 0x1105cf 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d32 136)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1105b7 copyBytes 24 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 136 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x105d7 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1105d7 0x48 (by simp [RexWPrefix]) 1
    (.base 3 (.d8 40)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1105b7 copyBytes 32 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 40 (by simp)
    · x86_norm
      exact hP.codeApart 40 (by simp) 0x105d7 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 40 (by simp) 0x105b7 83 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x105db (by decide))
  advance_then (mov_r64_m64_effect_step 0x1105db 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d32 128)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1105b7 copyBytes 36 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 128 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x105e3 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1105e3 0x48 (by simp [RexWPrefix]) 1
    (.base 3 (.d8 32)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1105b7 copyBytes 44 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 32 (by simp)
    · x86_norm
      exact hP.codeApart 32 (by simp) 0x105e3 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 32 (by simp) 0x105b7 83 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x105e7 (by decide))
  advance_then (mov_r64_m64_effect_step 0x1105e7 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d8 120)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1105b7 copyBytes 48 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 120 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x105ec (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1105ec 0x48 (by simp [RexWPrefix]) 1
    (.base 3 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1105b7 copyBytes 53 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 24 (by simp)
    · x86_norm
      exact hP.codeApart 24 (by simp) 0x105ec 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 24 (by simp) 0x105b7 83 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x105f0 (by decide))
  advance_then (mov_r64_m64_effect_step 0x1105f0 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d8 112)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1105b7 copyBytes 57 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 112 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x105f5 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1105f5 0x48 (by simp [RexWPrefix]) 1
    (.base 3 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1105b7 copyBytes 62 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 16 (by simp)
    · x86_norm
      exact hP.codeApart 16 (by simp) 0x105f5 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 16 (by simp) 0x105b7 83 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x105f9 (by decide))
  advance_then (mov_r64_m64_effect_step 0x1105f9 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d8 96)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1105b7 copyBytes 66 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 96 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x105fe (by decide))
  advance_then (mov_r64_m64_effect_step 0x1105fe 0x48 (by simp [RexWPrefix]) 2
    (.sib 4 none 0 (.d8 104)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1105b7 copyBytes 71 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 104 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x10603 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x110603 0x48 (by simp [RexWPrefix]) 2
    (.base 3 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1105b7 copyBytes 76 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 8 (by simp)
    · x86_norm
      exact hP.codeApart 8 (by simp) 0x10603 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 8 (by simp) 0x105b7 83 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x10607 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x110607 0x48 (by simp [RexWPrefix]) 1
    (.base 3 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1105b7 copyBytes 80 3
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 0 (by simp)
    · x86_norm
      exact hP.codeApart 0 (by simp) 0x10607 3 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 0 (by simp) 0x105b7 83 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1060a (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  have hread (mem : Ram) (i j : BitVec 64) (v : BitVec 64)
      (hi : i ∈ ([0,8,16,24,32,40,48,56] : List (BitVec 64)))
      (hj : j ∈ ([96,104,112,120,128,136,144,152] : List (BitVec 64))) :
      memLoad (memStore mem ((Operand.reg 3 : Operand 64).read s + i) v)
        ((Operand.reg 4 : Operand 64).read s + j) 64 =
      memLoad mem ((Operand.reg 4 : Operand 64).read s + j) 64 :=
    memLoad_memStore_rangeApart _ _ _ _ 64 (hP.sourceApart i hi j hj)
  have h64_328 := fun mem v => hread mem 56 144 v (by decide) (by decide)
  have h64_320 := fun mem v => hread mem 56 136 v (by decide) (by decide)
  have h56_320 := fun mem v => hread mem 48 136 v (by decide) (by decide)
  have h64_312 := fun mem v => hread mem 56 128 v (by decide) (by decide)
  have h56_312 := fun mem v => hread mem 48 128 v (by decide) (by decide)
  have h48_312 := fun mem v => hread mem 40 128 v (by decide) (by decide)
  have h64_304 := fun mem v => hread mem 56 120 v (by decide) (by decide)
  have h56_304 := fun mem v => hread mem 48 120 v (by decide) (by decide)
  have h48_304 := fun mem v => hread mem 40 120 v (by decide) (by decide)
  have h40_304 := fun mem v => hread mem 32 120 v (by decide) (by decide)
  have h64_296 := fun mem v => hread mem 56 112 v (by decide) (by decide)
  have h56_296 := fun mem v => hread mem 48 112 v (by decide) (by decide)
  have h48_296 := fun mem v => hread mem 40 112 v (by decide) (by decide)
  have h40_296 := fun mem v => hread mem 32 112 v (by decide) (by decide)
  have h32_296 := fun mem v => hread mem 24 112 v (by decide) (by decide)
  have h64_280 := fun mem v => hread mem 56 96 v (by decide) (by decide)
  have h56_280 := fun mem v => hread mem 48 96 v (by decide) (by decide)
  have h48_280 := fun mem v => hread mem 40 96 v (by decide) (by decide)
  have h40_280 := fun mem v => hread mem 32 96 v (by decide) (by decide)
  have h32_280 := fun mem v => hread mem 24 96 v (by decide) (by decide)
  have h24_280 := fun mem v => hread mem 16 96 v (by decide) (by decide)
  have h64_288 := fun mem v => hread mem 56 104 v (by decide) (by decide)
  have h56_288 := fun mem v => hread mem 48 104 v (by decide) (by decide)
  have h48_288 := fun mem v => hread mem 40 104 v (by decide) (by decide)
  have h40_288 := fun mem v => hread mem 32 104 v (by decide) (by decide)
  have h32_288 := fun mem v => hread mem 24 104 v (by decide) (by decide)
  have h24_288 := fun mem v => hread mem 16 104 v (by decide) (by decide)
  simp only [BitVec.ofNat_eq_ofNat] at h64_328 h64_320 h56_320 h64_312 h56_312 h48_312 h64_304 h56_304 h48_304 h40_304 h64_296 h56_296 h48_296 h40_296 h32_296 h64_280 h56_280 h48_280 h40_280 h32_280 h24_280 h64_288 h56_288 h48_288 h40_288 h32_288 h24_288
  apply hH.weaken
  · x86_norm [copyEffect]
  · x86_norm [copyEffect, operand_write_reg_external, operand_write_mem_external, h64_328, h64_320, h56_320, h64_312, h56_312, h48_312, h64_304, h56_304, h48_304, h40_304, h64_296, h56_296, h48_296, h40_296, h32_296, h64_280, h56_280, h48_280, h40_280, h32_280, h24_280, h64_288, h56_288, h48_288, h40_288, h32_288, h24_288]
    all_goals (repeat constructor <;> rfl)
  · intro i; cases i <;> x86_norm [copyEffect]
  · x86_norm [copyEffect]

end P256.Proofs.Sec1.Affine.Compact.Finish.Payload
