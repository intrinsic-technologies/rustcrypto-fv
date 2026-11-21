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

namespace P256.Proofs.Sec1.Affine.Compressed.Finish.Payload

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

private theorem operand_write_reg_external (s : RamState) (r : BitVec 5) (v : BitVec 64) :
    ((Operand.reg r : Operand 64).write s v).external = s.external := rfl

private theorem operand_write_mem_external (s : RamState) (a : BitVec 64) (v : BitVec 64) :
    ((Operand.mem a : Operand 64).write s v).external = memStore s.external a v := rfl

structure CopyPre (s : RamState) : Prop where
  rip : s.RIP = 0x11019c
  readable : ∀ i ∈ ([376,384,392,400,408,416,424,432] : List (BitVec 64)),
    MemReadable s ((Operand.reg 4 : Operand 64).read s + i) 8
  writable : ∀ i ∈ ([0,8,16,24,32,40,48,56] : List (BitVec 64)),
    P256.Proofs.Common.Instructions.CrossPageStore.Writable s ((Operand.reg 3 : Operand 64).read s + i) 8
  codeApart : ∀ i ∈ ([0,8,16,24,32,40,48,56] : List (BitVec 64)), ∀ offset len : Nat,
    offset + len ≤ 118431 → RangeApart ((Operand.reg 3 : Operand 64).read s + i) 8
      (Extracted.textAddress + BitVec.ofNat 64 offset) len
  sourceApart : ∀ i ∈ ([0,8,16,24,32,40,48,56] : List (BitVec 64)),
    ∀ j ∈ ([376,384,392,400,408,416,424,432] : List (BitVec 64)),
    RangeApart ((Operand.reg 3 : Operand 64).read s + i) 8
      ((Operand.reg 4 : Operand 64).read s + j) 8

def copyBytes : List UInt8 :=
  [0x48, 0x8b, 0x8c, 0x24, 0xb0, 0x1, 0x0, 0x0, 0x48, 0x89, 0x4b, 0x38, 0x48, 0x8b, 0x8c, 0x24, 0xa8, 0x1, 0x0, 0x0, 0x48, 0x89, 0x4b, 0x30, 0x48, 0x8b, 0x8c, 0x24, 0xa0, 0x1, 0x0, 0x0, 0x48, 0x89, 0x4b, 0x28, 0x48, 0x8b, 0x8c, 0x24, 0x98, 0x1, 0x0, 0x0, 0x48, 0x89, 0x4b, 0x20, 0x48, 0x8b, 0x8c, 0x24, 0x90, 0x1, 0x0, 0x0, 0x48, 0x89, 0x4b, 0x18, 0x48, 0x8b, 0x8c, 0x24, 0x88, 0x1, 0x0, 0x0, 0x48, 0x89, 0x4b, 0x10, 0x48, 0x8b, 0x8c, 0x24, 0x78, 0x1, 0x0, 0x0, 0x48, 0x8b, 0x94, 0x24, 0x80, 0x1, 0x0, 0x0, 0x48, 0x89, 0x53, 0x8, 0x48, 0x89, 0xb]

def copyEffect (s : RamState) : Effect :=
  { rip := 0x1101fb
    writes := [
      ⟨(.reg 1 : Operand 64), (.mem ((Operand.reg 4 : Operand 64).read s + 376) : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (.mem ((Operand.reg 4 : Operand 64).read s + 384) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 3 : Operand 64).read s + 0) : Operand 64),
        (.mem ((Operand.reg 4 : Operand 64).read s + 376) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 3 : Operand 64).read s + 8) : Operand 64),
        (.mem ((Operand.reg 4 : Operand 64).read s + 384) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 3 : Operand 64).read s + 16) : Operand 64),
        (.mem ((Operand.reg 4 : Operand 64).read s + 392) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 3 : Operand 64).read s + 24) : Operand 64),
        (.mem ((Operand.reg 4 : Operand 64).read s + 400) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 3 : Operand 64).read s + 32) : Operand 64),
        (.mem ((Operand.reg 4 : Operand 64).read s + 408) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 3 : Operand 64).read s + 40) : Operand 64),
        (.mem ((Operand.reg 4 : Operand 64).read s + 416) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 3 : Operand 64).read s + 48) : Operand 64),
        (.mem ((Operand.reg 4 : Operand 64).read s + 424) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 3 : Operand 64).read s + 56) : Operand 64),
        (.mem ((Operand.reg 4 : Operand 64).read s + 432) : Operand 64).read s⟩
    ] }

set_option maxHeartbeats 3200000 in
theorem copy [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary CopyPre (codeRange 0x11019c copyBytes)
      (Effect.post copyEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x11019c 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d32 432)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.readable 432 (by simp)⟩
  case next =>
    intro s hP
    exact boundary_ne_program hout (inProgram_of_textOffset 0x101a4 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1101a4 0x48 (by simp [RexWPrefix]) 1
    (.base 3 (.d8 56)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11019c copyBytes 8 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 56 (by simp)
    · x86_norm
      exact hP.codeApart 56 (by simp) 0x101a4 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 56 (by simp) 0x1019c 95 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x101a8 (by decide))
  advance_then (mov_r64_m64_effect_step 0x1101a8 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d32 424)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11019c copyBytes 12 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 424 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x101b0 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1101b0 0x48 (by simp [RexWPrefix]) 1
    (.base 3 (.d8 48)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11019c copyBytes 20 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 48 (by simp)
    · x86_norm
      exact hP.codeApart 48 (by simp) 0x101b0 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 48 (by simp) 0x1019c 95 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x101b4 (by decide))
  advance_then (mov_r64_m64_effect_step 0x1101b4 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d32 416)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11019c copyBytes 24 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 416 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x101bc (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1101bc 0x48 (by simp [RexWPrefix]) 1
    (.base 3 (.d8 40)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11019c copyBytes 32 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 40 (by simp)
    · x86_norm
      exact hP.codeApart 40 (by simp) 0x101bc 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 40 (by simp) 0x1019c 95 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x101c0 (by decide))
  advance_then (mov_r64_m64_effect_step 0x1101c0 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d32 408)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11019c copyBytes 36 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 408 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x101c8 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1101c8 0x48 (by simp [RexWPrefix]) 1
    (.base 3 (.d8 32)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11019c copyBytes 44 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 32 (by simp)
    · x86_norm
      exact hP.codeApart 32 (by simp) 0x101c8 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 32 (by simp) 0x1019c 95 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x101cc (by decide))
  advance_then (mov_r64_m64_effect_step 0x1101cc 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d32 400)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11019c copyBytes 48 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 400 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x101d4 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1101d4 0x48 (by simp [RexWPrefix]) 1
    (.base 3 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11019c copyBytes 56 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 24 (by simp)
    · x86_norm
      exact hP.codeApart 24 (by simp) 0x101d4 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 24 (by simp) 0x1019c 95 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x101d8 (by decide))
  advance_then (mov_r64_m64_effect_step 0x1101d8 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d32 392)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11019c copyBytes 60 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 392 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x101e0 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1101e0 0x48 (by simp [RexWPrefix]) 1
    (.base 3 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11019c copyBytes 68 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 16 (by simp)
    · x86_norm
      exact hP.codeApart 16 (by simp) 0x101e0 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 16 (by simp) 0x1019c 95 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x101e4 (by decide))
  advance_then (mov_r64_m64_effect_step 0x1101e4 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d32 376)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11019c copyBytes 72 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 376 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x101ec (by decide))
  advance_then (mov_r64_m64_effect_step 0x1101ec 0x48 (by simp [RexWPrefix]) 2
    (.sib 4 none 0 (.d32 384)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11019c copyBytes 80 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 384 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x101f4 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1101f4 0x48 (by simp [RexWPrefix]) 2
    (.base 3 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11019c copyBytes 88 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 8 (by simp)
    · x86_norm
      exact hP.codeApart 8 (by simp) 0x101f4 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 8 (by simp) 0x1019c 95 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x101f8 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1101f8 0x48 (by simp [RexWPrefix]) 1
    (.base 3 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11019c copyBytes 92 3
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 0 (by simp)
    · x86_norm
      exact hP.codeApart 0 (by simp) 0x101f8 3 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 0 (by simp) 0x1019c 95 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x101fb (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  have hread (mem : Ram) (i j : BitVec 64) (v : BitVec 64)
      (hi : i ∈ ([0,8,16,24,32,40,48,56] : List (BitVec 64)))
      (hj : j ∈ ([376,384,392,400,408,416,424,432] : List (BitVec 64))) :
      memLoad (memStore mem ((Operand.reg 3 : Operand 64).read s + i) v)
        ((Operand.reg 4 : Operand 64).read s + j) 64 =
      memLoad mem ((Operand.reg 4 : Operand 64).read s + j) 64 :=
    memLoad_memStore_rangeApart _ _ _ _ 64 (hP.sourceApart i hi j hj)
  have h64_328 := fun mem v => hread mem 56 424 v (by decide) (by decide)
  have h64_320 := fun mem v => hread mem 56 416 v (by decide) (by decide)
  have h56_320 := fun mem v => hread mem 48 416 v (by decide) (by decide)
  have h64_312 := fun mem v => hread mem 56 408 v (by decide) (by decide)
  have h56_312 := fun mem v => hread mem 48 408 v (by decide) (by decide)
  have h48_312 := fun mem v => hread mem 40 408 v (by decide) (by decide)
  have h64_304 := fun mem v => hread mem 56 400 v (by decide) (by decide)
  have h56_304 := fun mem v => hread mem 48 400 v (by decide) (by decide)
  have h48_304 := fun mem v => hread mem 40 400 v (by decide) (by decide)
  have h40_304 := fun mem v => hread mem 32 400 v (by decide) (by decide)
  have h64_296 := fun mem v => hread mem 56 392 v (by decide) (by decide)
  have h56_296 := fun mem v => hread mem 48 392 v (by decide) (by decide)
  have h48_296 := fun mem v => hread mem 40 392 v (by decide) (by decide)
  have h40_296 := fun mem v => hread mem 32 392 v (by decide) (by decide)
  have h32_296 := fun mem v => hread mem 24 392 v (by decide) (by decide)
  have h64_280 := fun mem v => hread mem 56 376 v (by decide) (by decide)
  have h56_280 := fun mem v => hread mem 48 376 v (by decide) (by decide)
  have h48_280 := fun mem v => hread mem 40 376 v (by decide) (by decide)
  have h40_280 := fun mem v => hread mem 32 376 v (by decide) (by decide)
  have h32_280 := fun mem v => hread mem 24 376 v (by decide) (by decide)
  have h24_280 := fun mem v => hread mem 16 376 v (by decide) (by decide)
  have h64_288 := fun mem v => hread mem 56 384 v (by decide) (by decide)
  have h56_288 := fun mem v => hread mem 48 384 v (by decide) (by decide)
  have h48_288 := fun mem v => hread mem 40 384 v (by decide) (by decide)
  have h40_288 := fun mem v => hread mem 32 384 v (by decide) (by decide)
  have h32_288 := fun mem v => hread mem 24 384 v (by decide) (by decide)
  have h24_288 := fun mem v => hread mem 16 384 v (by decide) (by decide)
  simp only [BitVec.ofNat_eq_ofNat] at h64_328 h64_320 h56_320 h64_312 h56_312 h48_312 h64_304 h56_304 h48_304 h40_304 h64_296 h56_296 h48_296 h40_296 h32_296 h64_280 h56_280 h48_280 h40_280 h32_280 h24_280 h64_288 h56_288 h48_288 h40_288 h32_288 h24_288
  apply hH.weaken
  · x86_norm [copyEffect]
  · x86_norm [copyEffect, operand_write_reg_external, operand_write_mem_external, h64_328, h64_320, h56_320, h64_312, h56_312, h48_312, h64_304, h56_304, h48_304, h40_304, h64_296, h56_296, h48_296, h40_296, h32_296, h64_280, h56_280, h48_280, h40_280, h32_280, h24_280, h64_288, h56_288, h48_288, h40_288, h32_288, h24_288]
    all_goals (repeat constructor <;> rfl)
  · intro i; cases i <;> x86_norm [copyEffect]
  · x86_norm [copyEffect]

end P256.Proofs.Sec1.Affine.Compressed.Finish.Payload
