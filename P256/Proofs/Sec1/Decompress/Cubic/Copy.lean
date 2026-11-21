import P256.Proofs.Program.Code
import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose
import P256.Proofs.Common.Instructions.CrossPageStore
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.Instructions.CrossPageStore
import X86Proofs.Instructions.MovLoad.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Field.Montgomery.Schoolbook (memLoad_memStore_rangeApart)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Sec1.Decompress.Cubic

open P256.Spec.Program.Routines
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

private theorem operand_write_reg_external (s : RamState) (r : BitVec 5) (v : BitVec 64) :
    ((Operand.reg r : Operand 64).write s v).external = s.external := rfl

private theorem operand_write_mem_external (s : RamState) (a : BitVec 64) (v : BitVec 64) :
    ((Operand.mem a : Operand 64).write s v).external = memStore s.external a v := rfl

structure CopyPre (s : RamState) : Prop where
  rip : s.RIP = 0x10fdcc
  readable : ∀ i ∈ ([120,128,136,144] : List (BitVec 64)),
    MemReadable s ((Operand.reg 4 : Operand 64).read s + i) 8
  writable : ∀ i ∈ ([0,8,16,24] : List (BitVec 64)),
    P256.Proofs.Common.Instructions.CrossPageStore.Writable s ((Operand.reg 4 : Operand 64).read s + i) 8
  codeApart : ∀ i ∈ ([0,8,16,24] : List (BitVec 64)), ∀ offset len : Nat,
    offset + len ≤ 118431 → RangeApart ((Operand.reg 4 : Operand 64).read s + i) 8
      (Extracted.textAddress + BitVec.ofNat 64 offset) len

def copyBytes : List UInt8 :=
  [72, 139, 132, 36, 144, 0, 0, 0, 72, 137, 68, 36, 24, 72, 139, 132, 36, 136, 0, 0, 0, 72, 137, 68, 36, 16, 72, 139, 68, 36, 120, 72, 139, 140, 36, 128, 0, 0, 0, 72, 137, 76, 36, 8, 72, 137, 4, 36]

def copyEffect (s : RamState) : Effect :=
  { rip := 0x10fdfc
    writes := [
      ⟨(.reg 0 : Operand 64), (.mem ((Operand.reg 4 : Operand 64).read s + 120) : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), (.mem ((Operand.reg 4 : Operand 64).read s + 128) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 0) : Operand 64),
        (.mem ((Operand.reg 4 : Operand 64).read s + 120) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 8) : Operand 64),
        (.mem ((Operand.reg 4 : Operand 64).read s + 128) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 16) : Operand 64),
        (.mem ((Operand.reg 4 : Operand 64).read s + 136) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 24) : Operand 64),
        (.mem ((Operand.reg 4 : Operand 64).read s + 144) : Operand 64).read s⟩
    ] }

set_option maxHeartbeats 800000 in
theorem copy [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary CopyPre (codeRange 0x10fdcc copyBytes) (Effect.post copyEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x10fdcc 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 144)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.readable 144 (by simp)⟩
  case next =>
    intro s hP
    exact boundary_ne_program hout (inProgram_of_textOffset 0xfdd4 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10fdd4 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fdcc copyBytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 24 (by simp)
    · x86_norm
      exact hP.codeApart 24 (by simp) 0xfdd4 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 24 (by simp) 0xfdcc 48 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfdd9 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10fdd9 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 136)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fdcc copyBytes 13 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 136 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfde1 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10fde1 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fdcc copyBytes 21 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 16 (by simp)
    · x86_norm
      exact hP.codeApart 16 (by simp) 0xfde1 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 16 (by simp) 0xfdcc 48 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfde6 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10fde6 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 120)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fdcc copyBytes 26 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 120 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfdeb (by decide))
  advance_then (mov_r64_m64_effect_step 0x10fdeb 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d32 128)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fdcc copyBytes 31 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 128 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfdf3 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10fdf3 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fdcc copyBytes 39 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 8 (by simp)
    · x86_norm
      exact hP.codeApart 8 (by simp) 0xfdf3 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 8 (by simp) 0xfdcc 48 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfdf8 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10fdf8 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10fdcc copyBytes 44 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 0 (by simp)
    · x86_norm
      exact hP.codeApart 0 (by simp) 0xfdf8 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 0 (by simp) 0xfdcc 48 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfdfc (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  have hread (mem : Ram) (i j : Nat) (v : BitVec 64)
      (hi : i + 8 ≤ 32) (hj : 120 ≤ j ∧ j ≤ 144) :
      memLoad (memStore mem ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 i) v)
        ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 j) 64 =
      memLoad mem ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 j) 64 :=
    memLoad_memStore_rangeApart _ _ _ _ _
      (RangeApart.offsets _ (by omega) (by omega) (.inl (by omega)))
  have h24_136 := fun mem v => hread mem 24 136 v (by decide) (by decide)
  have h24_120 := fun mem v => hread mem 24 120 v (by decide) (by decide)
  have h24_128 := fun mem v => hread mem 24 128 v (by decide) (by decide)
  have h16_120 := fun mem v => hread mem 16 120 v (by decide) (by decide)
  have h16_128 := fun mem v => hread mem 16 128 v (by decide) (by decide)
  apply hH.weaken
  · x86_norm [copyEffect]
  · x86_norm [copyEffect, operand_write_reg_external, operand_write_mem_external, h24_136, h24_120, h24_128, h16_120, h16_128]
    all_goals (repeat constructor <;> rfl)
  · intro i; cases i <;> x86_norm [copyEffect]
  · x86_norm [copyEffect]

end P256.Proofs.Sec1.Decompress.Cubic
