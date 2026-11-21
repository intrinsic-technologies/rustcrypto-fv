import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Encoding.Serialize.Convert.Compose
import P256.Proofs.Common.Instructions.CrossPageStore
import P256.Proofs.Program.Code
import P256.Proofs.Common.Field.Operations.Run.Compose

set_option autoImplicit false
open P256.Proofs.Common.Field.Montgomery.Schoolbook (memLoad_memStore_rangeApart)

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Sec1.Decompress.Select

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

private theorem operand_write_reg_external (s : RamState) (r : BitVec 5) (v : BitVec 64) :
    ((Operand.reg r : Operand 64).write s v).external = s.external := rfl

private theorem operand_write_mem_external (s : RamState) (a : BitVec 64) (v : BitVec 64) :
    ((Operand.mem a : Operand 64).write s v).external = memStore s.external a v := rfl

structure CopyPre (s : RamState) : Prop where
  rip : s.RIP = 0x10ff31
  readable : ∀ i ∈ ([152,160,168,176] : List (BitVec 64)),
    MemReadable s ((Operand.reg 4 : Operand 64).read s + i) 8
  writable : ∀ i ∈ ([0,8,16,24] : List (BitVec 64)),
    P256.Proofs.Common.Instructions.CrossPageStore.Writable s ((Operand.reg 4 : Operand 64).read s + i) 8
  codeApart : ∀ i ∈ ([0,8,16,24] : List (BitVec 64)), ∀ offset len : Nat,
    offset + len ≤ 118431 → RangeApart ((Operand.reg 4 : Operand 64).read s + i) 8
      (Extracted.textAddress + BitVec.ofNat 64 offset) len

def copyBytes : List UInt8 := [72,139,132,36,176,0,0,0,72,137,68,36,24,72,139,132,36,168,0,0,0,72,137,68,36,16,72,139,132,36,152,0,0,0,72,139,140,36,160,0,0,0,72,137,76,36,8,72,137,4,36]

def copyEffect (s : RamState) : Effect :=
  { rip := 0x10ff64
    writes := [
      ⟨(.reg 0 : Operand 64), (.mem ((Operand.reg 4 : Operand 64).read s + 152) : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), (.mem ((Operand.reg 4 : Operand 64).read s + 160) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 24) : Operand 64),
        (.mem ((Operand.reg 4 : Operand 64).read s + 176) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 16) : Operand 64),
        (.mem ((Operand.reg 4 : Operand 64).read s + 168) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 8) : Operand 64),
        (.mem ((Operand.reg 4 : Operand 64).read s + 160) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s) : Operand 64),
        (.mem ((Operand.reg 4 : Operand 64).read s + 152) : Operand 64).read s⟩] }

set_option maxHeartbeats 800000 in
theorem copy [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary CopyPre (codeRange 0x10ff31 copyBytes) (Effect.post copyEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x10ff31 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 176)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.readable 176 (by simp)⟩
  case next =>
    intro s hP
    exact boundary_ne_program hout (inProgram_of_textOffset 0xff39 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10ff39 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10ff31 copyBytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 24 (by simp)
    · x86_norm
      exact hP.codeApart 24 (by simp) 0xff39 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 24 (by simp) 0xff31 51 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xff3e (by decide))
  advance_then (mov_r64_m64_effect_step 0x10ff3e 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 168)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10ff31 copyBytes 13 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 168 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xff46 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10ff46 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10ff31 copyBytes 21 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 16 (by simp)
    · x86_norm
      exact hP.codeApart 16 (by simp) 0xff46 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 16 (by simp) 0xff31 51 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xff4b (by decide))
  advance_then (mov_r64_m64_effect_step 0x10ff4b 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 152)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10ff31 copyBytes 26 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 152 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xff53 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10ff53 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d32 160)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10ff31 copyBytes 34 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 160 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xff5b (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10ff5b 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10ff31 copyBytes 42 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 8 (by simp)
    · x86_norm
      exact hP.codeApart 8 (by simp) 0xff5b 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 8 (by simp) 0xff31 51 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xff60 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10ff60 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10ff31 copyBytes 47 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 0 (by simp)
    · x86_norm
      exact hP.codeApart 0 (by simp) 0xff60 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 0 (by simp) 0xff31 51 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xff64 (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  have hread (mem : Ram) (i j : Nat) (v : BitVec 64)
      (hi : i + 8 ≤ 32) (hj : 152 ≤ j ∧ j ≤ 176) :
      memLoad (memStore mem ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 i) v)
        ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 j) 64 =
      memLoad mem ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 j) 64 :=
    memLoad_memStore_rangeApart _ _ _ _ 64
      (RangeApart.offsets _ (by omega) (by omega) (.inl (by omega)))
  have h16_152 := fun mem v => hread mem 16 152 v (by decide) (by decide)
  have h16_160 := fun mem v => hread mem 16 160 v (by decide) (by decide)
  have h16_168 := fun mem v => hread mem 16 168 v (by decide) (by decide)
  have h24_152 := fun mem v => hread mem 24 152 v (by decide) (by decide)
  have h24_160 := fun mem v => hread mem 24 160 v (by decide) (by decide)
  have h24_168 := fun mem v => hread mem 24 168 v (by decide) (by decide)
  simp only [BitVec.ofNat_eq_ofNat] at h16_152 h16_160 h16_168 h24_152 h24_160 h24_168
  apply hH.weaken
  · x86_norm [BitVec.add_zero, copyEffect]
  · x86_norm [BitVec.add_zero, copyEffect, operand_write_reg_external, operand_write_mem_external, h16_152, h16_160, h16_168, h24_152, h24_160, h24_168]
    all_goals (repeat constructor <;> rfl)
  · intro i; cases i <;> x86_norm [BitVec.add_zero, copyEffect]
  · x86_norm [BitVec.add_zero, copyEffect]

end P256.Proofs.Sec1.Decompress.Select
