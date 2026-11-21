import P256.Proofs.Projective.Multiply.Machine.Lookup.Select.Setup.Effect
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.Code
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)

open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Projective.Multiply.Machine.Lookup.Select

open P256.Proofs.Field P256.Proofs.Program P256.Spec.Program.Routines
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure SetupSuffixPre (s : RamState) : Prop where
  rip : s.RIP = 0x11438b
  readable : ∀ i ∈ ([0, 8, 16, 24] : List (BitVec 64)),
    MemReadable s ((Operand.reg 6 : Operand 64).read s + i) 8
  writable : ∀ i ∈ ([0, 8, 16, 24] : List (BitVec 64)),
    MemWritable s ((Operand.reg 4 : Operand 64).read s + i) 8
  codeApart : ∀ i ∈ ([0, 8, 16, 24] : List (BitVec 64)), ∀ offset len : Nat,
    offset + len ≤ 118431 → RangeApart ((Operand.reg 4 : Operand 64).read s + i) 8
      (Extracted.textAddress + BitVec.ofNat 64 offset) len
  sourceApart : ∀ i ∈ ([0, 8, 16, 24] : List (BitVec 64)),
    ∀ j ∈ ([0, 8, 16, 24] : List (BitVec 64)),
    RangeApart ((Operand.reg 4 : Operand 64).read s + i) 8
      ((Operand.reg 6 : Operand 64).read s + j) 8

def setupSuffixBytes : List UInt8 :=
  [0x48, 0x8b, 0x46, 0x18, 0x48, 0x89, 0x44, 0x24, 0x18,
   0x48, 0x8b, 0x46, 0x10, 0x48, 0x89, 0x44, 0x24, 0x10,
   0x48, 0x8b, 0x06, 0x48, 0x8b, 0x4e, 0x08, 0x48, 0x89, 0x4c, 0x24, 0x08,
   0x48, 0x89, 0x04, 0x24, 0x48, 0x89, 0xe7, 0xbe, 4, 0, 0, 0, 0xb9, 4, 0, 0, 0]

def setupSuffixEffect (s : RamState) : Effect :=
  { rip := 0x1143ba
    writes := [
      ⟨(.reg 0 : Operand 64), (.mem ((Operand.reg 6 : Operand 64).read s + 0) : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), 4⟩,
      ⟨(.reg 6 : Operand 64), 4⟩,
      ⟨(.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 0) : Operand 64),
        (.mem ((Operand.reg 6 : Operand 64).read s + 0) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 8) : Operand 64),
        (.mem ((Operand.reg 6 : Operand 64).read s + 8) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 16) : Operand 64),
        (.mem ((Operand.reg 6 : Operand 64).read s + 16) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 24) : Operand 64),
        (.mem ((Operand.reg 6 : Operand 64).read s + 24) : Operand 64).read s⟩] }

set_option maxHeartbeats 1600000 in
theorem setup_suffix [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary SetupSuffixPre (codeRange 0x11438b setupSuffixBytes)
      (Effect.post setupSuffixEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x11438b 0x48 (by simp [RexWPrefix]) 0 (.base 6 (.d8 24)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.readable 24 (by simp)⟩
  case next =>
    intro s hP
    exact boundary_ne_program hout (inProgram_of_textOffset 0x1438f (by decide))
  advance_then (mov_m64_r64_effect_step 0x11438f 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11438b setupSuffixBytes 4 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 24 (by simp)
    · x86_norm
      exact hP.codeApart 24 (by simp) 0x1438f 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 24 (by simp) 0x1438b 47 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x14394 (by decide))
  advance_then (mov_r64_m64_effect_step 0x114394 0x48 (by simp [RexWPrefix]) 0 (.base 6 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11438b setupSuffixBytes 9 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 16 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x14398 (by decide))
  advance_then (mov_m64_r64_effect_step 0x114398 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11438b setupSuffixBytes 13 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 16 (by simp)
    · x86_norm
      exact hP.codeApart 16 (by simp) 0x14398 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 16 (by simp) 0x1438b 47 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1439d (by decide))
  advance_then (mov_r64_m64_effect_step 0x11439d 0x48 (by simp [RexWPrefix]) 0 (.base 6 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11438b setupSuffixBytes 18 3
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 0 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x143a0 (by decide))
  advance_then (mov_r64_m64_effect_step 0x1143a0 0x48 (by simp [RexWPrefix]) 1 (.base 6 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11438b setupSuffixBytes 21 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 8 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x143a4 (by decide))
  advance_then (mov_m64_r64_effect_step 0x1143a4 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11438b setupSuffixBytes 25 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 8 (by simp)
    · x86_norm
      exact hP.codeApart 8 (by simp) 0x143a4 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 8 (by simp) 0x1438b 47 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x143a9 (by decide))
  advance_then (mov_m64_r64_effect_step 0x1143a9 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11438b setupSuffixBytes 30 4
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 0 (by simp)
    · x86_norm
      exact hP.codeApart 0 (by simp) 0x143a9 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 0 (by simp) 0x1438b 47 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x143ad (by decide))
  advance_then (mov_r64_r64_effect_step 0x1143ad 0x48 0xe7 (by simp [RexWPrefix]) (by decide +kernel))
  case sub => exact codeRange_slice_subset 0x11438b setupSuffixBytes 34 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x143b0 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x1143b0 0xbe (by decide +kernel) 4)
  case sub => exact codeRange_slice_subset 0x11438b setupSuffixBytes 37 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x143b5 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x1143b5 0xb9 (by decide +kernel) 4)
  case sub => exact codeRange_slice_subset 0x11438b setupSuffixBytes 42 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x143ba (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  have hread (mem : Ram) (i j : BitVec 64) (v : BitVec 64)
      (hi : i ∈ ([0, 8, 16, 24] : List (BitVec 64)))
      (hj : j ∈ ([0, 8, 16, 24] : List (BitVec 64))) :
      memLoad (memStore mem ((Operand.reg 4 : Operand 64).read s + i) v)
        ((Operand.reg 6 : Operand 64).read s + j) 64 =
      memLoad mem ((Operand.reg 6 : Operand 64).read s + j) 64 :=
    P256.Proofs.Common.Field.Montgomery.Schoolbook.memLoad_memStore_rangeApart _ _ _ _ _ (hP.sourceApart i hi j hj)
  have h2416 := fun mem v => hread mem 24 16 v (by decide) (by decide)
  have h240 := fun mem v => hread mem 24 0 v (by decide) (by decide)
  have h248 := fun mem v => hread mem 24 8 v (by decide) (by decide)
  have h160 := fun mem v => hread mem 16 0 v (by decide) (by decide)
  have h168 := fun mem v => hread mem 16 8 v (by decide) (by decide)
  simp only [BitVec.ofNat_eq_ofNat] at h2416 h240 h248 h160 h168
  apply hH.weaken
  · x86_norm [setupSuffixEffect]
  · x86_norm [setupSuffixEffect, h2416, h240, h248, h160, h168]
    all_goals (repeat constructor <;> rfl)
  · intro i; cases i <;> x86_norm [setupSuffixEffect]
  · x86_norm [setupSuffixEffect]

end P256.Proofs.Projective.Multiply.Machine.Lookup.Select
