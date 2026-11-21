import P256.Proofs.Verifying.Message.Convert.CopyY
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Convert.One

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Field.Montgomery.Schoolbook (memLoad_memStore_rangeApart)

def source := (fun _ : RamState => (0x202580 : BitVec 64))
def destination := (fun s : RamState => (Operand.reg 4 : Operand 64).read s + 64)
def bytes : List UInt8 := [0x4c, 0x8d, 0x74, 0x24, 0x40, 0x48, 0x8b, 0x5, 0xe2, 0x4b, 0xf, 0x0, 0x48, 0x89, 0x44, 0x24, 0x58, 0x48, 0x8b, 0x5, 0xce, 0x4b, 0xf, 0x0, 0x48, 0x89, 0x44, 0x24, 0x50, 0x48, 0x8b, 0x5, 0xba, 0x4b, 0xf, 0x0, 0x48, 0x89, 0x44, 0x24, 0x48, 0x48, 0x8b, 0x5, 0xa6, 0x4b, 0xf, 0x0, 0x48, 0x89, 0x44, 0x24, 0x40]

def effect (s : RamState) : Effect :=
  { rip := 0x10d9df
    writes := [
      ⟨(.reg 14 : Operand 64), destination s⟩,
      ⟨(.reg 0 : Operand 64), (.mem (source s) : Operand 64).read s⟩,
      ⟨(.mem (destination s) : Operand 64), (.mem (source s) : Operand 64).read s⟩,
      ⟨(.mem (destination s + 8) : Operand 64), (.mem (source s + 8) : Operand 64).read s⟩,
      ⟨(.mem (destination s + 16) : Operand 64), (.mem (source s + 16) : Operand 64).read s⟩,
      ⟨(.mem (destination s + 24) : Operand 64), (.mem (source s + 24) : Operand 64).read s⟩] }

theorem copy [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (Copy32.Pre 0x10d9aa source destination)
      (codeRange 0x10d9aa bytes) (Effect.post effect) := by
  advance_begin (lea_r64_effect_step 0x10d9aa 0x4c (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d8 64)) (by decide) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0xd9af (by decide))
  advance_then (mov_r64_m64_effect_step 0x10d9af 0x48 (by simp [RexWPrefix]) 0 (.rip 0xf4be2) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d9aa bytes 5 7
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa only [source, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.reduceAdd] using hP.readable 24 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xd9b6 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10d9b6 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 88)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d9aa bytes 12 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      simpa only [destination, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd] using hP.writable 24 (by simp)
    · x86_norm
      simpa only [destination, Extracted.textAddress, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd] using hP.codeApart 24 (by simp) 0xd9b6 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa only [destination, Extracted.textAddress, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd] using hP.codeApart 24 (by simp) 0xd9aa 53 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xd9bb (by decide))
  advance_then (mov_r64_m64_effect_step 0x10d9bb 0x48 (by simp [RexWPrefix]) 0 (.rip 0xf4bce) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d9aa bytes 17 7
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa only [source, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.reduceAdd] using hP.readable 16 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xd9c2 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10d9c2 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 80)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d9aa bytes 24 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      simpa only [destination, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd] using hP.writable 16 (by simp)
    · x86_norm
      simpa only [destination, Extracted.textAddress, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd] using hP.codeApart 16 (by simp) 0xd9c2 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa only [destination, Extracted.textAddress, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd] using hP.codeApart 16 (by simp) 0xd9aa 53 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xd9c7 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10d9c7 0x48 (by simp [RexWPrefix]) 0 (.rip 0xf4bba) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d9aa bytes 29 7
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa only [source, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.reduceAdd] using hP.readable 8 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xd9ce (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10d9ce 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 72)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d9aa bytes 36 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      simpa only [destination, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd] using hP.writable 8 (by simp)
    · x86_norm
      simpa only [destination, Extracted.textAddress, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd] using hP.codeApart 8 (by simp) 0xd9ce 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa only [destination, Extracted.textAddress, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd] using hP.codeApart 8 (by simp) 0xd9aa 53 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xd9d3 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10d9d3 0x48 (by simp [RexWPrefix]) 0 (.rip 0xf4ba6) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d9aa bytes 41 7
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa only [source, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.reduceAdd] using hP.readable 0 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xd9da (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10d9da 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 64)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d9aa bytes 48 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      simpa only [destination, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd] using hP.writable 0 (by simp)
    · x86_norm
      simpa only [destination, Extracted.textAddress, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd] using hP.codeApart 0 (by simp) 0xd9da 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa only [destination, Extracted.textAddress, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd] using hP.codeApart 0 (by simp) 0xd9aa 53 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xd9df (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  have hread (mem : Ram) (i j : Nat) (v : BitVec 64)
      (hi : i + 8 ≤ 32) (hj : j + 8 ≤ 32) :
      memLoad (memStore mem (destination s + BitVec.ofNat 64 i) v)
        (source s + BitVec.ofNat 64 j) 64 = memLoad mem (source s + BitVec.ofNat 64 j) 64 := by
    apply memLoad_memStore_rangeApart
    intro k hk l hl he
    apply hP.apart (i+k) (by omega) (j+l) (by omega)
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using he
  have h24_16 := fun mem v => hread mem 24 16 v (by decide) (by decide)
  have h24_8 := fun mem v => hread mem 24 8 v (by decide) (by decide)
  have h24_0 := fun mem v => hread mem 24 0 v (by decide) (by decide)
  have h16_8 := fun mem v => hread mem 16 8 v (by decide) (by decide)
  have h16_0 := fun mem v => hread mem 16 0 v (by decide) (by decide)
  have h8_0 := fun mem v => hread mem 8 0 v (by decide) (by decide)
  simp only [source, destination, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
    BitVec.add_assoc, BitVec.reduceAdd] at h24_16 h24_8 h24_0 h16_8 h16_0 h8_0
  apply hH.weaken
  · x86_norm [effect]
  · x86_norm [effect, source, destination, h24_16, h24_8, h24_0, h16_8, h16_0, h8_0, BitVec.add_assoc, BitVec.add_zero]
    all_goals (repeat constructor <;> rfl)
  · intro i; cases i <;> x86_norm [effect]
  · x86_norm [effect, source, destination, BitVec.add_assoc]

end P256.Proofs.Verifying.Message.Convert.One
