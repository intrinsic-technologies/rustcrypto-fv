import P256.Proofs.Verifying.Message.Convert.CopyY

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Convert.CopyX

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Field.Montgomery.Schoolbook (memLoad_memStore_rangeApart)

def source := (fun s : RamState => (Operand.reg 2 : Operand 64).read s)
def destination := (fun s : RamState => (Operand.reg 4 : Operand 64).read s + 0)
def bytes : List UInt8 := [0x48, 0x8b, 0x2, 0x48, 0x8b, 0x4a, 0x8, 0x48, 0x89, 0x4, 0x24, 0x48, 0x89, 0x4c, 0x24, 0x8, 0x48, 0x8b, 0x42, 0x10, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8b, 0x42, 0x18, 0x48, 0x89, 0x44, 0x24, 0x18]

def effect (s : RamState) : Effect :=
  { rip := 0x10d9aa
    writes := [
      ⟨(.reg 0 : Operand 64), (.mem (source s + 24) : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), (.mem (source s + 8) : Operand 64).read s⟩,
      ⟨(.mem (destination s) : Operand 64), (.mem (source s) : Operand 64).read s⟩,
      ⟨(.mem (destination s + 8) : Operand 64), (.mem (source s + 8) : Operand 64).read s⟩,
      ⟨(.mem (destination s + 16) : Operand 64), (.mem (source s + 16) : Operand 64).read s⟩,
      ⟨(.mem (destination s + 24) : Operand 64), (.mem (source s + 24) : Operand 64).read s⟩] }

theorem copy [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (Copy32.Pre 0x10d988 source destination)
      (codeRange 0x10d988 bytes) (Effect.post effect) := by
  advance_begin (mov_r64_m64_effect_step 0x10d988 0x48 (by simp [RexWPrefix]) 0 (.base 2 .none) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    refine ⟨hP.rip, ?_⟩
    x86_norm
    simpa only [source, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hP.readable 0 (by simp)
  case next =>
    intro s hP
    exact boundary_ne_program hout (inProgram_of_textOffset 0xd98b (by decide))
  advance_then (mov_r64_m64_effect_step 0x10d98b 0x48 (by simp [RexWPrefix]) 1 (.base 2 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d988 bytes 3 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa only [source, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd] using hP.readable 8 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xd98f (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10d98f 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d988 bytes 7 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      simpa only [destination, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd] using hP.writable 0 (by simp)
    · x86_norm
      simpa only [destination, Extracted.textAddress, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd] using hP.codeApart 0 (by simp) 0xd98f 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa only [destination, Extracted.textAddress, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd] using hP.codeApart 0 (by simp) 0xd988 34 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xd993 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10d993 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d988 bytes 11 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      simpa only [destination, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd] using hP.writable 8 (by simp)
    · x86_norm
      simpa only [destination, Extracted.textAddress, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd] using hP.codeApart 8 (by simp) 0xd993 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa only [destination, Extracted.textAddress, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd] using hP.codeApart 8 (by simp) 0xd988 34 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xd998 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10d998 0x48 (by simp [RexWPrefix]) 0 (.base 2 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d988 bytes 16 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa only [source, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd] using hP.readable 16 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xd99c (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10d99c 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d988 bytes 20 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      simpa only [destination, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd] using hP.writable 16 (by simp)
    · x86_norm
      simpa only [destination, Extracted.textAddress, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd] using hP.codeApart 16 (by simp) 0xd99c 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa only [destination, Extracted.textAddress, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd] using hP.codeApart 16 (by simp) 0xd988 34 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xd9a1 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10d9a1 0x48 (by simp [RexWPrefix]) 0 (.base 2 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d988 bytes 25 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa only [source, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd] using hP.readable 24 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xd9a5 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10d9a5 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d988 bytes 29 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      simpa only [destination, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd] using hP.writable 24 (by simp)
    · x86_norm
      simpa only [destination, Extracted.textAddress, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd] using hP.codeApart 24 (by simp) 0xd9a5 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa only [destination, Extracted.textAddress, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd] using hP.codeApart 24 (by simp) 0xd988 34 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xd9aa (by decide))
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
  have h0_16 := fun mem v => hread mem 0 16 v (by decide) (by decide)
  have h8_16 := fun mem v => hread mem 8 16 v (by decide) (by decide)
  have h0_24 := fun mem v => hread mem 0 24 v (by decide) (by decide)
  have h8_24 := fun mem v => hread mem 8 24 v (by decide) (by decide)
  have h16_24 := fun mem v => hread mem 16 24 v (by decide) (by decide)
  simp only [source, destination, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
    ] at h0_16 h8_16 h0_24 h8_24 h16_24
  apply hH.weaken
  · x86_norm [effect]
  · x86_norm [effect, source, destination, h0_16, h8_16, h0_24, h8_24, h16_24,
      BitVec.add_assoc, BitVec.add_zero]
    all_goals (repeat constructor <;> rfl)
  · intro i; cases i <;> x86_norm [effect]
  · x86_norm [effect, source, destination, BitVec.add_assoc]

end P256.Proofs.Verifying.Message.Convert.CopyX
