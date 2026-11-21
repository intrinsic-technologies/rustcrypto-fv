import P256.Proofs.Nonce.Update.Seeded.Prepare.State
import P256.Proofs.Nonce.Update.Prepare.Memory
import P256.Proofs.HMAC.Key.Output.Bytes
import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Seeded.Prepare.KeySetup

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10a455
  readable : ∀ i ∈ ([0,8,16,24] : List Nat), MemReadable s ((Operand.reg 3 : Operand 64).read s+BitVec.ofNat 64 i) 8
  writable : ∀ i ∈ ([464,472,480,488,0,8,16,24,32,40,48,56] : List Nat),
    MemWritable s (rspOf s+BitVec.ofNat 64 i) 8
  apart : ∀ i ∈ ([464,472,480,488,0,8,16,24,32,40,48,56] : List Nat),
    ∀ off len : Nat, off+len≤118431 → RangeApart (rspOf s+BitVec.ofNat 64 i) 8
      (Extracted.textAddress+BitVec.ofNat 64 off) len
  inputApart : ∀ i ∈ ([464,472,480,488] : List Nat),
    RangeApart (rspOf s+BitVec.ofNat 64 i) 8 ((Operand.reg 3 : Operand 64).read s) 32

def bytes : List UInt8 :=
  [72, 199, 132, 36, 232, 1, 0, 0, 0, 0, 0, 0, 72, 199, 132, 36, 224, 1, 0, 0, 0, 0, 0, 0, 72, 199, 132, 36, 216, 1, 0, 0, 0, 0, 0, 0, 72, 199, 132, 36, 208, 1, 0, 0, 0, 0, 0, 0, 72, 139, 67, 24, 72, 139, 75, 16, 72, 139, 19, 72, 139, 115, 8, 72, 137, 20, 36, 72, 137, 116, 36, 8, 72, 137, 76, 36, 16, 72, 137, 68, 36, 24, 72, 199, 68, 36, 32, 0, 0, 0, 0, 72, 199, 68, 36, 40, 0, 0, 0, 0, 72, 199, 68, 36, 48, 0, 0, 0, 0, 72, 199, 68, 36, 56, 0, 0, 0, 0]

def effect (s : RamState) : Effect :=
  { rip := 0x10a4cb
    writes := [⟨(.reg 0 : Operand 64),(.mem ((Operand.reg 3 : Operand 64).read s+24) : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64),(.mem ((Operand.reg 3 : Operand 64).read s+16) : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64),(.mem ((Operand.reg 3 : Operand 64).read s) : Operand 64).read s⟩,
      ⟨(.reg 6 : Operand 64),(.mem ((Operand.reg 3 : Operand 64).read s+8) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s+488) : Operand 64),0⟩,
      ⟨(.mem (rspOf s+480) : Operand 64),0⟩,
      ⟨(.mem (rspOf s+472) : Operand 64),0⟩,
      ⟨(.mem (rspOf s+464) : Operand 64),0⟩,
      ⟨(.mem (rspOf s+0) : Operand 64),(.mem ((Operand.reg 3 : Operand 64).read s) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s+8) : Operand 64),(.mem ((Operand.reg 3 : Operand 64).read s+8) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s+16) : Operand 64),(.mem ((Operand.reg 3 : Operand 64).read s+16) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s+24) : Operand 64),(.mem ((Operand.reg 3 : Operand 64).read s+24) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s+32) : Operand 64),0⟩,
      ⟨(.mem (rspOf s+40) : Operand 64),0⟩,
      ⟨(.mem (rspOf s+48) : Operand 64),0⟩,
      ⟨(.mem (rspOf s+56) : Operand 64),0⟩] }

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1200000 in
theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10a455 bytes) (Effect.post effect) := by
  advance_begin (mov_m64_imm32_effect_step 0x10a455 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 488)) (by decide) rfl rfl 0)
  case pre =>
    intro s hp
    exact ⟨hp.rip,hp.writable 488 (by simp),hp.apart 488 (by simp) 0xa455 12 (by decide)⟩
  case av =>
    intro s hp
    apply Effect.avoids_codeRange
    intro c hc a len eq
    simp only [movM64Imm32Effect,storeEffect_components,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl
    · cases eq; exact hp.apart 488 (by simp) 0xa455 118 (by decide)
    · cases eq
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0xa461 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x10a461 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 480)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10a455 bytes 12 12
  case mid =>
    intro s t hp hh ho
    refine ⟨StorePre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm; exact hp.writable 480 (by simp)
    · x86_norm; exact hp.apart 480 (by simp) 0xa461 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.apart 480 (by simp) 0xa455 118 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa46d (by decide))
  advance_then (mov_m64_imm32_effect_step 0x10a46d 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 472)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10a455 bytes 24 12
  case mid =>
    intro s t hp hh ho
    refine ⟨StorePre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm; exact hp.writable 472 (by simp)
    · x86_norm; exact hp.apart 472 (by simp) 0xa46d 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.apart 472 (by simp) 0xa455 118 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa479 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x10a479 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 464)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10a455 bytes 36 12
  case mid =>
    intro s t hp hh ho
    refine ⟨StorePre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm; exact hp.writable 464 (by simp)
    · x86_norm; exact hp.apart 464 (by simp) 0xa479 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.apart 464 (by simp) 0xa455 118 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa485 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10a485 0x48 (by simp [RexWPrefix]) 0 (.base 3 (.d8 24)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a455 bytes 48 4
  case mid =>
    intro s t hp hh ho
    refine ⟨LoadPre.of_holds hh (ho true) (by x86_norm) ?_ ?_, Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
    · x86_addr_obs
    · x86_norm; exact hp.readable 24 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa489 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10a489 0x48 (by simp [RexWPrefix]) 1 (.base 3 (.d8 16)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a455 bytes 52 4
  case mid =>
    intro s t hp hh ho
    refine ⟨LoadPre.of_holds hh (ho true) (by x86_norm) ?_ ?_, Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
    · x86_addr_obs
    · x86_norm; exact hp.readable 16 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa48d (by decide))
  advance_then (mov_r64_m64_effect_step 0x10a48d 0x48 (by simp [RexWPrefix]) 2 (.base 3 .none) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a455 bytes 56 3
  case mid =>
    intro s t hp hh ho
    refine ⟨LoadPre.of_holds hh (ho true) (by x86_norm) ?_ ?_, Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
    · x86_addr_obs
    · x86_norm; exact hp.readable 0 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa490 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10a490 0x48 (by simp [RexWPrefix]) 6 (.base 3 (.d8 8)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a455 bytes 59 4
  case mid =>
    intro s t hp hh ho
    refine ⟨LoadPre.of_holds hh (ho true) (by x86_norm) ?_ ?_, Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
    · x86_addr_obs
    · x86_norm; exact hp.readable 8 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa494 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10a494 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 .none) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a455 bytes 63 4
  case mid =>
    intro s t hp hh ho
    refine ⟨StorePre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm; exact hp.writable 0 (by simp)
    · x86_norm; exact hp.apart 0 (by simp) 0xa494 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.apart 0 (by simp) 0xa455 118 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa498 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10a498 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a455 bytes 67 5
  case mid =>
    intro s t hp hh ho
    refine ⟨StorePre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm; exact hp.writable 8 (by simp)
    · x86_norm; exact hp.apart 8 (by simp) 0xa498 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.apart 8 (by simp) 0xa455 118 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa49d (by decide))
  advance_then (mov_m64_r64_effect_step 0x10a49d 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 16)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a455 bytes 72 5
  case mid =>
    intro s t hp hh ho
    refine ⟨StorePre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm; exact hp.writable 16 (by simp)
    · x86_norm; exact hp.apart 16 (by simp) 0xa49d 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.apart 16 (by simp) 0xa455 118 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa4a2 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10a4a2 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 24)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a455 bytes 77 5
  case mid =>
    intro s t hp hh ho
    refine ⟨StorePre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm; exact hp.writable 24 (by simp)
    · x86_norm; exact hp.apart 24 (by simp) 0xa4a2 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.apart 24 (by simp) 0xa455 118 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa4a7 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x10a4a7 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 32)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10a455 bytes 82 9
  case mid =>
    intro s t hp hh ho
    refine ⟨StorePre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm; exact hp.writable 32 (by simp)
    · x86_norm; exact hp.apart 32 (by simp) 0xa4a7 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.apart 32 (by simp) 0xa455 118 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa4b0 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x10a4b0 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 40)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10a455 bytes 91 9
  case mid =>
    intro s t hp hh ho
    refine ⟨StorePre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm; exact hp.writable 40 (by simp)
    · x86_norm; exact hp.apart 40 (by simp) 0xa4b0 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.apart 40 (by simp) 0xa455 118 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa4b9 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x10a4b9 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 48)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10a455 bytes 100 9
  case mid =>
    intro s t hp hh ho
    refine ⟨StorePre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm; exact hp.writable 48 (by simp)
    · x86_norm; exact hp.apart 48 (by simp) 0xa4b9 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.apart 48 (by simp) 0xa455 118 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa4c2 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x10a4c2 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 56)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10a455 bytes 109 9
  case mid =>
    intro s t hp hh ho
    refine ⟨StorePre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm; exact hp.writable 56 (by simp)
    · x86_norm; exact hp.apart 56 (by simp) 0xa4c2 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.apart 56 (by simp) 0xa455 118 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa4cb (by decide))
  apply AdvanceTriple.block_end
  intro s t hp hh
  have operand_write_mem_external (m : RamState) (a : BitVec 64) (v : BitVec 64) :
      ((Operand.mem a : Operand 64).write m v).external = memStore m.external a v := rfl
  have hread (mem : Ram) (i j : Nat) (v : BitVec 64)
      (hi : i ∈ ([464,472,480,488] : List Nat)) (hj : j ∈ ([0,8,16,24] : List Nat)) :
      memLoad (memStore mem (rspOf s+BitVec.ofNat 64 i) v)
        ((Operand.reg 3 : Operand 64).read s+BitVec.ofNat 64 j) 64 =
        memLoad mem ((Operand.reg 3 : Operand 64).read s+BitVec.ofNat 64 j) 64 := by
    apply P256.Proofs.Common.Field.Montgomery.Schoolbook.memLoad_memStore_rangeApart
    intro a ha b hb eq
    have apart := hp.inputApart i hi
    change RangeApart (rspOf s+BitVec.ofNat 64 i) 8 ((Operand.reg 3 : Operand 64).read s) 32 at apart
    apply apart a ha (j+b) (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hj; omega)
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using eq
  have h464_0 := fun mem v => hread mem 464 0 v (by decide) (by decide)
  have h464_8 := fun mem v => hread mem 464 8 v (by decide) (by decide)
  have h464_16 := fun mem v => hread mem 464 16 v (by decide) (by decide)
  have h464_24 := fun mem v => hread mem 464 24 v (by decide) (by decide)
  have h472_0 := fun mem v => hread mem 472 0 v (by decide) (by decide)
  have h472_8 := fun mem v => hread mem 472 8 v (by decide) (by decide)
  have h472_16 := fun mem v => hread mem 472 16 v (by decide) (by decide)
  have h472_24 := fun mem v => hread mem 472 24 v (by decide) (by decide)
  have h480_0 := fun mem v => hread mem 480 0 v (by decide) (by decide)
  have h480_8 := fun mem v => hread mem 480 8 v (by decide) (by decide)
  have h480_16 := fun mem v => hread mem 480 16 v (by decide) (by decide)
  have h480_24 := fun mem v => hread mem 480 24 v (by decide) (by decide)
  have h488_0 := fun mem v => hread mem 488 0 v (by decide) (by decide)
  have h488_8 := fun mem v => hread mem 488 8 v (by decide) (by decide)
  have h488_16 := fun mem v => hread mem 488 16 v (by decide) (by decide)
  have h488_24 := fun mem v => hread mem 488 24 v (by decide) (by decide)
  simp only [BitVec.ofNat_eq_ofNat,BitVec.add_zero,rspOf] at h464_0 h464_8 h464_16 h464_24 h472_0 h472_8 h472_16 h472_24 h480_0 h480_8 h480_16 h480_24 h488_0 h488_8 h488_16 h488_24
  apply hh.weaken
  · x86_norm [effect]
  · x86_norm [effect,BitVec.add_zero,operand_write_mem_external, h464_0, h464_8, h464_16, h464_24, h472_0, h472_8, h472_16, h472_24, h480_0, h480_8, h480_16, h480_24, h488_0, h488_8, h488_16, h488_24]
    all_goals repeat constructor <;> rfl
  · intro i; cases i <;> x86_norm [effect]
  · x86_norm [effect]


end P256.Proofs.Nonce.Update.Seeded.Prepare.KeySetup
