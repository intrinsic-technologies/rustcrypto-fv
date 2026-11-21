import P256.Proofs.Nonce.Update.Prepare.Key.Arguments
import P256.Proofs.Nonce.Update.Prepare.Memory
import P256.Proofs.HMAC.Key.Output.Bytes
import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Prepare.Key

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)

structure InlinePre (s : RamState) : Prop where
  rip : s.RIP = 0x109f4a
  readable : ∀ i ∈ ([0,8,16,24] : List Nat), MemReadable s ((Operand.reg 7 : Operand 64).read s+BitVec.ofNat 64 i) 8
  writable : ∀ i ∈ ([464,472,480,488,88,96,104,112,120,128,136,144] : List Nat),
    MemWritable s (rspOf s+BitVec.ofNat 64 i) 8
  apart : ∀ i ∈ ([464,472,480,488,88,96,104,112,120,128,136,144] : List Nat),
    ∀ off len : Nat, off+len≤118431 → RangeApart (rspOf s+BitVec.ofNat 64 i) 8
      (Extracted.textAddress+BitVec.ofNat 64 off) len
  inputApart : ∀ i ∈ ([464,472,480,488] : List Nat),
    RangeApart (rspOf s+BitVec.ofNat 64 i) 8 ((Operand.reg 7 : Operand 64).read s) 32

def bytes : List UInt8 :=
  [72, 199, 132, 36, 232, 1, 0, 0, 0, 0, 0, 0, 72, 199, 132, 36, 224, 1, 0, 0, 0, 0, 0, 0, 72, 199, 132, 36, 216, 1, 0, 0, 0, 0, 0, 0, 72, 199, 132, 36, 208, 1, 0, 0, 0, 0, 0, 0, 72, 139, 71, 24, 72, 139, 79, 16, 72, 139, 23, 72, 139, 119, 8, 72, 137, 84, 36, 88, 72, 137, 116, 36, 96, 72, 137, 76, 36, 104, 72, 137, 68, 36, 112, 72, 199, 68, 36, 120, 0, 0, 0, 0, 72, 199, 132, 36, 128, 0, 0, 0, 0, 0, 0, 0, 72, 199, 132, 36, 136, 0, 0, 0, 0, 0, 0, 0, 72, 199, 132, 36, 144, 0, 0, 0, 0, 0, 0, 0]

def effect (s : RamState) : Effect :=
  { rip := 0x109fca
    writes := [⟨(.reg 0 : Operand 64),(.mem ((Operand.reg 7 : Operand 64).read s+24) : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64),(.mem ((Operand.reg 7 : Operand 64).read s+16) : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64),(.mem ((Operand.reg 7 : Operand 64).read s) : Operand 64).read s⟩,
      ⟨(.reg 6 : Operand 64),(.mem ((Operand.reg 7 : Operand 64).read s+8) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s+488) : Operand 64),0⟩,
      ⟨(.mem (rspOf s+480) : Operand 64),0⟩,
      ⟨(.mem (rspOf s+472) : Operand 64),0⟩,
      ⟨(.mem (rspOf s+464) : Operand 64),0⟩,
      ⟨(.mem (rspOf s+88) : Operand 64),(.mem ((Operand.reg 7 : Operand 64).read s) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s+96) : Operand 64),(.mem ((Operand.reg 7 : Operand 64).read s+8) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s+104) : Operand 64),(.mem ((Operand.reg 7 : Operand 64).read s+16) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s+112) : Operand 64),(.mem ((Operand.reg 7 : Operand 64).read s+24) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s+120) : Operand 64),0⟩,
      ⟨(.mem (rspOf s+128) : Operand 64),0⟩,
      ⟨(.mem (rspOf s+136) : Operand 64),0⟩,
      ⟨(.mem (rspOf s+144) : Operand 64),0⟩] }

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1200000 in
theorem inline_run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary InlinePre (codeRange 0x109f4a bytes) (Effect.post effect) := by
  advance_begin (mov_m64_imm32_effect_step 0x109f4a 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 488)) (by decide) rfl rfl 0)
  case pre =>
    intro s hp
    exact ⟨hp.rip,hp.writable 488 (by simp),hp.apart 488 (by simp) 0x9f4a 12 (by decide)⟩
  case av =>
    intro s hp
    apply Effect.avoids_codeRange
    intro c hc a len eq
    simp only [movM64Imm32Effect,storeEffect_components,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl
    · cases eq; exact hp.apart 488 (by simp) 0x9f4a 128 (by decide)
    · cases eq
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x9f56 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x109f56 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 480)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x109f4a bytes 12 12
  case mid =>
    intro s t hp hh ho
    refine ⟨StorePre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm; exact hp.writable 480 (by simp)
    · x86_norm; exact hp.apart 480 (by simp) 0x9f56 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.apart 480 (by simp) 0x9f4a 128 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x9f62 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x109f62 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 472)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x109f4a bytes 24 12
  case mid =>
    intro s t hp hh ho
    refine ⟨StorePre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm; exact hp.writable 472 (by simp)
    · x86_norm; exact hp.apart 472 (by simp) 0x9f62 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.apart 472 (by simp) 0x9f4a 128 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x9f6e (by decide))
  advance_then (mov_m64_imm32_effect_step 0x109f6e 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 464)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x109f4a bytes 36 12
  case mid =>
    intro s t hp hh ho
    refine ⟨StorePre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm; exact hp.writable 464 (by simp)
    · x86_norm; exact hp.apart 464 (by simp) 0x9f6e 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.apart 464 (by simp) 0x9f4a 128 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x9f7a (by decide))
  advance_then (mov_r64_m64_effect_step 0x109f7a 0x48 (by simp [RexWPrefix]) 0 (.base 7 (.d8 24)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x109f4a bytes 48 4
  case mid =>
    intro s t hp hh ho
    refine ⟨LoadPre.of_holds hh (ho true) (by x86_norm) ?_ ?_, Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
    · x86_addr_obs
    · x86_norm; exact hp.readable 24 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x9f7e (by decide))
  advance_then (mov_r64_m64_effect_step 0x109f7e 0x48 (by simp [RexWPrefix]) 1 (.base 7 (.d8 16)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x109f4a bytes 52 4
  case mid =>
    intro s t hp hh ho
    refine ⟨LoadPre.of_holds hh (ho true) (by x86_norm) ?_ ?_, Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
    · x86_addr_obs
    · x86_norm; exact hp.readable 16 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x9f82 (by decide))
  advance_then (mov_r64_m64_effect_step 0x109f82 0x48 (by simp [RexWPrefix]) 2 (.base 7 .none) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x109f4a bytes 56 3
  case mid =>
    intro s t hp hh ho
    refine ⟨LoadPre.of_holds hh (ho true) (by x86_norm) ?_ ?_, Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
    · x86_addr_obs
    · x86_norm; exact hp.readable 0 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x9f85 (by decide))
  advance_then (mov_r64_m64_effect_step 0x109f85 0x48 (by simp [RexWPrefix]) 6 (.base 7 (.d8 8)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x109f4a bytes 59 4
  case mid =>
    intro s t hp hh ho
    refine ⟨LoadPre.of_holds hh (ho true) (by x86_norm) ?_ ?_, Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
    · x86_addr_obs
    · x86_norm; exact hp.readable 8 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x9f89 (by decide))
  advance_then (mov_m64_r64_effect_step 0x109f89 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 88)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x109f4a bytes 63 5
  case mid =>
    intro s t hp hh ho
    refine ⟨StorePre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm; exact hp.writable 88 (by simp)
    · x86_norm; exact hp.apart 88 (by simp) 0x9f89 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.apart 88 (by simp) 0x9f4a 128 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x9f8e (by decide))
  advance_then (mov_m64_r64_effect_step 0x109f8e 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 96)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x109f4a bytes 68 5
  case mid =>
    intro s t hp hh ho
    refine ⟨StorePre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm; exact hp.writable 96 (by simp)
    · x86_norm; exact hp.apart 96 (by simp) 0x9f8e 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.apart 96 (by simp) 0x9f4a 128 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x9f93 (by decide))
  advance_then (mov_m64_r64_effect_step 0x109f93 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 104)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x109f4a bytes 73 5
  case mid =>
    intro s t hp hh ho
    refine ⟨StorePre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm; exact hp.writable 104 (by simp)
    · x86_norm; exact hp.apart 104 (by simp) 0x9f93 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.apart 104 (by simp) 0x9f4a 128 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x9f98 (by decide))
  advance_then (mov_m64_r64_effect_step 0x109f98 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 112)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x109f4a bytes 78 5
  case mid =>
    intro s t hp hh ho
    refine ⟨StorePre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm; exact hp.writable 112 (by simp)
    · x86_norm; exact hp.apart 112 (by simp) 0x9f98 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.apart 112 (by simp) 0x9f4a 128 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x9f9d (by decide))
  advance_then (mov_m64_imm32_effect_step 0x109f9d 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 120)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x109f4a bytes 83 9
  case mid =>
    intro s t hp hh ho
    refine ⟨StorePre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm; exact hp.writable 120 (by simp)
    · x86_norm; exact hp.apart 120 (by simp) 0x9f9d 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.apart 120 (by simp) 0x9f4a 128 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x9fa6 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x109fa6 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 128)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x109f4a bytes 92 12
  case mid =>
    intro s t hp hh ho
    refine ⟨StorePre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm; exact hp.writable 128 (by simp)
    · x86_norm; exact hp.apart 128 (by simp) 0x9fa6 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.apart 128 (by simp) 0x9f4a 128 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x9fb2 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x109fb2 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 136)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x109f4a bytes 104 12
  case mid =>
    intro s t hp hh ho
    refine ⟨StorePre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm; exact hp.writable 136 (by simp)
    · x86_norm; exact hp.apart 136 (by simp) 0x9fb2 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.apart 136 (by simp) 0x9f4a 128 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x9fbe (by decide))
  advance_then (mov_m64_imm32_effect_step 0x109fbe 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 144)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x109f4a bytes 116 12
  case mid =>
    intro s t hp hh ho
    refine ⟨StorePre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm; exact hp.writable 144 (by simp)
    · x86_norm; exact hp.apart 144 (by simp) 0x9fbe 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.apart 144 (by simp) 0x9f4a 128 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x9fca (by decide))
  apply AdvanceTriple.block_end
  intro s t hp hh
  have operand_write_mem_external (m : RamState) (a : BitVec 64) (v : BitVec 64) :
      ((Operand.mem a : Operand 64).write m v).external = memStore m.external a v := rfl
  have hread (mem : Ram) (i j : Nat) (v : BitVec 64)
      (hi : i ∈ ([464,472,480,488] : List Nat)) (hj : j ∈ ([0,8,16,24] : List Nat)) :
      memLoad (memStore mem (rspOf s+BitVec.ofNat 64 i) v)
        ((Operand.reg 7 : Operand 64).read s+BitVec.ofNat 64 j) 64 =
        memLoad mem ((Operand.reg 7 : Operand 64).read s+BitVec.ofNat 64 j) 64 := by
    apply P256.Proofs.Common.Field.Montgomery.Schoolbook.memLoad_memStore_rangeApart
    intro a ha b hb eq
    have apart := hp.inputApart i hi
    change RangeApart (rspOf s+BitVec.ofNat 64 i) 8 ((Operand.reg 7 : Operand 64).read s) 32 at apart
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


set_option maxRecDepth 2048 in
theorem call [Bindings] {initial s : RamState} {boundary : ReturnBoundary} {state : State}
    (pre : DrbgCalleePre initial boundary 0x109f30 1856 state)
    (input : Arguments initial s state) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ (effect s).Holds s t := by
  have hp : InlinePre s := by
    refine ⟨input.rip, ?_, ?_, ?_, ?_⟩
    · intro off member
      have bound : off + 8 ≤ 32 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at member; omega
      rw [show (Operand.reg 7 : Operand 64).read s = initial.regValue .rdi from input.source]
      have address : (initial.regValue .rdi + BitVec.ofNat 64 off).toNat = (initial.regValue .rdi).toNat + off := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : off < 2^64)]
        exact Nat.mod_eq_of_lt (by have h : (initial.regValue .rdi).toNat + 64 < 2^32 := pre.stateBounded; omega)
      refine ⟨?_, ?_⟩
      · rw [address]
        have h : (initial.regValue .rdi).toNat + 64 < 2^32 := pre.stateBounded
        omega
      · intro i hi
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
        exact input.allocated _ (Option.isSome_iff_exists.mpr (pre.stateAllocated _
          (memoryRegion_contains_add (len := 64) pre.stateBounded (Nat.le_refl _) (Nat.le_refl _) (by omega))))
    · intro off member
      have bound : off ≤ 632 ∧ (680-off)%8=0 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [show rspOf s = stackPtr s from rfl,
        ScalarFrame.scalar_stack_address (frameOffset := 680) input.rsp (by decide) (by omega)]
      exact writable_of_grow (stack_sub_writable8 pre.stack
        (fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp)) (by omega) bound.2) input.allocated
    · intro off member codeOffset codeLen codeBound
      have bound : off + 8 ≤ 632 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at member; omega
      exact ScalarFrame.stack_code (frameOffset := 680) pre.callee input.toFrameState (by decide) (by omega) codeBound
    · intro off member i hi j hj he
      have bound : off + 8 ≤ 632 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at member; omega
      rw [show (Operand.reg 7 : Operand 64).read s = initial.regValue .rdi from input.source] at he
      apply pre.separation _ (memoryRegion_contains_add pre.stateBounded (Nat.le_refl _) (Nat.le_refl _) (by omega : j<64))
      rw [← he]
      apply work_substack pre
      apply work_contains_scratch pre bound
      exact ⟨i, hi, by rw [show rspOf s = scratch initial from input.rsp]⟩
  obtain ⟨fuel,t,run,ready,_,holds⟩ := inline_run boundary pre.outerBoundary s
    (readyToStep input.machine input.bindingsSupported)
    (programText_slice (programLoaded_codeIn input.loaded) 0x9f4a bytes (by decide) (by decide +kernel)) hp
  exact ⟨fuel,t,run,ready,holds⟩

end P256.Proofs.Nonce.Update.Prepare.Key
