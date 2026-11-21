import P256.Proofs.Nonce.Fill.Entry.ScaleBits
import P256.Proofs.Nonce.Fill.Work
import P256.Proofs.Common.Instructions.CrossPageStore
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Entry

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field

attribute [local x86_compose] P256.Proofs.Common.Instructions.Lea32.leaR32NoBaseEffect

structure SetupPre (s : RamState) : Prop where
  rip : s.RIP = 0x10735a
  writable : ∀ off ∈ ([56,144,136,64,48] : List Nat), MemWritable s (stackPtr s + BitVec.ofNat 64 off) 8
  apart : ∀ off ∈ ([56,144,136,64,48] : List Nat), ∀ co cl : Nat, co + cl ≤ 118431 →
    RangeApart (stackPtr s + BitVec.ofNat 64 off) 8 (Extracted.textAddress + BitVec.ofNat 64 co) cl

def setupBytes : List UInt8 :=
  [66, 141, 4, 237, 0, 0, 0, 0, 137, 68, 36, 56, 72, 137, 188, 36, 144, 0, 0, 0, 72, 141, 71, 40, 72, 137, 132, 36, 136, 0, 0, 0, 72, 137, 207, 72, 137, 76, 36, 64, 76, 137, 108, 36, 48]

def setupEffect (s : RamState) : Effect :=
  { rip := 0x107387
    writes := [⟨(.reg 0 : Operand 64), s.regValue .rdi + 40⟩,
      ⟨(.mem (stackPtr s + 56) : Operand 32), (s.regValue .r13 <<< (3 : Nat)).setWidth 32⟩,
      ⟨(.mem (stackPtr s + 144) : Operand 64), s.regValue .rdi⟩,
      ⟨(.mem (stackPtr s + 136) : Operand 64), s.regValue .rdi + 40⟩,
      ⟨(.reg 7 : Operand 64), s.regValue .rcx⟩,
      ⟨(.mem (stackPtr s + 64) : Operand 64), s.regValue .rcx⟩,
      ⟨(.mem (stackPtr s + 48) : Operand 64), s.regValue .r13⟩] }

theorem setup_block [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary SetupPre (codeRange 0x10735a setupBytes) (Effect.post setupEffect) := by
  advance_begin (lea_eax_r13_scale8_effect_step 0x10735a)
  case next => intro s h; exact boundary_ne_program outside (inProgram_of_textOffset 0x7362 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m32_r32_legacy_effect_step_any 0x107362 0 (.sib 4 none 0 (.d8 56)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10735a setupBytes 8 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      change P256.Proofs.Common.Instructions.CrossPageStore.Writable s (stackPtr s + 56) 4
      have w := hP.writable 56 (by simp)
      have low : (stackPtr s + 56).toNat + 8 ≤ 2^32 := w.low
      exact ⟨⟨by omega, fun i hi => w.mem i (by omega)⟩,
        w.tables.sub (Nat.le_refl _) (Nat.add_le_add_left (by decide : 4 ≤ 8) _)⟩
    · x86_norm
      intro i hi j hj
      exact hP.apart 56 (by simp) 0x7362 4 (by decide) i (by omega) j hj
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      intro i hi j hj
      exact hP.apart 56 (by simp) 0x735a 45 (by decide) i (by omega) j hj
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x7366 (by decide))
  advance_then (mov_m64_r64_effect_step 0x107366 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 144)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10735a setupBytes 12 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 144 (by simp)
    · x86_norm
      exact hP.apart 144 (by simp) 0x7366 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 144 (by simp) 0x735a 45 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x736e (by decide))
  advance_then (lea_r64_effect_step 0x10736e 0x48 (by simp [RexWPrefix]) 0 (.base 7 (.d8 40)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10735a setupBytes 20 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x7372 (by decide))⟩
  advance_then (mov_m64_r64_effect_step 0x107372 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 136)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10735a setupBytes 24 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 136 (by simp)
    · x86_norm
      exact hP.apart 136 (by simp) 0x7372 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 136 (by simp) 0x735a 45 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x737a (by decide))
  advance_then (mov_r64_r64_effect_step 0x10737a 0x48 0xcf (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10735a setupBytes 32 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x737d (by decide))⟩
  advance_then (mov_m64_r64_effect_step 0x10737d 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 64)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10735a setupBytes 35 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 64 (by simp)
    · x86_norm
      exact hP.apart 64 (by simp) 0x737d 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 64 (by simp) 0x735a 45 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x7382 (by decide))
  advance_then (mov_m64_r64_effect_step 0x107382 0x4c (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8 48)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10735a setupBytes 40 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 48 (by simp)
    · x86_norm
      exact hP.apart 48 (by simp) 0x7382 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 48 (by simp) 0x735a 45 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x7387 (by decide))
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [setupEffect]
  · x86_norm [setupEffect, P256.Proofs.Common.Instructions.Lea32.leaR32NoBaseEffect]
    simp only [Operand.read_reg64, State.regValue, gprNumber, gprIndex, rexR, rexB,
      modrmReg, modrmRm, Syntax.Reg.fin, BitVec.add_zero]
    simp only [Int.reduceToNat, Fin.isValue, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
      Fin.reduceFinMk, Fin.getElem_fin, Nat.reduceLeDiff, BitVec.setWidth_shiftLeft_of_le,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, Write.mk.injEq, Nat.reduceEqDiff,
      false_and, BitVec.add_left_inj, false_or, Nat.pow_one, Nat.zero_mod, Nat.zero_shiftLeft,
      UInt8.toBitVec_ofNat, BitVec.reduceExtractLsb', Nat.add_zero, Nat.mod_succ, Nat.zero_add,
      Nat.one_mod, Fin.mk_one, Nat.reduceAdd, Fin.val_one, Nat.reduceShiftLeft, or_self, or_false,
      or_true, true_and, and_self_left]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · intro flag; cases flag <;> x86_norm [setupEffect]
  · x86_norm [setupEffect, stackPtr, Operand.read_reg64, State.regValue]

end P256.Proofs.Nonce.Fill.Entry
