import Hkdf.Proofs.Standard.Update.State
import Hkdf.Proofs.Standard.Memory
import Hkdf.Proofs.Common.Streaming
import Hkdf.Proofs.Wrapper.Absorb.Mathematics
import Hkdf.Proofs.Wrapper.Absorb.Arithmetic
import X86Proofs.Instructions.Test.Generated.RR.Triple
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import Hkdf.Proofs.Common.Instructions.MemoryAlu.Inc
import Hkdf.Proofs.Common.Instructions.ByteStore
import Hkdf.Proofs.Standard.Update
import Hkdf.Proofs.Common.Instructions.MemoryAlu.Add

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Update

open Hkdf.Spec Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.Field (AdvanceTriple)
open Hkdf.Proofs.Common.Instructions.MemoryAlu

theorem select_blocks [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip) (empty : Bool)
    (rip : s.RIP = if empty then 0x101719 else 0x1016b9) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      t.RIP = (if (s.regValue .rbp).toNat / 64 = 0 then 0x1016da else 0x1016c2) ∧
      t.regValue .rdx = BitVec.ofNat 64 ((s.regValue .rbp).toNat / 64) ∧
      AgreesExcept [.reg 2, .flags, .rip] s t := by
  let pc : BitVec 64 := if empty then 0x101719 else 0x1016b9
  obtain ⟨u, first, readyU, moved⟩ :=
    (mov_r64_r64_effect_step pc 0x48 0xea (by simp [RexWPrefix]) rfl).advances ready
      (by cases empty
          · exact programText_slice (programLoaded_codeIn loaded) 0x16b9 _
              (by decide) (by decide +kernel)
          · exact programText_slice (programLoaded_codeIn loaded) 0x1719 _
              (by decide) (by decide +kernel)) rip
      (by cases empty
          · exact boundary_ne_program outside (inProgram_of_textOffset 0x16bc (by decide))
          · exact boundary_ne_program outside (inProgram_of_textOffset 0x171c (by decide)))
  have frame1 : AgreesExcept [.reg 2, .rip] s u := moved.agrees
  have rdx : u.regValue .rdx = s.regValue .rbp := moved.writes
  have codeU := frame1.codeIn (by simp [Component.Covers]) (programLoaded_codeIn loaded)
  obtain ⟨v, second, readyV, shifted⟩ :=
    (shr_r64_imm8_effect_step (pc + 3) 0x48 0xea 6
      (by simp [RexWPrefix]) rfl rfl).advances readyU
      (by cases empty
          · exact programText_slice codeU 0x16bc _ (by decide) (by decide +kernel)
          · exact programText_slice codeU 0x171c _ (by decide) (by decide +kernel)) moved.rip
      (by cases empty
          · exact boundary_ne_program outside (inProgram_of_textOffset 0x16c0 (by decide))
          · exact boundary_ne_program outside (inProgram_of_textOffset 0x1720 (by decide)))
  have frame2 : AgreesExcept [.reg 2, .flags, .rip] u v := shifted.agrees
  have count : v.regValue .rdx = BitVec.ofNat 64 ((s.regValue .rbp).toNat / 64) := by
    have value := shifted.writes
    change v.regValue .rdx = u.regValue .rdx >>> 6 at value
    rw [rdx, Hkdf.Proofs.Wrapper.Absorb.block_count] at value
    exact value
  have zf : (StatusFlags.ofRFLAGS v.RFLAGS).ZF =
      decide ((s.regValue .rbp).toNat / 64 = 0) := by
    rw [shifted.flags.2.2.2.1]
    change (u.regValue .rdx >>> 6 == 0) = _
    rw [rdx, Hkdf.Proofs.Wrapper.Absorb.block_count]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    constructor
    · intro h
      have hn := congrArg BitVec.toNat h
      have bound := BitVec.isLt (s.regValue .rbp)
      change ((s.regValue .rbp).toNat / 64) % 2^64 = 0 at hn
      omega
    · intro h
      rw [h]
      rfl
  have codeV := frame2.codeIn (by simp [Component.Covers]) codeU
  obtain ⟨w, step, readyW, jumped⟩ := jcc_rel8_effect_step (pc + 7)
    (if empty then 5 else 4) (if empty then 0xa0 else 0x18) v readyV
    (by cases empty
        · exact programText_slice codeV 0x16c0 _ (by decide) (by decide +kernel)
        · exact programText_slice codeV 0x1720 _ (by decide) (by decide +kernel))
    ⟨shifted.rip.trans (by cases empty <;> rfl),
      by cases empty <;> exact fun _ ↦ by decide⟩
  have target : w.RIP = if (s.regValue .rbp).toNat / 64 = 0
      then (if empty then 0x101722 else 0x1016da) else 0x1016c2 := by
    have destination : branchTarget (pc + 7) 2
        (BitVec.signExtend 64 (if empty then (0xa0 : BitVec 8) else 0x18)) =
        (if empty then 0x1016c2 else 0x1016da) := by
      cases empty <;> decide +kernel
    have fallthrough : pc + 7 + BitVec.ofNat 64 2 =
        (if empty then 0x101722 else 0x1016c2) := by
      cases empty <;> decide +kernel
    rw [jumped.rip]
    change (if condHolds (if empty then 5 else 4) (StatusFlags.ofRFLAGS v.RFLAGS)
      then branchTarget (pc + 7) 2
        (BitVec.signExtend 64 (if empty then (0xa0 : BitVec 8) else 0x18))
      else pc + 7 + BitVec.ofNat 64 2) = _
    rw [destination, fallthrough]
    cases empty
    · change (if (StatusFlags.ofRFLAGS v.RFLAGS).ZF then 0x1016da else 0x1016c2) = _
      rw [zf]
      simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq]
    · change (if !(StatusFlags.ofRFLAGS v.RFLAGS).ZF then 0x1016c2 else 0x101722) = _
      rw [zf]
      by_cases zero : (s.regValue .rbp).toNat / 64 = 0 <;> simp only [zero,
        decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.false_eq_true,
        ↓reduceIte]
  have third : Advances boundary 1 v w := by
    apply Advances.of_step step
    left
    rw [target]
    split
    · cases empty
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x16da (by decide))
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x1722 (by decide))
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x16c2 (by decide))
  have fullFrame : AgreesExcept [.reg 2, .flags, .rip] s w :=
    ((frame1.trans frame2).trans jumped.agrees).mono (by
      simp [jccEffect, branchEffect_components])
  have countW : w.regValue .rdx = BitVec.ofNat 64 ((s.regValue .rbp).toNat / 64) :=
    (jumped.agrees.read (n := 64) (r := 2) (by simp [jccEffect])).trans count
  by_cases skip : empty = true ∧ (s.regValue .rbp).toNat / 64 = 0
  · obtain ⟨isEmpty, zero⟩ := skip
    have ripW : w.RIP = 0x101722 := by simpa only [zero, isEmpty, ↓reduceIte] using target
    have codeW := fullFrame.codeIn (by simp [Component.Covers]) (programLoaded_codeIn loaded)
    obtain ⟨t, fourth, readyT, jump⟩ :=
      (jmp_rel8_effect_step 0x101722 0xb6 (by decide)).advances readyW
        (programText_slice codeW 0x1722 _ (by decide) (by decide +kernel)) ripW
        (boundary_ne_program outside (inProgram_of_textOffset 0x16da (by decide)))
    refine ⟨4, t, (first.trans second).trans (third.trans fourth), readyT, ?_, ?_, ?_⟩
    · simpa only [zero, ↓reduceIte] using (show t.RIP = 0x1016da from jump.rip)
    · exact (jump.agrees.read (n := 64) (r := 2) (by simp [jmpEffect, Effect.components])).trans countW
    · exact (fullFrame.trans jump.agrees).mono (by simp [jmpEffect, Effect.components])
  · refine ⟨3, w, first.trans (second.trans third), readyW, ?_, countW, fullFrame⟩
    rw [target]
    by_cases zero : (s.regValue .rbp).toNat / 64 = 0
    · have notEmpty : empty = false := by cases empty <;> simp_all
      simp only [zero, notEmpty, Bool.false_eq_true, ↓reduceIte]
    · simp only [zero, ↓reduceIte]


def tailRegisterBytes : List UInt8 :=
  [0x48,0x89,0xe8,0x48,0xb9,0xc0,0xff,0xff,0xff,0xff,0xff,0xff,0x7f,
   0x48,0x21,0xc8,0x83,0xe5,0x3f,0x49,0x01,0xc5]

def tailRegisterEffect (s : RamState) : Effect :=
  { rip := 0x1016f0
    writes := [⟨(.reg 0 : Operand 64), 0x7fffffffffffffc0 &&& s.regValue .rbp⟩,
      ⟨(.reg 1 : Operand 64), 0x7fffffffffffffc0⟩,
      ⟨(.reg 5 : Operand 64), ((s.regValue .rbp).setWidth 32 &&& 63).setWidth 64⟩,
      ⟨(.reg 13 : Operand 64), s.regValue .r13 + (0x7fffffffffffffc0 &&& s.regValue .rbp)⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

theorem tail_registers [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1016da)
      (codeRange 0x1016da tailRegisterBytes) (Effect.post tailRegisterEffect) := by
  advance_begin (mov_r64_r64_effect_step 0x1016da 0x48 0xe8 (by simp [RexWPrefix]) rfl)
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0x16dd (by decide))
  advance_then (mov_r64_imm64_effect_step 0x1016dd 0x48 0xb9 (by simp [RexWPrefix]) (by decide) 0x7fffffffffffffc0)
  case sub => exact codeRange_slice_subset 0x1016da tailRegisterBytes 3 10
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x16e7 (by decide))⟩
  advance_then (and_r64_r64_effect_step 0x1016e7 0x48 0xc8 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1016da tailRegisterBytes 13 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x16ea (by decide))⟩
  advance_then (and_r32_imm8_effect_step 0x1016ea 0xe5 63 rfl rfl)
  case sub => exact codeRange_slice_subset 0x1016da tailRegisterBytes 16 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x16ed (by decide))⟩
  advance_then (add_r64_r64_effect_step 0x1016ed 0x49 0xc5 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1016da tailRegisterBytes 19 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x16f0 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hp hh
  apply hh.weaken
  · x86_norm [tailRegisterEffect, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq, BitVec.and_comm]
    all_goals solve_by_elim (maxDepth := 30) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [tailRegisterEffect, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq, BitVec.and_comm]
    all_goals solve_by_elim (maxDepth := 30) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> exact Or.inl rfl
  · x86_norm [tailRegisterEffect]
    all_goals solve_by_elim (maxDepth := 30) only [And.intro, Or.inl, Or.inr, Eq.refl]

def tailBytes : List UInt8 :=
  [0x40,0x88,0xac,0x24,0xb7,0,0,0,0x48,0x8d,0x7c,0x24,0x78,
    0x4c,0x89,0xee,0x48,0x89,0xea]

def tailEffect (s : RamState) : Effect :=
  { rip := 0x101703
    writes := [⟨(.mem (rspOf s + 183) : Operand 8), (Operand.reg 5 : Operand 8).read s⟩,
      ⟨(.reg 7 : Operand 64), rspOf s + 120⟩,
      ⟨(.reg 6 : Operand 64), (Operand.reg 13 : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (Operand.reg 5 : Operand 64).read s⟩] }

theorem tail_setup [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s ↦ s.RIP = 0x1016f0 ∧
      MemWritable s (rspOf s+183) 1 ∧ RangeApart (rspOf s+183) 1 0x1016f0 19)
      (codeRange 0x1016f0 tailBytes) (Effect.post tailEffect) := by
  advance_begin (Hkdf.Proofs.Common.Instructions.mov_m8_r8_effect_step 0x1016f0 0x40
    (by simp [RexPrefix]) 5 (.sib 4 none 0 (.d32 183)) (by decide) rfl rfl)
  case pre =>
    intro s h
    refine ⟨h.1, h.2.1, ?_⟩
    intro i hi j hj
    exact h.2.2 i hi j (by simp [AddrMode.tail, Disp.bytes] at hj; omega)
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm
    exact h.2.2
  case next =>
    exact fun _ _ ↦ boundary_ne_program outside (inProgram_of_textOffset 0x16f8 (by decide))
  advance_then (lea_r64_effect_step 0x1016f8 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d8 120)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1016f0 tailBytes 8 5
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x16fd (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x1016fd 0x4c 0xee (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1016f0 tailBytes 13 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x1700 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x101700 0x48 0xea (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1016f0 tailBytes 16 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x1703 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hp hh
  apply hh.weaken
  · x86_norm [tailEffect]
    all_goals solve_by_elim (maxDepth := 30) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [tailEffect]
    all_goals solve_by_elim (maxDepth := 30) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [tailEffect]
  · x86_norm [tailEffect]
    all_goals solve_by_elim (maxDepth := 30) only [And.intro, Or.inl, Or.inr, Eq.refl]

def bulkBytes : List UInt8 :=
  [0x48,0x01,0x94,0x24,0xd8,0,0,0,0x48,0x8d,0xbc,0x24,0xb8,0,0,0,0x4c,0x89,0xee]

def bulkEffect (s : RamState) : Effect :=
  { rip := 0x1016d5
    writes := [⟨(.mem (rspOf s+216) : Operand 64),
        memLoad s.external (rspOf s+216) 64 + (Operand.reg 2 : Operand 64).read s⟩,
      ⟨(.reg 7 : Operand 64), rspOf s+184⟩,
      ⟨(.reg 6 : Operand 64), (Operand.reg 13 : Operand 64).read s⟩]
    flags := some (.ofStatusFlags (addSpec (memLoad s.external (rspOf s+216) 64)
      ((Operand.reg 2 : Operand 64).read s)).2) }

theorem bulk_setup [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s ↦ s.RIP = 0x1016c2 ∧
      MemWritable s (rspOf s+216) 8 ∧ RangeApart (rspOf s+216) 8 0x1016c2 19)
      (codeRange 0x1016c2 bulkBytes) (Effect.post bulkEffect) := by
  advance_begin (add_m64_r64_effect_step 0x1016c2 0x48 (by simp [RexWPrefix]) 2
    (.sib 4 none 0 (.d32 216)) (by decide) rfl rfl)
  case pre =>
    intro s h
    refine ⟨h.1, h.2.1, ?_⟩
    intro i hi j hj
    exact h.2.2 i hi j (by simp [AddrMode.tail, Disp.bytes] at hj; omega)
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm [addM64R64Effect]
    exact h.2.2
  case next =>
    exact fun _ _ ↦ boundary_ne_program outside (inProgram_of_textOffset 0x16ca (by decide))
  advance_then (lea_r64_effect_step 0x1016ca 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d32 184)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1016c2 bulkBytes 8 8
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x16d2 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x1016d2 0x4c 0xee (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1016c2 bulkBytes 16 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x16d5 (by decide))⟩
  advance_finish [bulkEffect, addM64R64Effect]

end Hkdf.Proofs.Standard.Update
