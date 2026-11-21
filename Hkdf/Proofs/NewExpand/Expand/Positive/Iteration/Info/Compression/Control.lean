import Hkdf.Proofs.Common.Field.Operations.Run.Compose
import Hkdf.Proofs.Common.Machine.Code
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import X86Proofs.Instructions.Add.Generated.MR.Triple
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Inc.Generated.M.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Info

open Hkdf.Spec.Program Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.Field (AdvanceTriple)
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

local macro "control_next " offset:num " against " outside:term : tactic => `(tactic| (
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program $outside (inProgram_of_textOffset $offset (by decide))⟩))

private def fillBytes : List UInt8 :=
  [0x48,0x8d,0x2c,0x13, 0x4a,0x8d,0x3c,0x34, 0x48,0x81,0xc7,0x10,1,0,0, 0x48,0x89,0xde]

def fillEffect (s : RamState) : Effect :=
  let base := rspOf s + (Operand.reg 14 : Operand 64).read s
  let source := (Operand.reg 3 : Operand 64).read s
  { rip := 0x10f75d
    writes := [⟨(.reg 5 : Operand 64), source + (Operand.reg 2 : Operand 64).read s⟩,
      ⟨(.reg 7 : Operand 64), base + 272⟩, ⟨(.reg 6 : Operand 64), source⟩]
    flags := some (.ofStatusFlags (addSpec base 272).2) }

private theorem fillRun [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s ↦ s.RIP = 0x10f74b) (codeRange 0x10f74b fillBytes)
      (Effect.post fillEffect) := by
  advance_begin (lea_r64_effect_step 0x10f74b 0x48 (by simp [RexWPrefix]) 5
    (.sib 3 (some 2) 0 .none) (by decide) rfl rfl)
  case next => exact fun _ _ ↦ boundary_ne_program outside (inProgram_of_textOffset 0xf74f (by decide))
  advance_then (lea_r64_effect_step 0x10f74f 0x4a (by simp [RexWPrefix]) 7
    (.sib 4 (some 14) 0 .none) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f74b fillBytes 4 4
  control_next 0xf753 against outside
  advance_then (add_r64_imm32_effect_step 0x10f753 0x48 0xc7 272 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f74b fillBytes 8 7
  control_next 0xf75a against outside
  advance_then (mov_r64_r64_effect_step 0x10f75a 0x48 0xde (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10f74b fillBytes 15 3
  control_next 0xf75d against outside
  advance_finish [fillEffect, BitVec.shiftLeft_zero, BitVec.add_zero, BitVec.add_assoc]

theorem fillArguments [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (outside : ¬ InProgram boundary.rip)
    (pc : s.RIP = 0x10f74b) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ (fillEffect s).Holds s t := by
  have code := programText_slice (programLoaded_codeIn loaded) 0xf74b fillBytes
    (by decide) (by decide +kernel)
  obtain ⟨fuel, t, run, rt, _, effect⟩ := fillRun boundary outside s ready code pc
  exact ⟨fuel, t, run, rt, effect⟩

private def filledBytes : List UInt8 :=
  [0x48,0xff,0x84,0x24,0x70,1,0,0, 0xba,1,0,0,0,
    0x48,0x8d,0xbc,0x24,0x50,1,0,0, 0x48,0x8d,0xb4,0x24,0x10,1,0,0]

def filledEffect (s : RamState) : Effect :=
  let addr := rspOf s + 368
  let old := (Operand.mem addr : Operand 64).read s
  { rip := 0x10f77d
    writes := [⟨(.mem addr : Operand 64), old + 1⟩,
      ⟨(.reg 2 : Operand 64), 1⟩, ⟨(.reg 7 : Operand 64), rspOf s + 336⟩,
      ⟨(.reg 6 : Operand 64), rspOf s + 272⟩]
    flags := some (.ofStatusFlags (incSpec (StatusFlags.ofRFLAGS s.RFLAGS) old).2) }

private theorem filledRun [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s ↦ s.RIP = 0x10f760 ∧ MemWritable s (rspOf s + 368) 8 ∧
      RangeApart (rspOf s + 368) 8 0x10f760 29) (codeRange 0x10f760 filledBytes)
      (Effect.post filledEffect) := by
  advance_begin (inc_m64_effect_step 0x10f760 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d32 368)) (by decide) rfl rfl)
  case pre =>
    intro s h
    exact ⟨h.1, h.2.1, h.2.2.sub0 8 (by decide)⟩
  case av =>
    intro s h
    have apart := h.2.2
    x86_avoid
  case next => exact fun _ _ ↦ boundary_ne_program outside (inProgram_of_textOffset 0xf768 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10f768 0xba (by decide) 1)
  case sub => exact codeRange_slice_subset 0x10f760 filledBytes 8 5
  control_next 0xf76d against outside
  advance_then (lea_r64_effect_step 0x10f76d 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d32 336)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f760 filledBytes 13 8
  control_next 0xf775 against outside
  advance_then (lea_r64_effect_step 0x10f775 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d32 272)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f760 filledBytes 21 8
  control_next 0xf77d against outside
  advance_finish [filledEffect, incMEffect, BitVec.add_zero]

theorem filledArguments [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (outside : ¬ InProgram boundary.rip)
    (pc : s.RIP = 0x10f760) (writable : MemWritable s (rspOf s + 368) 8)
    (apart : RangeApart (rspOf s + 368) 8 0x10f760 29) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ (filledEffect s).Holds s t := by
  have code := programText_slice (programLoaded_codeIn loaded) 0xf760 filledBytes
    (by decide) (by decide +kernel)
  obtain ⟨fuel, t, run, rt, _, effect⟩ :=
    filledRun boundary outside s ready code ⟨pc, writable, apart⟩
  exact ⟨fuel, t, run, rt, effect⟩

private def bulkBytes : List UInt8 :=
  [0x48,0x01,0x94,0x24,0x70,1,0,0, 0x48,0x8d,0xbc,0x24,0x50,1,0,0, 0x48,0x89,0xde]

def bulkEffect (s : RamState) : Effect :=
  let addr := rspOf s + 368
  let old := (Operand.mem addr : Operand 64).read s
  { rip := 0x10f7a9
    writes := [⟨(.mem addr : Operand 64), old + (Operand.reg 2 : Operand 64).read s⟩,
      ⟨(.reg 7 : Operand 64), rspOf s + 336⟩, ⟨(.reg 6 : Operand 64), (Operand.reg 3 : Operand 64).read s⟩]
    flags := some (.ofStatusFlags (addSpec old ((Operand.reg 2 : Operand 64).read s)).2) }

private theorem bulkRun [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s ↦ s.RIP = 0x10f796 ∧ MemWritable s (rspOf s + 368) 8 ∧
      RangeApart (rspOf s + 368) 8 0x10f796 19) (codeRange 0x10f796 bulkBytes)
      (Effect.post bulkEffect) := by
  advance_begin (add_m64_r64_effect_step 0x10f796 0x48 (by simp [RexWPrefix]) 2
    (.sib 4 none 0 (.d32 368)) (by decide) rfl rfl)
  case pre =>
    intro s h
    exact ⟨h.1, h.2.1, h.2.2.sub0 8 (by decide)⟩
  case av =>
    intro s h
    have apart := h.2.2
    x86_avoid
  case next => exact fun _ _ ↦ boundary_ne_program outside (inProgram_of_textOffset 0xf79e (by decide))
  advance_then (lea_r64_effect_step 0x10f79e 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d32 336)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f796 bulkBytes 8 8
  control_next 0xf7a6 against outside
  advance_then (mov_r64_r64_effect_step 0x10f7a6 0x48 0xde (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10f796 bulkBytes 16 3
  control_next 0xf7a9 against outside
  advance_finish [bulkEffect, addMREffect, BitVec.add_zero]

theorem bulkArguments [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (outside : ¬ InProgram boundary.rip)
    (pc : s.RIP = 0x10f796) (writable : MemWritable s (rspOf s + 368) 8)
    (apart : RangeApart (rspOf s + 368) 8 0x10f796 19) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ (bulkEffect s).Holds s t := by
  have code := programText_slice (programLoaded_codeIn loaded) 0xf796 bulkBytes
    (by decide) (by decide +kernel)
  obtain ⟨fuel, t, run, rt, _, effect⟩ :=
    bulkRun boundary outside s ready code ⟨pc, writable, apart⟩
  exact ⟨fuel, t, run, rt, effect⟩

private theorem zeroBlocks (n : BitVec 64) : ((n >>> 6) == 0) = decide (n.toNat < 64) := by
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  change n.toNat / 64 = 0 ↔ n.toNat < 64
  omega

private def bufferedBytes : List UInt8 :=
  [0xc6,0x84,0x24,0x4f,1,0,0,0, 0x48,0x89,0xeb, 0x4c,0x89,0xfa, 0x48,0xc1,0xea,6, 0x74,0x18]

def bufferedEffect (s : RamState) : Effect :=
  let n := (Operand.reg 15 : Operand 64).read s
  { rip := if n.toNat < 64 then 0x10f7ae else 0x10f796
    writes := [⟨(.mem (rspOf s + 335) : Operand 8), 0⟩,
      ⟨(.reg 3 : Operand 64), (Operand.reg 5 : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), n >>> 6⟩]
    flags := some (shrFlags (StatusFlags.ofRFLAGS s.RFLAGS) 6 n) }

private theorem bufferedRun [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s ↦ s.RIP = 0x10f782 ∧ MemWritable s (rspOf s + 335) 1 ∧
      RangeApart (rspOf s + 335) 1 0x10f782 20) (codeRange 0x10f782 bufferedBytes)
      (Effect.post (fun s ↦ { bufferedEffect s with rip := 0x10f794 })) := by
  advance_begin (mov_m8_imm8_effect_step 0x10f782 (.sib 4 none 0 (.d32 335)) (by decide) rfl rfl 0)
  case pre =>
    intro s h
    exact ⟨h.1, h.2.1, h.2.2.sub0 8 (by decide)⟩
  case av =>
    intro s h
    have apart := h.2.2
    x86_avoid
  case next => exact fun _ _ ↦ boundary_ne_program outside (inProgram_of_textOffset 0xf78a (by decide))
  advance_then (mov_r64_r64_effect_step 0x10f78a 0x48 0xeb (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10f782 bufferedBytes 8 3
  control_next 0xf78d against outside
  advance_then (mov_r64_r64_effect_step 0x10f78d 0x4c 0xfa (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10f782 bufferedBytes 11 3
  control_next 0xf790 against outside
  advance_then (shr_r64_imm8_effect_step 0x10f790 0x48 0xea 6 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f782 bufferedBytes 14 4
  control_next 0xf794 against outside
  apply AdvanceTriple.block_end
  intro s t _ effect
  x86_norm [bufferedEffect] at effect ⊢
  exact effect

theorem bufferedDispatch [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (outside : ¬ InProgram boundary.rip)
    (pc : s.RIP = 0x10f782) (writable : MemWritable s (rspOf s + 335) 1)
    (apart : RangeApart (rspOf s + 335) 1 0x10f782 20) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ (bufferedEffect s).Holds s t := by
  have code := programText_slice (programLoaded_codeIn loaded) 0xf782 bufferedBytes
    (by decide) (by decide +kernel)
  obtain ⟨fuel, u, run, ru, codeU, effect⟩ :=
    bufferedRun boundary outside s ready code ⟨pc, writable, apart⟩
  obtain ⟨t, step, rt, branch⟩ := jcc_rel8_effect_step 0x10f794 4 0x18 u ru
    (codeU.mono (codeRange_slice_subset 0x10f782 bufferedBytes 18 2))
    ⟨effect.rip, fun _ ↦ by decide⟩
  have zf : (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
      (((Operand.reg 15 : Operand 64).read s >>> 6) == 0) := effect.flags.2.2.2.1
  have target : t.RIP = (bufferedEffect s).rip := by
    rw [branch.rip]
    simp only [jccEffect, branchEffect, condHolds_4, zf, zeroBlocks, decide_eq_true_eq]
    rfl
  have next : t.RIP ≠ boundary.rip := by
    rw [target]
    change (if ((Operand.reg 15 : Operand 64).read s).toNat < 64 then 0x10f7ae else 0x10f796) ≠
      boundary.rip
    split
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf7ae (by decide))
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf796 (by decide))
  have ag : AgreesExcept [.rip] u t := branch.agrees
  have ext := ag.external (by simp [Component.Covers])
  have flags := ag.rflags (by decide) (by decide)
  have buffer : (Operand.mem (rspOf s + 335) : Operand 8).read t =
      (Operand.mem (rspOf s + 335) : Operand 8).read u := congrArg (fun m ↦ memLoad m _ 8) ext
  refine ⟨_, t, run.trans (Advances.of_step step (.inl next)), rt, target, ?_, ?_, ?_⟩
  · exact ⟨buffer.trans effect.writes.1, (ag.read (by decide)).trans effect.writes.2.1,
      (ag.read (by decide)).trans effect.writes.2.2⟩
  · change (bufferedEffect s).FlagsHold t
    unfold Effect.FlagsHold
    rw [flags]
    exact effect.flags
  · exact (effect.agrees.trans ag).mono (by simp [bufferedEffect, Effect.components])

private def alignedBytes : List UInt8 :=
  [0x49,0x89,0xef, 0x4c,0x89,0xfa, 0x48,0xc1,0xea,6, 0x75,0x95]

def alignedEffect (s : RamState) : Effect :=
  let n := (Operand.reg 5 : Operand 64).read s
  { rip := 0x10f796
    writes := [⟨(.reg 15 : Operand 64), n⟩, ⟨(.reg 2 : Operand 64), n >>> 6⟩]
    flags := some (shrFlags (StatusFlags.ofRFLAGS s.RFLAGS) 6 n) }

private theorem alignedRun [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s ↦ s.RIP = 0x10f7f5) (codeRange 0x10f7f5 alignedBytes)
      (Effect.post (fun s ↦ { alignedEffect s with rip := 0x10f7ff })) := by
  advance_begin (mov_r64_r64_effect_step 0x10f7f5 0x49 0xef (by simp [RexWPrefix]) rfl)
  case next => exact fun _ _ ↦ boundary_ne_program outside (inProgram_of_textOffset 0xf7f8 (by decide))
  advance_then (mov_r64_r64_effect_step 0x10f7f8 0x4c 0xfa (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10f7f5 alignedBytes 3 3
  control_next 0xf7fb against outside
  advance_then (shr_r64_imm8_effect_step 0x10f7fb 0x48 0xea 6 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f7f5 alignedBytes 6 4
  control_next 0xf7ff against outside
  advance_finish [alignedEffect]

theorem alignedDispatch [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (outside : ¬ InProgram boundary.rip)
    (pc : s.RIP = 0x10f7f5) (long : 64 ≤ (s.regValue .rbp).toNat) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ (alignedEffect s).Holds s t := by
  have code := programText_slice (programLoaded_codeIn loaded) 0xf7f5 alignedBytes
    (by decide) (by decide +kernel)
  obtain ⟨fuel, u, run, ru, codeU, effect⟩ := alignedRun boundary outside s ready code pc
  obtain ⟨t, step, rt, branch⟩ := jcc_rel8_effect_step 0x10f7ff 5 0x95 u ru
    (codeU.mono (codeRange_slice_subset 0x10f7f5 alignedBytes 10 2))
    ⟨effect.rip, fun _ ↦ by decide⟩
  have zf : (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
      (((Operand.reg 5 : Operand 64).read s >>> 6) == 0) := effect.flags.2.2.2.1
  have notSmall : ¬ ((Operand.reg 5 : Operand 64).read s).toNat < 64 :=
    Nat.not_lt.mpr long
  have target : t.RIP = 0x10f796 := by
    rw [branch.rip]
    simp only [jccEffect, branchEffect, condHolds_5, zf, zeroBlocks, notSmall,
      decide_false, Bool.not_false, ↓reduceIte]
    rfl
  have next : t.RIP ≠ boundary.rip :=
    target ▸ boundary_ne_program outside (inProgram_of_textOffset 0xf796 (by decide))
  have ag : AgreesExcept [.rip] u t := branch.agrees
  have flags := ag.rflags (by decide) (by decide)
  refine ⟨_, t, run.trans (Advances.of_step step (.inl next)), rt, target, ?_, ?_, ?_⟩
  · exact ⟨(ag.read (by decide)).trans effect.writes.1, (ag.read (by decide)).trans effect.writes.2⟩
  · change (alignedEffect s).FlagsHold t
    unfold Effect.FlagsHold
    rw [flags]
    exact effect.flags
  · exact (effect.agrees.trans ag).mono (by simp [alignedEffect, Effect.components])

end Hkdf.Proofs.NewExpand.Expand.Info
