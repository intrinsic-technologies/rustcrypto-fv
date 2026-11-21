import Hkdf.Proofs.Common.Field.Operations.Run.Compose
import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.Instructions.ByteStore
import X86Proofs.Program.ReadWrite.Bytes
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import X86Proofs.Instructions.Add.Generated.R8.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Info.Short

open Hkdf.Spec.Program Hkdf.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Field Hkdf.Proofs.Common.Machine

private def setupBytes : List UInt8 :=
  [0x4a, 0x8d, 0x3c, 0x34, 0x48, 0x81, 0xc7, 0x10, 1, 0, 0,
   0x48, 0x89, 0xde, 0x48, 0x89, 0xea]

def setupEffect (s : RamState) : Effect :=
  { rip := 0x10f701
    writes := [⟨(.reg 7 : Operand 64), rspOf s + (Operand.reg 14 : Operand 64).read s + 272⟩,
      ⟨(.reg 6 : Operand 64), (Operand.reg 3 : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (Operand.reg 5 : Operand 64).read s⟩]
    flags := some (.ofStatusFlags (addSpec (rspOf s + (Operand.reg 14 : Operand 64).read s) 272).2) }

private theorem setup_run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s ↦ s.RIP = 0x10f6f0)
      (codeRange 0x10f6f0 setupBytes) (Effect.post setupEffect) := by
  advance_begin (lea_r64_effect_step 0x10f6f0 0x4a (by simp [RexWPrefix]) 7
    (.sib 4 (some 14) 0 .none) (by decide) rfl rfl)
  case next => exact fun _ _ ↦ boundary_ne_program outside (inProgram_of_textOffset 0xf6f4 (by decide))
  advance_then (add_r64_imm32_effect_step 0x10f6f4 0x48 0xc7 272 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f6f0 setupBytes 4 7
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0xf6fb (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10f6fb 0x48 0xde (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10f6f0 setupBytes 11 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0xf6fe (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10f6fe 0x48 0xea (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10f6f0 setupBytes 14 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0xf701 (by decide))⟩
  advance_finish [setupEffect, BitVec.shiftLeft_zero, BitVec.add_zero]

theorem arguments [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (outside : ¬ InProgram boundary.rip)
    (pc : s.RIP = 0x10f6f0) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ (setupEffect s).Holds s t := by
  have code := programText_slice (programLoaded_codeIn loaded) 0xf6f0 setupBytes
    (by decide) (by decide +kernel)
  obtain ⟨fuel, t, run, rt, _, effect⟩ := setup_run boundary outside s ready code pc
  exact ⟨fuel, t, run, rt, effect⟩

theorem storeLength [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (outside : ¬ InProgram boundary.rip)
    (pc : s.RIP = 0x10f704) (writable : MemWritable s (rspOf s + 335) 1)
    (apart : RangeApart (rspOf s + 335) 1 0x10f707 8) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ t.RIP = 0x10f70f ∧
      t.external[rspOf s + 335]? = some
        (storedByte ((s.regValue .rbp).setWidth 8 + (s.regValue .r14).setWidth 8) 0) ∧
      AgreesExcept [.reg 5, .flags, .mem (rspOf s + 335) 1, .rip] s t := by
  have code := programText_slice (programLoaded_codeIn loaded) 0xf704 [0x44, 0, 0xf5]
    (by decide) (by decide +kernel)
  obtain ⟨u, run, readyU, add⟩ := (add_r8_r8_rex_effect_step 0x10f704 0x44 0xf5
    (by simp [RexPrefix]) rfl).advances ready code pc
    (boundary_ne_program outside (inProgram_of_textOffset 0xf707 (by decide)))
  change (addR8R8Effect 0x10f704 3 5 14 s).Holds s u at add
  have ag : AgreesExcept [.reg 5, .flags, .rip] s u := add.agrees
  have sp : rspOf u = rspOf s := ag.read (by decide)
  have ext := ag.external (by simp [Component.Covers])
  have writableU : MemWritable u (rspOf u + 335) 1 := by
    rw [sp]
    exact writable.of_external_eq ext
  have codeS := programText_slice (programLoaded_codeIn loaded) 0xf707
    [0x40, 0x88, 0xac, 0x24, 0x4f, 1, 0, 0] (by decide) (by decide +kernel)
  have store : StepEffect (StorePre 0x10f707 8 (fun u ↦ rspOf u + 335) 1)
      (codeRange 0x10f707 [0x40, 0x88, 0xac, 0x24, 0x4f, 1, 0, 0])
      (storeEffect 0x10f707 8 (fun u ↦ rspOf u + 335)
        (fun u ↦ (Operand.reg 5 : Operand 8).read u)) :=
    Hkdf.Proofs.Common.Instructions.mov_m8_r8_effect_step 0x10f707 0x40 (by simp [RexPrefix])
      5 (.sib 4 none 0 (.d32 335)) (by decide) rfl rfl
  obtain ⟨t, runT, readyT, eff⟩ := store.advances readyU (codeS.of_external_eq ext)
    ⟨add.rip, writableU, sp ▸ apart⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0xf70f (by decide)))
  have agT : AgreesExcept [.mem (rspOf s + 335) 1, .rip] u t := by
    simpa only [storeEffect_components, Nat.reduceDiv, sp] using eff.agrees
  have value : (Operand.reg 5 : Operand 8).read u =
      (s.regValue .rbp).setWidth 8 + (s.regValue .r14).setWidth 8 := by
    change ((Operand.reg 5 : Operand 64).read u).setWidth 8 = _
    have eq : (Operand.reg 5 : Operand 64).read u = _ := add.writes
    rw [eq, setWidth_mergeGPR8]
    rfl
  have byte : memLoad t.external (rspOf s + 335) 8 =
      (s.regValue .rbp).setWidth 8 + (s.regValue .r14).setWidth 8 := by
    rw [← sp, ← value]
    exact eff.writes
  have present : ∀ i < 1, (t.external[rspOf s + 335 + BitVec.ofNat 64 i]?).isSome :=
    fun i hi ↦ agT.grow _ (ag.grow _ (writable.mem i hi))
  have stored := Bytes.of_memLoad (n := 8) present 0 (by decide)
  rw [byte] at stored
  refine ⟨t, run.trans runT, readyT, eff.rip, ?_, (ag.trans agT).mono (by simp)⟩
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using stored

end Hkdf.Proofs.NewExpand.Expand.Info.Short
