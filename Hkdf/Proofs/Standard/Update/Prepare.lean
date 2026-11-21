import Hkdf.Proofs.Standard.Memory
import X86Proofs.Instructions.Branch.Triple
import Hkdf.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Update

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.Field

def prepareBytes : List UInt8 :=
  [0xba,0x40,0,0,0,0x4c,0x29,0xfa,0x48,0x89,0xdd,0x48,0x29,0xd5]

def prepareEffect (s : RamState) : Effect :=
  { rip := 0x101672
    writes := [⟨(.reg 2 : Operand 64), 64 - s.regValue .r15⟩,
      ⟨(.reg 5 : Operand 64), s.regValue .rbx - (64 - s.regValue .r15)⟩]
    flags := some (.ofStatusFlags (subSpec (s.regValue .rbx) (64 - s.regValue .r15)).2) }

theorem prepare_run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s ↦ s.RIP = 0x101664)
      (codeRange 0x101664 prepareBytes) (Effect.post prepareEffect) := by
  advance_begin (mov_r32_imm32_effect_step 0x101664 0xba (by decide +kernel) 64)
  case next => exact fun _ _ ↦ boundary_ne_program outside (inProgram_of_textOffset 0x1669 (by decide))
  advance_then (sub_r64_r64_effect_step 0x101669 0x4c 0xfa (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x101664 prepareBytes 5 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0x166c (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10166c 0x48 0xdd (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x101664 prepareBytes 8 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0x166f (by decide))⟩
  advance_then (sub_r64_r64_effect_step 0x10166f 0x48 0xd5 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x101664 prepareBytes 11 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0x1672 (by decide))⟩
  advance_finish [prepareEffect]


theorem prepare_case [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip) (rip : s.RIP = 0x101664) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      t.RIP = (if (s.regValue .rbx).toNat < (64 - s.regValue .r15).toNat
        then 0x101620 else 0x101674) ∧
      t.regValue .rdx = 64 - s.regValue .r15 ∧
      t.regValue .rbp = s.regValue .rbx - (64 - s.regValue .r15) ∧
      AgreesExcept [.reg 2, .reg 5, .flags, .rip] s t := by
  obtain ⟨fuel, u, run, readyU, _, effect⟩ := prepare_run boundary outside s ready
    (programText_slice (programLoaded_codeIn loaded) 0x1664 prepareBytes
      (by decide +kernel) (by decide +kernel)) rip
  have frame : AgreesExcept [.reg 2, .reg 5, .flags, .rip] s u := effect.agrees
  have codeU := frame.codeIn (by simp [Component.Covers]) (programLoaded_codeIn loaded)
  obtain ⟨t, step, readyT, jumped⟩ := jcc_rel8_effect_step 0x101672 2 0xac u readyU
    (programText_slice codeU 0x1672 _ (by decide) (by decide +kernel))
    ⟨effect.rip, fun _ ↦ by decide⟩
  have carry : (StatusFlags.ofRFLAGS u.RFLAGS).CF =
      decide ((s.regValue .rbx).toNat < (64 - s.regValue .r15).toNat) := by
    rw [effect.flags.1]
    change (s.regValue .rbx).ult (64 - s.regValue .r15) = _
    rw [BitVec.ult_eq_decide]
  have target : t.RIP =
      (if (s.regValue .rbx).toNat < (64 - s.regValue .r15).toNat
        then 0x101620 else 0x101674) := by
    rw [jumped.rip]
    change (if (StatusFlags.ofRFLAGS u.RFLAGS).CF then 0x101620 else 0x101674) = _
    rw [carry]
    simp only [decide_eq_true_eq]
  have next : Advances boundary 1 u t := by
    apply Advances.of_step step
    left
    rw [target]
    split
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1620 (by decide))
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1674 (by decide))
  have registers : u.regValue .rdx = 64 - s.regValue .r15 ∧
      u.regValue .rbp = s.regValue .rbx - (64 - s.regValue .r15) := effect.writes
  refine ⟨fuel + 1, t, run.trans next, readyT, target,
    (jumped.agrees.read (n := 64) (r := 2) (by simp [jccEffect])).trans registers.1,
    (jumped.agrees.read (n := 64) (r := 5) (by simp [jccEffect])).trans registers.2, ?_⟩
  exact (frame.trans jumped.agrees).mono (by
    intro c hc
    simp only [jccEffect, branchEffect_components, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl) | rfl <;> simp)

end Hkdf.Proofs.Standard.Update
