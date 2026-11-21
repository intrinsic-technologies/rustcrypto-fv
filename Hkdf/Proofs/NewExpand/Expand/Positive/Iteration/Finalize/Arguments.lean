import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Finalize.Compression
import Hkdf.Proofs.Common.EffectCompose.Advance
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Finalize

open Hkdf.Spec.Program Hkdf.Proofs.Common Hkdf.Proofs.Common.Machine
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Field (AdvanceTriple)

def CompressionSite.setupOffset : CompressionSite → Nat
  | .extra => 0xf9eb
  | .inner => 0xf3a0
  | .outer => 0xf4b6

private def setupBytes : CompressionSite → List UInt8
  | .extra => [0xba,0x1,0x0,0x0,0x0,0x48,0x8d,0xbc,0x24,0x90,0x0,0x0,0x0,0x48,0x8d,0x74,0x24,0x10]
  | .inner => [0xba,0x1,0x0,0x0,0x0,0x4c,0x8d,0xbc,0x24,0x90,0x0,0x0,0x0,0x4c,0x89,0xff,0x4c,0x8d,0x6c,0x24,0x10,0x4c,0x89,0xee]
  | .outer => [0xba,0x1,0x0,0x0,0x0,0x48,0x8d,0xbc,0x24,0xb8,0x0,0x0,0x0,0x4c,0x89,0xee]

def CompressionSite.setupEffect (site : CompressionSite) (s : RamState) : Effect :=
  let src := if site matches .outer then (.reg 13 : Operand 64).read s else rspOf s + 16
  let dst := rspOf s + BitVec.ofNat 64 site.hashOffset
  { rip := site.pc
    writes := [⟨(.reg 2 : Operand 64), 1⟩, ⟨(.reg 7 : Operand 64), dst⟩,
      ⟨(.reg 6 : Operand 64), src⟩] ++
      (match site with
      | .inner => [⟨(.reg 15 : Operand 64), dst⟩, ⟨(.reg 13 : Operand 64), src⟩]
      | _ => []) }

theorem compressionArguments [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (site : CompressionSite) (loaded : ProgramLoaded s) (ready : ReadyToStep s)
    (outside : ¬ InProgram boundary.rip)
    (rip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 site.setupOffset) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ (site.setupEffect s).Holds s t := by
  have code := programText_slice (programLoaded_codeIn loaded) site.setupOffset (setupBytes site)
    (by cases site <;> decide) (by cases site <;> decide +kernel)
  suffices run : AdvanceTriple boundary
      (fun s ↦ s.RIP = Extracted.textAddress + BitVec.ofNat 64 site.setupOffset)
      (codeRange (Extracted.textAddress + BitVec.ofNat 64 site.setupOffset) (setupBytes site))
      (Effect.post site.setupEffect) by
    obtain ⟨fuel,t,exec,rt,_,effect⟩ := run s ready code rip
    exact ⟨fuel,t,exec,rt,effect⟩
  cases site with
  | extra =>
    change AdvanceTriple boundary (fun s ↦ s.RIP = 0x10f9eb) (codeRange 0x10f9eb (setupBytes .extra)) _
    advance_begin (mov_r32_imm32_effect_step 0x10f9eb 0xba (by decide) 1)
    case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xf9f0 (by decide))
    advance_then (lea_r64_effect_step 0x10f9f0 0x48 (by simp [RexWPrefix]) 7
      (.sib 4 none 0 (.d32 144)) (by decide) rfl rfl)
    case sub => exact codeRange_slice_subset 0x10f9eb (setupBytes .extra) 5 8
    case mid =>
      intro s t hp hh ho
      exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
        boundary_ne_program outside (inProgram_of_textOffset 0xf9f8 (by decide))⟩
    advance_then (lea_r64_effect_step 0x10f9f8 0x48 (by simp [RexWPrefix]) 6
      (.sib 4 none 0 (.d8 16)) (by decide) rfl rfl)
    case sub => exact codeRange_slice_subset 0x10f9eb (setupBytes .extra) 13 5
    case mid =>
      intro s t hp hh ho
      exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
        boundary_ne_program outside (inProgram_of_textOffset 0xf9fd (by decide))⟩
    advance_finish [CompressionSite.setupEffect, CompressionSite.pc, CompressionSite.hashOffset,
      CompressionSite.offset, Extracted.textAddress]
  | inner =>
    change AdvanceTriple boundary (fun s ↦ s.RIP = 0x10f3a0) (codeRange 0x10f3a0 (setupBytes .inner)) _
    advance_begin (mov_r32_imm32_effect_step 0x10f3a0 0xba (by decide) 1)
    case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xf3a5 (by decide))
    advance_then (lea_r64_effect_step 0x10f3a5 0x4c (by simp [RexWPrefix]) 7
      (.sib 4 none 0 (.d32 144)) (by decide) rfl rfl)
    case sub => exact codeRange_slice_subset 0x10f3a0 (setupBytes .inner) 5 8
    case mid =>
      intro s t hp hh ho
      exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
        boundary_ne_program outside (inProgram_of_textOffset 0xf3ad (by decide))⟩
    advance_then (mov_r64_r64_effect_step 0x10f3ad 0x4c 0xff (by simp [RexWPrefix]) rfl)
    case sub => exact codeRange_slice_subset 0x10f3a0 (setupBytes .inner) 13 3
    case mid =>
      intro s t hp hh ho
      exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
        boundary_ne_program outside (inProgram_of_textOffset 0xf3b0 (by decide))⟩
    advance_then (lea_r64_effect_step 0x10f3b0 0x4c (by simp [RexWPrefix]) 5
      (.sib 4 none 0 (.d8 16)) (by decide) rfl rfl)
    case sub => exact codeRange_slice_subset 0x10f3a0 (setupBytes .inner) 16 5
    case mid =>
      intro s t hp hh ho
      exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
        boundary_ne_program outside (inProgram_of_textOffset 0xf3b5 (by decide))⟩
    advance_then (mov_r64_r64_effect_step 0x10f3b5 0x4c 0xee (by simp [RexWPrefix]) rfl)
    case sub => exact codeRange_slice_subset 0x10f3a0 (setupBytes .inner) 21 3
    case mid =>
      intro s t hp hh ho
      exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
        boundary_ne_program outside (inProgram_of_textOffset 0xf3b8 (by decide))⟩
    advance_finish [CompressionSite.setupEffect, CompressionSite.pc, CompressionSite.hashOffset,
      CompressionSite.offset, Extracted.textAddress]
  | outer =>
    change AdvanceTriple boundary (fun s ↦ s.RIP = 0x10f4b6) (codeRange 0x10f4b6 (setupBytes .outer)) _
    advance_begin (mov_r32_imm32_effect_step 0x10f4b6 0xba (by decide) 1)
    case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xf4bb (by decide))
    advance_then (lea_r64_effect_step 0x10f4bb 0x48 (by simp [RexWPrefix]) 7
      (.sib 4 none 0 (.d32 184)) (by decide) rfl rfl)
    case sub => exact codeRange_slice_subset 0x10f4b6 (setupBytes .outer) 5 8
    case mid =>
      intro s t hp hh ho
      exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
        boundary_ne_program outside (inProgram_of_textOffset 0xf4c3 (by decide))⟩
    advance_then (mov_r64_r64_effect_step 0x10f4c3 0x4c 0xee (by simp [RexWPrefix]) rfl)
    case sub => exact codeRange_slice_subset 0x10f4b6 (setupBytes .outer) 13 3
    case mid =>
      intro s t hp hh ho
      exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
        boundary_ne_program outside (inProgram_of_textOffset 0xf4c6 (by decide))⟩
    advance_finish [CompressionSite.setupEffect, CompressionSite.pc, CompressionSite.hashOffset,
      CompressionSite.offset, Extracted.textAddress]

end Hkdf.Proofs.NewExpand.Expand.Finalize
