import P256.Proofs.Nonce.Update.Seeded.Prepare.CompressionSetup
import X86Proofs.Instructions.NopMem.Triple
import X86Proofs.Instructions.Nop.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Seeded.Prepare.PadSetup

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program

attribute [local x86_compose] movM8Imm8Effect
attribute [local x86_local] CompressionSetup.byteStore_local

def innerBytes : List UInt8 := [0xb8, 0x3, 0x0, 0x0, 0x0]

def innerEffect (_ : RamState) : Effect :=
  { rip := 0x10a4d0, writes := [⟨(.reg 0 : Operand 64),3⟩] }

theorem inner_code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x10a4cb innerBytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xa4cb innerBytes
    (by decide +kernel) (by decide +kernel)

theorem inner_run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10a4cb)
      (codeRange 0x10a4cb innerBytes) (Effect.post innerEffect) := by
  advance_begin (mov_r32_imm32_effect_step 0x10a4cb 0xb8 (by decide) 3)
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xa4d0 (by decide))
  advance_finish [innerEffect]

structure OuterPre (s : RamState) : Prop where
  rip : s.RIP = 0x10a561
  writable : MemWritable s (rspOf s + 319) 1
  codeApart : RangeApart (rspOf s + 319) 1 0x10a561 15

def outerBytes : List UInt8 := [0xc6, 0x84, 0x24, 0x3f, 0x1, 0x0, 0x0, 0x0, 0xb8, 0x3, 0x0, 0x0, 0x0, 0x66, 0x90]

def outerEffect (s : RamState) : Effect :=
  { rip := 0x10a570, writes := [⟨(.mem (rspOf s + 319) : Operand 8),0⟩,
      ⟨(.reg 0 : Operand 64),3⟩] }

theorem outer_code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x10a561 outerBytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xa561 outerBytes
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 1024 in
theorem outer_run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary OuterPre (codeRange 0x10a561 outerBytes) (Effect.post outerEffect) := by
  advance_begin (mov_m8_imm8_effect_step 0x10a561 (.sib 4 none 0 (.d32 319)) (by decide) rfl rfl 0)
  case pre =>
    intro s pre
    exact ⟨pre.rip, pre.writable, fun i hi j hj => pre.codeApart i hi j (by change j < 8 at hj; omega)⟩
  case av =>
    intro s pre
    apply Effect.avoids_codeRange
    intro c hc a len equal
    simp only [movM8Imm8Effect, storeEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · cases equal
      exact pre.codeApart
    · cases equal
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xa569 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10a569 0xb8 (by decide) 3)
  case sub => exact codeRange_slice_subset 0x10a561 outerBytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa56e (by decide))
  advance_then (nop_66_effect_step 0x10a56e)
  case sub => exact codeRange_slice_subset 0x10a561 outerBytes 13 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa570 (by decide))
  advance_finish [outerEffect, nopEffect, nopMemLen]

end P256.Proofs.Nonce.Update.Seeded.Prepare.PadSetup
