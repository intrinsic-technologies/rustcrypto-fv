import P256.Proofs.Nonce.UpdateValue.Prepare.CompressionSetup
import X86Proofs.Instructions.NopMem.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.UpdateValue.Prepare.PadSetup

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program

attribute [local x86_compose] movM8Imm8Effect
attribute [local x86_local] CompressionSetup.byteStore_local

def innerBytes : List UInt8 := [0xb8,0x03,0,0,0]

def innerEffect (_ : RamState) : Effect :=
  { rip := 0x10a990, writes := [⟨(.reg 0 : Operand 64),3⟩] }

theorem inner_code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x10a98b innerBytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xa98b innerBytes
    (by decide +kernel) (by decide +kernel)

theorem inner_run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10a98b)
      (codeRange 0x10a98b innerBytes) (Effect.post innerEffect) := by
  advance_begin (mov_r32_imm32_effect_step 0x10a98b 0xb8 (by decide) 3)
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xa990 (by decide))
  advance_finish [innerEffect]

structure OuterPre (s : RamState) : Prop where
  rip : s.RIP = 0x10aa24
  writable : MemWritable s (rspOf s + 167) 1
  codeApart : RangeApart (rspOf s + 167) 1 0x10aa24 28

def outerBytes : List UInt8 :=
  [0xc6,0x84,0x24,0xa7,0,0,0,0,0xb8,3,0,0,0,
   0x66,0x66,0x66,0x66,0x66,0x66,0x2e,0x0f,0x1f,0x84,0,0,0,0,0]

def outerEffect (s : RamState) : Effect :=
  { rip := 0x10aa40, writes := [⟨(.mem (rspOf s + 167) : Operand 8),0⟩,
      ⟨(.reg 0 : Operand 64),3⟩] }

theorem outer_code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x10aa24 outerBytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xaa24 outerBytes
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 1024 in
theorem outer_run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary OuterPre (codeRange 0x10aa24 outerBytes) (Effect.post outerEffect) := by
  advance_begin (mov_m8_imm8_effect_step 0x10aa24 (.sib 4 none 0 (.d32 167)) (by decide) rfl rfl 0)
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
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xaa2c (by decide))
  advance_then (mov_r32_imm32_effect_step 0x10aa2c 0xb8 (by decide) 3)
  case sub => exact codeRange_slice_subset 0x10aa24 outerBytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xaa31 (by decide))
  advance_then (nop_m_effect_step 0x10aa31 [0x66,0x66,0x66,0x66,0x66,0x66,0x2e]
    (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10aa24 outerBytes 13 15
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xaa40 (by decide))
  advance_finish [outerEffect, nopEffect, nopMemLen]

end P256.Proofs.Nonce.UpdateValue.Prepare.PadSetup
