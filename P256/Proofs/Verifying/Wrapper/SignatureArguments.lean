import P256.Proofs.Verifying.Wrapper.KeyArguments

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

structure SignatureLoadPre (s : RamState) : Prop where
  rip : s.RIP = 0x103122
  pointer : MemReadable s (s.regValue .r14+8#64) 8
  length : MemReadable s (s.regValue .rbx+8#64) 8

def signatureLoadBytes : List UInt8 := [73, 139, 118, 8, 72, 139, 67, 8]

def signatureLoadEffect (s : RamState) : Effect :=
  { rip := 0x10312a
    writes := [⟨(.reg 6 : Operand 64),memLoad s.external (s.regValue .r14+8#64) 64⟩,
      ⟨(.reg 0 : Operand 64),memLoad s.external (s.regValue .rbx+8#64) 64⟩] }

theorem signature_load [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary SignatureLoadPre (codeRange 0x103122 signatureLoadBytes)
      (Effect.post signatureLoadEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x103122 0x49 (by simp [RexWPrefix]) 6
    (.base 14 (.d8 8)) (by decide) rfl rfl)
  case pre =>
    intro s h
    exact ⟨h.rip,h.pointer⟩
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0x3126 (by decide))
  advance_then (mov_r64_m64_effect_step 0x103126 0x48 (by simp [RexWPrefix]) 0
    (.base 3 (.d8 8)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x103122 signatureLoadBytes 4 4
  case mid =>
    intro s t h hh ho
    refine ⟨LoadPre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x312a (by decide))⟩
    x86_norm
    exact h.length
  advance_finish [signatureLoadEffect]

def signatureArgumentBytes : List UInt8 := [72, 141, 124, 36, 72, 72, 137, 194]

def signatureArgumentEffect (s : RamState) : Effect :=
  { rip := 0x10313b
    writes := [⟨(.reg 7 : Operand 64),(Operand.reg 4 : Operand 64).read s+72⟩,
      ⟨(.reg 2 : Operand 64),s.regValue .rax⟩] }

theorem signature_arguments [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x103133)
      (codeRange 0x103133 signatureArgumentBytes) (Effect.post signatureArgumentEffect) := by
  advance_begin (lea_r64_effect_step 0x103133 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d8 72)) (by decide) rfl rfl)
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0x3138 (by decide))
  advance_then (mov_r64_r64_effect_step 0x103138 0x48 0xc2 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x103133 signatureArgumentBytes 5 3
  case mid =>
    intro s t h hh ho
    exact ⟨hh.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x313b (by decide))⟩
  advance_finish [signatureArgumentEffect]

end P256.Proofs.Verifying.Wrapper
