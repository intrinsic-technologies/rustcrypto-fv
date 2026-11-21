import P256.Proofs.Verifying.Wrapper.KeyArguments

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

structure MessageLoadPre (s : RamState) : Prop where
  rip : s.RIP = 0x1031aa
  pointer : MemReadable s (s.regValue .r14+16#64) 8
  length : MemReadable s (s.regValue .rbx+16#64) 8

def messageLoadBytes : List UInt8 := [73, 139, 78, 16, 72, 139, 67, 16]

def messageLoadEffect (s : RamState) : Effect :=
  { rip := 0x1031b2
    writes := [⟨(.reg 1 : Operand 64),memLoad s.external (s.regValue .r14+16#64) 64⟩,
      ⟨(.reg 0 : Operand 64),memLoad s.external (s.regValue .rbx+16#64) 64⟩] }

theorem message_load [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary MessageLoadPre (codeRange 0x1031aa messageLoadBytes)
      (Effect.post messageLoadEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x1031aa 0x49 (by simp [RexWPrefix]) 1
    (.base 14 (.d8 16)) (by decide) rfl rfl)
  case pre =>
    intro s h
    exact ⟨h.rip,h.pointer⟩
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0x31ae (by decide))
  advance_then (mov_r64_m64_effect_step 0x1031ae 0x48 (by simp [RexWPrefix]) 0
    (.base 3 (.d8 16)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1031aa messageLoadBytes 4 4
  case mid =>
    intro s t h hh ho
    refine ⟨LoadPre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x31b2 (by decide))⟩
    x86_norm
    exact h.length
  advance_finish [messageLoadEffect]

end P256.Proofs.Verifying.Wrapper
