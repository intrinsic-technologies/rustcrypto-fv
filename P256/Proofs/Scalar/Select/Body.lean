import P256.Proofs.EcdsaSign.Core.Prepare.Candidate.Select.Test
import P256.Proofs.Common.EffectCompose.Conditions
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Program.Code
import P256.Proofs.Common.Memory.Readable
import X86Proofs.Instructions.MovLoad.Triple
set_option autoImplicit false
namespace P256.Proofs.Scalar.Select
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field P256.Proofs.Common.Instructions
open P256.Proofs.EcdsaSign.Core.Prepare.Candidate.Select
attribute [local x86_compose] testClEffect testFlags BitVec.and_self
attribute [local x86_local] test_cl_local

def bodyBytes : List UInt8 := [0x4c,0x8b,0x12,0x4c,0x8b,0x5a,8,0x84,0xc9,0x49,0x0f,0x45,0xfa,0x84,0xc9,0x4d,0x0f,0x45,0xc3,0x4c,0x8b,0x52,16,0x84,0xc9,0x4d,0x0f,0x45,0xca,0x48,0x8b,0x52,24,0x84,0xc9,0x48,0x0f,0x45,0xf2]
def bodyEffect (s : RamState) : Effect :=
  let select (r : BitVec 5) (off : BitVec 64) :=
    if (Operand.reg 1 : Operand 8).read s = 0 then (Operand.reg r : Operand 64).read s
    else (Operand.mem ((Operand.reg 2 : Operand 64).read s+off) : Operand 64).read s
  { rip := 0x1132a7
    writes := [⟨(.reg 10 : Operand 64), (.mem ((.reg 2 : Operand 64).read s+16) : Operand 64).read s⟩,
      ⟨(.reg 11 : Operand 64), (.mem ((.reg 2 : Operand 64).read s+8) : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (.mem ((.reg 2 : Operand 64).read s+24) : Operand 64).read s⟩,
      ⟨(.reg 7 : Operand 64), select 7 0⟩, ⟨(.reg 8 : Operand 64), select 8 8⟩,
      ⟨(.reg 9 : Operand 64), select 9 16⟩, ⟨(.reg 6 : Operand 64), select 6 24⟩]
    flags := some (testFlags ((Operand.reg 1 : Operand 8).read s)) }

set_option maxHeartbeats 1200000 in
theorem body_correct [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x113280 ∧ MemReadable s (s.regValue .rdx) 32)
      (codeRange 0x113280 bodyBytes) (Effect.post bodyEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x113280 0x4c (by simp [RexWPrefix]) 2 (.base 2 .none) (by decide) rfl rfl)
  case pre =>
    intro s h
    refine ⟨h.1, ?_⟩
    change MemReadable s (s.regValue .rdx + BitVec.ofNat 64 0) 8
    exact P256.Proofs.Common.Memory.memReadable_sub h.2 0 8 (by decide)
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0x13283 (by decide))
  advance_then (mov_r64_m64_effect_step 0x113283 0x4c (by simp [RexWPrefix]) 3 (.base 2 (.d8 8)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113280 bodyBytes 3 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x13287 (by decide))⟩
    x86_norm
    exact P256.Proofs.Common.Memory.memReadable_sub hP.2 8 8 (by decide)
  advance_then (test_cl_cl_effect_step 0x113287)
  case sub => exact codeRange_slice_subset 0x113280 bodyBytes 7 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [testClEffect, Effect.components, Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x13289 (by decide))⟩
  advance_then_on [.ZF] using (show StepEffect _ _ (cmovR64R64Effect 0x113289 5 7 10) from cmov_r64_r64_effect_step 0x113289 0x49 0x45 0xfa (by simp [RexWPrefix]) (.inr rfl) rfl)
  case sub => exact codeRange_slice_subset 0x113280 bodyBytes 9 4
  case mid =>
    intro s t hP hH hO hF
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [cmovR64R64Effect, Effect.components, Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x1328d (by decide))⟩
  advance_then (test_cl_cl_effect_step 0x11328d)
  case sub => exact codeRange_slice_subset 0x113280 bodyBytes 13 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [testClEffect, Effect.components, Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x1328f (by decide))⟩
  advance_then_on [.ZF] using (show StepEffect _ _ (cmovR64R64Effect 0x11328f 5 8 11) from cmov_r64_r64_effect_step 0x11328f 0x4d 0x45 0xc3 (by simp [RexWPrefix]) (.inr rfl) rfl)
  case sub => exact codeRange_slice_subset 0x113280 bodyBytes 15 4
  case mid =>
    intro s t hP hH hO hF
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [cmovR64R64Effect, Effect.components, Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x13293 (by decide))⟩
  advance_then (mov_r64_m64_effect_step 0x113293 0x4c (by simp [RexWPrefix]) 2 (.base 2 (.d8 16)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113280 bodyBytes 19 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x13297 (by decide))⟩
    x86_norm
    exact P256.Proofs.Common.Memory.memReadable_sub hP.2 16 8 (by decide)
  advance_then (test_cl_cl_effect_step 0x113297)
  case sub => exact codeRange_slice_subset 0x113280 bodyBytes 23 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [testClEffect, Effect.components, Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x13299 (by decide))⟩
  advance_then_on [.ZF] using (show StepEffect _ _ (cmovR64R64Effect 0x113299 5 9 10) from cmov_r64_r64_effect_step 0x113299 0x4d 0x45 0xca (by simp [RexWPrefix]) (.inr rfl) rfl)
  case sub => exact codeRange_slice_subset 0x113280 bodyBytes 25 4
  case mid =>
    intro s t hP hH hO hF
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [cmovR64R64Effect, Effect.components, Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x1329d (by decide))⟩
  advance_then (mov_r64_m64_effect_step 0x11329d 0x48 (by simp [RexWPrefix]) 2 (.base 2 (.d8 24)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113280 bodyBytes 29 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x132a1 (by decide))⟩
    x86_norm
    exact P256.Proofs.Common.Memory.memReadable_sub hP.2 24 8 (by decide)
  advance_then (test_cl_cl_effect_step 0x1132a1)
  case sub => exact codeRange_slice_subset 0x113280 bodyBytes 33 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [testClEffect, Effect.components, Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x132a3 (by decide))⟩
  advance_then_on [.ZF] using (show StepEffect _ _ (cmovR64R64Effect 0x1132a3 5 6 2) from cmov_r64_r64_effect_step 0x1132a3 0x48 0x45 0xf2 (by simp [RexWPrefix]) (.inr rfl) rfl)
  case sub => exact codeRange_slice_subset 0x113280 bodyBytes 35 4
  case mid =>
    intro s t hP hH hO hF
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [cmovR64R64Effect, Effect.components, Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x132a7 (by decide))⟩
  advance_finish [bodyEffect, Bool.not_eq_true, beq_iff_eq, ite_not]
end P256.Proofs.Scalar.Select
