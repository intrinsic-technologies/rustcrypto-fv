import P256.Proofs.Program.Code
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.Instructions.CrossPageStore.Mov
import P256.Proofs.Common.EffectCompose.Memory

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)
open P256.Proofs.Common.Instructions.CrossPageStore (Writable Pre mov_m64_r64_effect_step_any)

namespace P256.Proofs.Scalar.Select

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure OutputPre (s : RamState) : Prop where
  rip : s.RIP = 0x1132a7
  writable : ∀ offset ∈ [0,8,16,24], Writable s (s.regValue .rax + BitVec.ofNat 64 offset) 8
  apart : ∀ offset ∈ [0,8,16,24], ∀ codeOffset codeLen, codeOffset + codeLen ≤ 118431 →
    RangeApart (s.regValue .rax + BitVec.ofNat 64 offset) 8
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) codeLen

def outputBytes : List UInt8 :=
  [0x48,0x89,0x38,0x4c,0x89,0x40,0x8,0x4c,0x89,0x48,0x10,0x48,0x89,0x70,0x18]

def outputEffect (s : RamState) : Effect :=
  { rip := 0x1132b6
    writes := [⟨(Operand.mem ((Operand.reg 0 : Operand 64).read s+0#64) : Operand 64), (Operand.reg 7 : Operand 64).read s⟩,
      ⟨(Operand.mem ((Operand.reg 0 : Operand 64).read s+8) : Operand 64), (Operand.reg 8 : Operand 64).read s⟩,
      ⟨(Operand.mem ((Operand.reg 0 : Operand 64).read s+16) : Operand 64), (Operand.reg 9 : Operand 64).read s⟩,
      ⟨(Operand.mem ((Operand.reg 0 : Operand 64).read s+24) : Operand 64), (Operand.reg 6 : Operand 64).read s⟩] }

set_option maxHeartbeats 600000 in
theorem output_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary OutputPre (codeRange 0x1132a7 outputBytes) (Effect.post outputEffect) := by
  refine AdvanceTriple.block_first ?k (show StepEffect _ _ (movM64R64Effect 0x1132a7 7 (.base 0 .none)) from mov_m64_r64_effect_step_any 0x1132a7 0x48 (by simp [RexWPrefix]) 7 (.base 0 .none) (by decide) rfl rfl) ?sub ?pre ?av ?next
  case sub => exact codeRange_slice_subset 0x1132a7 outputBytes 0 3
  case' k => x86_norm
  case pre =>
    intro s hP
    refine ⟨hP.rip, ?_, ?_⟩
    · change Writable s (s.regValue .rax + BitVec.ofNat 64 0) 8
      exact hP.writable 0 (by decide)
    · change RangeApart (s.regValue .rax + BitVec.ofNat 64 0) 8 (Extracted.textAddress + BitVec.ofNat 64 0x132a7) 3
      exact hP.apart 0 (by decide) 0x132a7 3 (by decide)
  case next => exact fun _ _ => boundary_ne_program hout (inProgram_of_textOffset 0x132aa (by decide))
  case av =>
    intro s hP
    apply Effect.avoids_codeRange
    x86_norm
    change RangeApart (s.regValue .rax + BitVec.ofNat 64 0) 8 (Extracted.textAddress + BitVec.ofNat 64 0x132a7) 15
    exact hP.apart 0 (by decide) 0x132a7 15 (by decide)
  advance_then (show StepEffect _ _ (movM64R64Effect 0x1132aa 8 (.base 0 (.d8 8))) from mov_m64_r64_effect_step_any 0x1132aa 0x4c (by simp [RexWPrefix]) 0 (.base 0 (.d8 8)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1132a7 outputBytes 3 4
  case mid =>
    intro s t hP hH hO
    refine ⟨Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 8 (by decide)
    · x86_norm
      exact hP.apart 8 (by decide) 0x132aa 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 8 (by decide) 0x132a7 15 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x132ae (by decide))
  advance_then (show StepEffect _ _ (movM64R64Effect 0x1132ae 9 (.base 0 (.d8 16))) from mov_m64_r64_effect_step_any 0x1132ae 0x4c (by simp [RexWPrefix]) 1 (.base 0 (.d8 16)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1132a7 outputBytes 7 4
  case mid =>
    intro s t hP hH hO
    refine ⟨Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 16 (by decide)
    · x86_norm
      exact hP.apart 16 (by decide) 0x132ae 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 16 (by decide) 0x132a7 15 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x132b2 (by decide))
  advance_then (show StepEffect _ _ (movM64R64Effect 0x1132b2 6 (.base 0 (.d8 24))) from mov_m64_r64_effect_step_any 0x1132b2 0x48 (by simp [RexWPrefix]) 6 (.base 0 (.d8 24)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1132a7 outputBytes 11 4
  case mid =>
    intro s t hP hH hO
    refine ⟨Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 24 (by decide)
    · x86_norm
      exact hP.apart 24 (by decide) 0x132b2 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 24 (by decide) 0x132a7 15 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x132b6 (by decide))
  advance_finish [outputEffect, BitVec.add_zero, gprNumber, rexR, Operand.read_reg64, BitVec.ofNat_eq_ofNat, gprIndex]

end P256.Proofs.Scalar.Select
