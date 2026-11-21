import P256.Proofs.Verifying.Core.Reduce.BlockPre
import P256.Proofs.Common.EffectCompose.Memory

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)
open P256.Proofs.Common.Instructions.CrossPageStore (Writable Pre mov_m64_r64_effect_step_any)

namespace P256.Proofs.Verifying.Core.Reduce

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure OutputPre (s : RamState) : Prop where
  rip : s.RIP = 0x113239
  writable : ∀ offset ∈ [0,8,16,24], Writable s (s.regValue .rax + BitVec.ofNat 64 offset) 8
  apart : ∀ offset ∈ [0,8,16,24], ∀ codeOffset codeLen, codeOffset + codeLen ≤ 118431 →
    RangeApart (s.regValue .rax + BitVec.ofNat 64 offset) 8
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) codeLen

def outputBytes : List UInt8 :=
  [0x48,0x89,0x8,0x4c,0x89,0x60,0x8,0x48,0x89,0x68,0x10,0x48,0x89,0x58,0x18]

def outputEffect (s : RamState) : Effect :=
  { rip := 0x113248
    writes := [⟨(Operand.mem ((Operand.reg 0 : Operand 64).read s+0#64) : Operand 64), (Operand.reg 1 : Operand 64).read s⟩,
      ⟨(Operand.mem ((Operand.reg 0 : Operand 64).read s+8) : Operand 64), (Operand.reg 12 : Operand 64).read s⟩,
      ⟨(Operand.mem ((Operand.reg 0 : Operand 64).read s+16) : Operand 64), (Operand.reg 5 : Operand 64).read s⟩,
      ⟨(Operand.mem ((Operand.reg 0 : Operand 64).read s+24) : Operand 64), (Operand.reg 3 : Operand 64).read s⟩] }

set_option maxHeartbeats 600000 in
theorem output_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary OutputPre (codeRange 0x113239 outputBytes) (Effect.post outputEffect) := by
  refine AdvanceTriple.block_first ?k (show StepEffect _ _ (movM64R64Effect 0x113239 1 (.base 0 .none)) from mov_m64_r64_effect_step_any 0x113239 0x48 (by simp [RexWPrefix]) 1 (.base 0 .none) (by decide) rfl rfl) ?sub ?pre ?av ?next
  case sub => exact codeRange_slice_subset 0x113239 outputBytes 0 3
  case' k => x86_norm
  case pre =>
    intro s hP
    refine ⟨hP.rip, ?_, ?_⟩
    · change Writable s (s.regValue .rax + BitVec.ofNat 64 0) 8
      exact hP.writable 0 (by decide)
    · change RangeApart (s.regValue .rax + BitVec.ofNat 64 0) 8 (Extracted.textAddress + BitVec.ofNat 64 0x13239) 3
      exact hP.apart 0 (by decide) 0x13239 3 (by decide)
  case next => exact fun _ _ => boundary_ne_program hout (inProgram_of_textOffset 0x1323c (by decide))
  case av =>
    intro s hP
    apply Effect.avoids_codeRange
    x86_norm
    change RangeApart (s.regValue .rax + BitVec.ofNat 64 0) 8 (Extracted.textAddress + BitVec.ofNat 64 0x13239) 15
    exact hP.apart 0 (by decide) 0x13239 15 (by decide)
  advance_then (show StepEffect _ _ (movM64R64Effect 0x11323c 12 (.base 0 (.d8 8))) from mov_m64_r64_effect_step_any 0x11323c 0x4c (by simp [RexWPrefix]) 4 (.base 0 (.d8 8)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113239 outputBytes 3 4
  case mid =>
    intro s t hP hH hO
    refine ⟨Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 8 (by decide)
    · x86_norm
      exact hP.apart 8 (by decide) 0x1323c 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 8 (by decide) 0x13239 15 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13240 (by decide))
  advance_then (show StepEffect _ _ (movM64R64Effect 0x113240 5 (.base 0 (.d8 16))) from mov_m64_r64_effect_step_any 0x113240 0x48 (by simp [RexWPrefix]) 5 (.base 0 (.d8 16)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113239 outputBytes 7 4
  case mid =>
    intro s t hP hH hO
    refine ⟨Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 16 (by decide)
    · x86_norm
      exact hP.apart 16 (by decide) 0x13240 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 16 (by decide) 0x13239 15 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13244 (by decide))
  advance_then (show StepEffect _ _ (movM64R64Effect 0x113244 3 (.base 0 (.d8 24))) from mov_m64_r64_effect_step_any 0x113244 0x48 (by simp [RexWPrefix]) 3 (.base 0 (.d8 24)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113239 outputBytes 11 4
  case mid =>
    intro s t hP hH hO
    refine ⟨Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 24 (by decide)
    · x86_norm
      exact hP.apart 24 (by decide) 0x13244 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 24 (by decide) 0x13239 15 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13248 (by decide))
  advance_finish [outputEffect, BitVec.add_zero, gprNumber, rexR, Operand.read_reg64, BitVec.ofNat_eq_ofNat, gprIndex]

end P256.Proofs.Verifying.Core.Reduce
