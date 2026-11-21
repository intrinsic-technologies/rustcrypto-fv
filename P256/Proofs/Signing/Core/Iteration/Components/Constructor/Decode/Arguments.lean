import P256.Proofs.Signing.Core.Iteration.Components.Constructor.Frame
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Movs.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Signing.Core.Iteration.Components.Constructor.Decode

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def argumentBytes (second : Bool) : List UInt8 :=
  [0x48,0x89,0xe7, 0xba,32,0,0,0, 0x4c,0x89,if second then 0xf6 else 0xfe]

def argumentEffect (p : BitVec 64) (second : Bool) (s : RamState) : Effect :=
  { rip := p + 11
    writes := [⟨(.reg 7 : Operand 64), stackPtr s⟩,
      ⟨(.reg 2 : Operand 64), 32⟩,
      ⟨(.reg 6 : Operand 64), s.regValue (if second then .r14 else .r15)⟩] }

set_option maxHeartbeats 800000 in
theorem first_arguments_run [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip)
 :
    AdvanceTriple boundary
      (fun s => s.RIP = if false then 0x10993b else 0x1098b2)
      (codeRange (if false then 0x10993b else 0x1098b2) (argumentBytes false))
      (Effect.post (argumentEffect (if false then 0x10993b else 0x1098b2) false)) := by
  let p : BitVec 64 := if false then 0x10993b else 0x1098b2
  have next (i : Nat) (hi : i ≤ 11) : p + BitVec.ofNat 64 i ≠ boundary.rip := by
    simpa [BitVec.ofNat_add, ← BitVec.add_assoc, p, Extracted.textAddress] using
      boundary_ne_program hout (inProgram_of_textOffset (0x98b2 + i) (by omega))
  advance_begin (mov_r64_r64_effect_step p 0x48 0xe7
    (by simp [RexWPrefix]) rfl)
  case next => intro _ _; exact next 3 (by decide)
  advance_then (mov_r32_imm32_effect_step (p + 3) 0xba (by decide +kernel) 32)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · change p + 3 + 5 ≠ boundary.rip
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceOfNat] using next 8 (by decide)
  advance_then (mov_r64_r64_effect_step (p + 8) 0x4c (if false then 0xf6 else 0xfe)
    (by simp [RexWPrefix]) (by rfl))
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · change p + 8 + 3 ≠ boundary.rip
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceOfNat] using next 11 (by decide)
  advance_finish [argumentBytes, argumentEffect, stackPtr, Operand.read_reg64, p]

set_option maxHeartbeats 800000 in
theorem second_arguments_run [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip)
 :
    AdvanceTriple boundary
      (fun s => s.RIP = if true then 0x10993b else 0x1098b2)
      (codeRange (if true then 0x10993b else 0x1098b2) (argumentBytes true))
      (Effect.post (argumentEffect (if true then 0x10993b else 0x1098b2) true)) := by
  let p : BitVec 64 := if true then 0x10993b else 0x1098b2
  have next (i : Nat) (hi : i ≤ 11) : p + BitVec.ofNat 64 i ≠ boundary.rip := by
    simpa [BitVec.ofNat_add, ← BitVec.add_assoc, p, Extracted.textAddress] using
      boundary_ne_program hout (inProgram_of_textOffset (0x993b + i) (by omega))
  advance_begin (mov_r64_r64_effect_step p 0x48 0xe7
    (by simp [RexWPrefix]) rfl)
  case next => intro _ _; exact next 3 (by decide)
  advance_then (mov_r32_imm32_effect_step (p + 3) 0xba (by decide +kernel) 32)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · change p + 3 + 5 ≠ boundary.rip
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceOfNat] using next 8 (by decide)
  advance_then (mov_r64_r64_effect_step (p + 8) 0x4c (if true then 0xf6 else 0xfe)
    (by simp [RexWPrefix]) (by rfl))
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · change p + 8 + 3 ≠ boundary.rip
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceOfNat] using next 11 (by decide)
  advance_finish [argumentBytes, argumentEffect, stackPtr, Operand.read_reg64, p]

theorem arguments_run [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip)
    (second : Bool) :
    AdvanceTriple boundary
      (fun s => s.RIP = if second then 0x10993b else 0x1098b2)
      (codeRange (if second then 0x10993b else 0x1098b2) (argumentBytes second))
      (Effect.post (argumentEffect (if second then 0x10993b else 0x1098b2) second)) := by
  cases second
  · exact first_arguments_run boundary hout
  · exact second_arguments_run boundary hout

def serializeArgumentBytes : List UInt8 :=
  [0x4c,0x8d,0xb4,0x24,0xa0,0,0,0,
   0x48,0x8d,0xb4,0x24,0x80,0,0,0, 0x4c,0x89,0xf7]

def serializeArgumentEffect (s : RamState) : Effect :=
  { rip := 0x109936
    writes := [⟨(.reg 14 : Operand 64), stackPtr s + 160⟩,
      ⟨(.reg 6 : Operand 64), stackPtr s + 128⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 160⟩] }

set_option maxHeartbeats 800000 in
theorem serialize_arguments_run [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x109923)
      (codeRange 0x109923 serializeArgumentBytes) (Effect.post serializeArgumentEffect) := by
  have next (i : Nat) (hi : i ≤ 19) : 0x109923 + BitVec.ofNat 64 i ≠ boundary.rip := by
    simpa [BitVec.ofNat_add, ← BitVec.add_assoc, Extracted.textAddress] using
      boundary_ne_program hout (inProgram_of_textOffset (0x9923 + i) (by omega))
  advance_begin (lea_r64_effect_step 0x109923 0x4c (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d32 160)) (by decide +kernel) rfl rfl)
  case next => intro _ _; exact next 8 (by decide)
  advance_then (lea_r64_effect_step 0x10992b 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d32 128)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x109923 serializeArgumentBytes 8 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact next 16 (by decide)
  advance_then (mov_r64_r64_effect_step 0x109933 0x4c 0xf7
    (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x109923 serializeArgumentBytes 16 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact next 19 (by decide)
  advance_finish [serializeArgumentBytes, serializeArgumentEffect, stackPtr, Operand.read_reg64]

end P256.Proofs.Signing.Core.Iteration.Components.Constructor.Decode
