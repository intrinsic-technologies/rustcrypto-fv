import P256.Proofs.Sec1.Affine.State
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.Instructions.NegByte
import P256.Proofs.Common.Instructions.ByteLogic.AndReg
import P256.Proofs.Common.Instructions.ByteOps
import X86Proofs.Instructions.Xor.Generated.AccImm8.Triple
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compressed.Finish

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions.NegByte P256.Proofs.Common.Instructions.ByteLogic

structure FlagsPre (s : RamState) : Prop where
  rip : s.RIP = 0x11018d
  readable : MemReadable s (stackPtr s + 80) 1

def flagsBytes : List UInt8 := [0x40,0xf6,0xdd,0x0f,0xb6,0x44,0x24,0x50,0x34,1,0x40,0x20,0xe8,0x34,1]

def infinityValue (s : RamState) : BitVec 8 :=
  (((memLoad s.external (stackPtr s+80) 8) ^^^ 1) &&& (-(s.regValue .rbp).setWidth 8)) ^^^ 1

def flagsEffect (s : RamState) : Effect :=
  { rip := 0x11019c
    writes := [⟨(.reg 5 : Operand 64), mergeGPR 8 (-(s.regValue .rbp).setWidth 8) (s.regValue .rbp)⟩,
      ⟨(.reg 0 : Operand 64), mergeGPR 8 (infinityValue s)
        (mergeGPR 8 (((memLoad s.external (stackPtr s+80) 8) ^^^ 1) &&& (-(s.regValue .rbp).setWidth 8))
          (mergeGPR 8 ((memLoad s.external (stackPtr s+80) 8) ^^^ 1)
            ((memLoad s.external (stackPtr s+80) 8).setWidth 64)))⟩]
    flags := some (xorFlags (infinityValue s)) }

set_option maxHeartbeats 800000 in
theorem flags [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary FlagsPre (codeRange 0x11018d flagsBytes) (Effect.post flagsEffect) := by
  advance_begin (show StepEffect _ _ (negR8Effect 0x11018d 5) from neg_r8_effect_step 0x11018d 0x40 0xdd (by simp [RexPrefix]) rfl rfl)
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x10190 (by decide))
  advance_then (movzx_r32_m8_effect_step 0x110190 0 (.sib 4 none 0 (.d8 80)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11018d flagsBytes 3 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm; exact hP.readable
    · exact Effect.Avoids.of_noMem (by x86_norm [andR8R8Effect]; simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10195 (by decide))
  advance_then (xor_al_imm8_effect_step 0x110195 1)
  case sub => exact codeRange_slice_subset 0x11018d flagsBytes 8 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by x86_norm [andR8R8Effect]; simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x10197 (by decide))⟩
  advance_then (show StepEffect _ _ (andR8R8Effect 0x110197 0 5) from and_r8_r8_rex_effect_step 0x110197 0x40 0xe8 (by simp [RexPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x11018d flagsBytes 10 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by x86_norm [andR8R8Effect]; simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x1019a (by decide))⟩
  advance_then (xor_al_imm8_effect_step 0x11019a 1)
  case sub => exact codeRange_slice_subset 0x11018d flagsBytes 13 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by x86_norm [andR8R8Effect]; simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x1019c (by decide))⟩
  advance_finish [flagsEffect, infinityValue, stackPtr, X86.State.regValue,
    BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64)]
  all_goals rfl

end P256.Proofs.Sec1.Affine.Compressed.Finish
