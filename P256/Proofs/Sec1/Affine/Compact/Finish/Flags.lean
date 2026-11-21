import P256.Proofs.Sec1.Affine.State
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.Instructions.NegByte
import P256.Proofs.Common.Instructions.ByteLogic.AndReg
import P256.Proofs.Common.Instructions.ByteOps
import X86Proofs.Instructions.Xor.Generated.AccImm8.Triple
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple
import X86Proofs.Instructions.And.Generated.R8M8.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compact.Finish

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions.NegByte P256.Proofs.Common.Instructions.ByteLogic

structure FlagsPre (s : RamState) : Prop where
  rip : s.RIP = 0x1105aa
  readable : MemReadable s (stackPtr s + 80) 1
  maskReadable : MemReadable s (stackPtr s + 12) 1

def flagsBytes : List UInt8 := [0x0f,0xb6,0x44,0x24,0x50,0x34,1,0x22,0x44,0x24,0x0c,0x34,1]

def infinityValue (s : RamState) : BitVec 8 :=
  (((memLoad s.external (stackPtr s+80) 8) ^^^ 1) &&& (memLoad s.external (stackPtr s+12) 8)) ^^^ 1

def flagsEffect (s : RamState) : Effect :=
  { rip := 0x1105b7
    writes := [⟨(.reg 0 : Operand 64), mergeGPR 8 (infinityValue s)
        (mergeGPR 8 (((memLoad s.external (stackPtr s+80) 8) ^^^ 1) &&& (memLoad s.external (stackPtr s+12) 8))
          (mergeGPR 8 ((memLoad s.external (stackPtr s+80) 8) ^^^ 1)
            ((memLoad s.external (stackPtr s+80) 8).setWidth 64)))⟩]
    flags := some (xorFlags (infinityValue s)) }

theorem flags [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary FlagsPre (codeRange 0x1105aa flagsBytes) (Effect.post flagsEffect) := by
  advance_begin (movzx_r32_m8_effect_step 0x1105aa 0 (.sib 4 none 0 (.d8 80)) (by decide) rfl rfl)
  case pre => intro s h; exact ⟨h.rip,h.readable⟩
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x105af (by decide))
  advance_then (xor_al_imm8_effect_step 0x1105af 1)
  case sub => exact codeRange_slice_subset 0x1105aa flagsBytes 5 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x105b1 (by decide))⟩
  advance_then (and_r8_m8_effect_step 0x1105b1 0 (by decide) (.sib 4 none 0 (.d8 12)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1105aa flagsBytes 7 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm; exact hP.maskReadable
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x105b5 (by decide))
  advance_then (xor_al_imm8_effect_step 0x1105b5 1)
  case sub => exact codeRange_slice_subset 0x1105aa flagsBytes 11 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x105b7 (by decide))⟩
  advance_finish [flagsEffect,infinityValue,stackPtr,X86.State.regValue,
    BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64)]
  all_goals rfl

end P256.Proofs.Sec1.Affine.Compact.Finish
