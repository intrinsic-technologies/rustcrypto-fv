import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovLoad.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Entry.HashCall

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

structure MessageLoadPre (s : RamState) : Prop where
  rip : s.RIP = 0x102706
  pointer : MemReadable s (s.regValue .r12+8#64) 8
  slot : MemReadable s (stackPtr s+328) 8
  length : MemReadable s (memLoad s.external (stackPtr s+328) 64+8#64) 8

def messageLoadBytes : List UInt8 := [0x49,0x8b,0x74,0x24,8,0x48,0x8b,0x84,0x24,0x48,1,0,0,0x48,0x8b,0x68,8]

def messageLoadEffect (s : RamState) : Effect :=
  { rip := 0x102717
    writes := [⟨(.reg 6 : Operand 64),memLoad s.external (s.regValue .r12+8#64) 64⟩,
      ⟨(.reg 0 : Operand 64),memLoad s.external (stackPtr s+328) 64⟩,
      ⟨(.reg 5 : Operand 64),memLoad s.external (memLoad s.external (stackPtr s+328) 64+8#64) 64⟩] }

theorem message_load [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary MessageLoadPre (codeRange 0x102706 messageLoadBytes)
      (Effect.post messageLoadEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x102706 0x49 (by simp [RexWPrefix]) 6
    (.sib 12 none 0 (.d8 8)) (by decide) rfl rfl)
  case pre =>
    intro s h
    exact ⟨h.rip,h.pointer⟩
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0x270b (by decide))
  advance_then (mov_r64_m64_effect_step 0x10270b 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 328)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x102706 messageLoadBytes 5 8
  case mid =>
    intro s t h hh ho
    refine ⟨LoadPre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x2713 (by decide))⟩
    x86_norm [stackPtr]
    exact h.slot
  advance_then (mov_r64_m64_effect_step 0x102713 0x48 (by simp [RexWPrefix]) 5
    (.base 0 (.d8 8)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x102706 messageLoadBytes 13 4
  case mid =>
    intro s t h hh ho
    refine ⟨LoadPre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x2717 (by decide))⟩
    x86_norm [stackPtr]
    exact h.length
  apply AdvanceTriple.block_end
  intro s t _ h
  apply h.weaken
  · x86_norm [messageLoadEffect]
  · x86_norm [messageLoadEffect,stackPtr,Operand.read_reg64,State.regValue]
    all_goals repeat constructor <;> rfl
  · intro i; cases i <;> x86_norm [messageLoadEffect]
  · x86_norm [messageLoadEffect]

end P256.Proofs.Signing.Wrapper.Entry.HashCall
