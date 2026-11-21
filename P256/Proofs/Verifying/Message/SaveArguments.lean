import P256.Proofs.Verifying.Message.Entry
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Instructions.CrossPageStore

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message

open P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions.CrossPageStore (Writable)

structure SaveArgumentsPre (s : RamState) : Prop where
  rip : s.RIP = 0x10d581
  writable : ∀ off ∈ ([456,384,464] : List Nat), Writable s (stackPtr s + BitVec.ofNat 64 off) 8
  apart : ∀ off ∈ ([456,384,464] : List Nat),
    ∀ pc len : Nat, pc + len ≤ 118431 →
      RangeApart (stackPtr s + BitVec.ofNat 64 off) 8
        (Extracted.textAddress + BitVec.ofNat 64 pc) len

def saveArgumentsBytes : List UInt8 :=
  [0x4c, 0x89, 0x84, 0x24, 0xd0, 0x1, 0x0, 0x0, 0x48, 0x89, 0xb4, 0x24, 0xc8, 0x1, 0x0, 0x0, 0x48, 0x89, 0xbc, 0x24, 0x80, 0x1, 0x0, 0x0]

def saveArgumentsEffect (s : RamState) : Effect :=
  { rip := 0x10d599
    writes := [⟨(.mem (stackPtr s + 464) : Operand 64), s.regValue .r8⟩,
      ⟨(.mem (stackPtr s + 456) : Operand 64), s.regValue .rsi⟩,
      ⟨(.mem (stackPtr s + 384) : Operand 64), s.regValue .rdi⟩] }

theorem save_arguments_correct [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary SaveArgumentsPre (codeRange 0x10d581 saveArgumentsBytes)
      (Effect.post saveArgumentsEffect) := by
  advance_begin (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any
    0x10d581 0x4c (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 464))
    (by decide) rfl rfl)
  case pre =>
    intro s hp
    refine ⟨hp.rip, ?_, ?_⟩
    · x86_norm; exact hp.writable 464 (by simp)
    · x86_norm
      exact hp.apart 464 (by simp) 0xd581 8 (by decide)
  case av =>
    intro s hp
    apply Effect.avoids_codeRange
    x86_norm
    exact hp.apart 464 (by simp) 0xd581 24 (by decide)
  case next =>
    intro s hp
    exact boundary_ne_program outside (inProgram_of_textOffset 0xd589 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any
    0x10d589 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 456))
    (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d581 saveArgumentsBytes 8 8
  case mid =>
    intro s t hp hh ho
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hh (ho true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm; exact hp.writable 456 (by simp)
    · x86_norm
      exact hp.apart 456 (by simp) 0xd589 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.apart 456 (by simp) 0xd581 24 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd591 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any
    0x10d591 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 384))
    (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d581 saveArgumentsBytes 16 8
  case mid =>
    intro s t hp hh ho
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hh (ho true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm; exact hp.writable 384 (by simp)
    · x86_norm
      exact hp.apart 384 (by simp) 0xd591 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hp.apart 384 (by simp) 0xd581 24 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd599 (by decide))
  apply AdvanceTriple.block_end
  intro s t hp hh
  apply hh.weaken
  · x86_norm [saveArgumentsEffect]
  · x86_norm [saveArgumentsEffect]
    exact ⟨rfl, rfl, rfl⟩
  · intro i; cases i <;> x86_norm [saveArgumentsEffect]
  · x86_norm [saveArgumentsEffect]

end P256.Proofs.Verifying.Message
