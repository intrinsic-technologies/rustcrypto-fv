import P256.Proofs.Verifying.Core.Memory
import P256.Proofs.Verifying.Core.Prepare.Pointers
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Instructions.CrossPageStore
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Digest.Setup

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field

attribute [local x86_compose] movM8Imm8Effect

private theorem byteStoreLocal (p : BitVec 64) (am : AddrMode) (imm : BitVec 8) :
    Effect.Local (movM8Imm8Effect p am imm) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [movM8Imm8Effect, storeEffect, storeAddrAt, AddrMode.addr_obs h]
  · intro s
    simp [movM8Imm8Effect, storeEffect, Write.Full, Operand.Full]

attribute [local x86_local] byteStoreLocal

structure PrefixPre (s : RamState) : Prop where
  rip : s.RIP = 0x10dbba
  writable : MemWritable s (rspOf s + 128) 1
  apart : ∀ off len : Nat, off + len ≤ 118431 →
    RangeApart (rspOf s + 128) 1 (Extracted.textAddress + BitVec.ofNat 64 off) len

def prefixBytes : List UInt8 :=
  [0x48, 0x8d, 0x84, 0x24, 0x80, 0x0, 0x0, 0x0, 0xc6, 0x84, 0x24, 0x80, 0x0, 0x0, 0x0, 0x0, 0xc6, 0x84, 0x24, 0x80, 0x0, 0x0, 0x0, 0x0, 0xc6, 0x84, 0x24, 0x80, 0x0, 0x0, 0x0, 0x0]

def prefixEffect (s : RamState) : Effect :=
  { rip := 0x10dbda
    writes := [⟨(.reg 0 : Operand 64), rspOf s + 128⟩,
      ⟨(.mem (rspOf s + 128) : Operand 8), 0⟩] }

theorem prefix_block [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary PrefixPre (codeRange 0x10dbba prefixBytes) (Effect.post prefixEffect) := by
  advance_begin (lea_r64_effect_step 0x10dbba 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 128)) (by decide) rfl rfl)
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0xdbc2 (by decide))
  advance_then (mov_m8_imm8_effect_step 0x10dbc2 (.sib 4 none 0 (.d32 128)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10dbba prefixBytes 8 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable
    · x86_norm
      exact hP.apart 0xdbc2 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 0xdbba 32 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xdbca (by decide))
  advance_then (mov_m8_imm8_effect_step 0x10dbca (.sib 4 none 0 (.d32 128)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10dbba prefixBytes 16 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable
    · x86_norm
      exact hP.apart 0xdbca 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 0xdbba 32 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xdbd2 (by decide))
  advance_then (mov_m8_imm8_effect_step 0x10dbd2 (.sib 4 none 0 (.d32 128)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10dbba prefixBytes 24 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable
    · x86_norm
      exact hP.apart 0xdbd2 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 0xdbba 32 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xdbda (by decide))
  advance_finish [prefixEffect]

end P256.Proofs.Verifying.Core.Digest.Setup
