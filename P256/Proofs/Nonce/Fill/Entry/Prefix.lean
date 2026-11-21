import P256.Proofs.Nonce.Fill.Work
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Entry

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field

structure PrefixPre (s : RamState) : Prop where
  rip : s.RIP = 0x107341
  writable : ∀ off ∈ ([40] : List Nat), MemWritable s (stackPtr s + BitVec.ofNat 64 off) 8
  apart : ∀ off ∈ ([40] : List Nat), ∀ co cl : Nat, co + cl ≤ 118431 →
    RangeApart (stackPtr s + BitVec.ofNat 64 off) 8 (Extracted.textAddress + BitVec.ofNat 64 co) cl

def prefixBytes : List UInt8 :=
  [73, 137, 213, 72, 137, 116, 36, 40, 72, 141, 79, 8]

def prefixEffect (s : RamState) : Effect :=
  { rip := 0x10734d
    writes := [⟨(.reg 13 : Operand 64), s.regValue .rdx⟩,
      ⟨(.mem (stackPtr s + 40) : Operand 64), s.regValue .rsi⟩,
      ⟨(.reg 1 : Operand 64), s.regValue .rdi + 8⟩] }

theorem prefix_block [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary PrefixPre (codeRange 0x107341 prefixBytes) (Effect.post prefixEffect) := by
  advance_begin (mov_r64_r64_effect_step 0x107341 0x49 0xd5 (by simp [RexWPrefix]) rfl)
  case next => intro s h; exact boundary_ne_program outside (inProgram_of_textOffset 0x7344 (by decide))
  advance_then (mov_m64_r64_effect_step 0x107344 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 40)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107341 prefixBytes 3 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 40 (by simp)
    · x86_norm
      exact hP.apart 40 (by simp) 0x7344 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 40 (by simp) 0x7341 12 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x7349 (by decide))
  advance_then (lea_r64_effect_step 0x107349 0x48 (by simp [RexWPrefix]) 1 (.base 7 (.d8 8)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107341 prefixBytes 8 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x734d (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [prefixEffect]
  · x86_norm [prefixEffect]
    exact ⟨rfl, rfl, rfl⟩
  · intro flag; cases flag <;> x86_norm [prefixEffect]
  · x86_norm [prefixEffect, stackPtr, Operand.read_reg64, State.regValue]

end P256.Proofs.Nonce.Fill.Entry
