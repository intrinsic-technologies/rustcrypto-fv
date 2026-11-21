import P256.Proofs.Generate.Wrapper.State
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Instructions.CrossPageStore
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Generate.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions.CrossPageStore (Writable)

structure DescriptorPre (s : RamState) : Prop where
  rip : s.RIP = 0x106d91
  writable : ∀ off ∈ ([8,16] : List Nat), Writable s (stackPtr s+BitVec.ofNat 64 off) 8
  apart : ∀ off ∈ ([8,16] : List Nat), ∀ codeOffset codeLen : Nat,
    codeOffset+codeLen ≤ 118431 →
    RangeApart (stackPtr s+BitVec.ofNat 64 off) 8
      (Extracted.textAddress+BitVec.ofNat 64 codeOffset) codeLen

def descriptorBytes : List UInt8 :=
  [72,137,76,36,8,72,137,68,36,16,76,141,124,36,80,72,141,116,36,8,76,137,255]

def descriptorEffect (s : RamState) : Effect :=
  { rip := 0x106da8
    writes := [⟨(.mem (stackPtr s+8) : Operand 64),s.regValue .rcx⟩,
      ⟨(.mem (stackPtr s+16) : Operand 64),s.regValue .rax⟩,
      ⟨(.reg 15 : Operand 64),stackPtr s+80⟩,
      ⟨(.reg 6 : Operand 64),stackPtr s+8⟩,
      ⟨(.reg 7 : Operand 64),stackPtr s+80⟩] }

theorem descriptor_block [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary DescriptorPre (codeRange 0x106d91 descriptorBytes)
      (Effect.post descriptorEffect) := by
  advance_begin (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any
    0x106d91 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 8))
    (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    exact ⟨h.rip,h.writable 8 (by simp),h.apart 8 (by simp) 0x6d91 5 (by decide)⟩
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0x6d96 (by decide))
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm
    exact h.apart 8 (by simp) 0x6d91 23 (by decide)
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any
    0x106d96 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 16))
    (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x106d91 descriptorBytes 5 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_,?_,?_⟩
    · x86_norm
      exact hP.writable 16 (by simp)
    · x86_norm
      exact hP.apart 16 (by simp) 0x6d96 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 16 (by simp) 0x6d91 23 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6d9b (by decide))
  advance_then (lea_r64_effect_step 0x106d9b 0x4c (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d8 80)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x106d91 descriptorBytes 10 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x6da0 (by decide))⟩
  advance_then (lea_r64_effect_step 0x106da0 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x106d91 descriptorBytes 15 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x6da5 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x106da5 0x4c 0xff (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x106d91 descriptorBytes 20 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm),Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x6da8 (by decide))⟩
  advance_finish [descriptorEffect,stackPtr,Operand.read_reg64,State.regValue,gprNumber]

end P256.Proofs.Generate.Wrapper
