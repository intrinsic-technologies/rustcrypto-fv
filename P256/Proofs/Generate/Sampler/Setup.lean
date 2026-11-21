import P256.Proofs.Program.Code
import P256.Proofs.SignatureFromDer.Parser.ReadSlice.Execution
import P256.Proofs.Common.Der.Memory.Compose
import P256.Proofs.Common.Der.Memory.Mov
import P256.Proofs.Common.Memory.Readable
import X86Proofs.Instructions.Mov.Generated.RM.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Generate.Sampler

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field P256.Proofs.SignatureFromDer.Parser.ReadSlice

attribute [local x86_compose] BitVec.add_zero

structure SetupPre (s : RamState) : Prop where
  rip : s.RIP = 0x100be1
  readable : MemReadable s ((Operand.reg 6 : Operand 64).read s) 16
  writable : P256.Proofs.Common.Der.Memory.MemWritable s (stackPtr s + 72) 8
  apart : RangeApart (stackPtr s + 72) 8 0x100be1 25
  separate : RangeApart (stackPtr s + 72) 8 ((Operand.reg 6 : Operand 64).read s) 16

def setupBytes : List UInt8 :=
  [0x49,0x89,0xf6,0x48,0x89,0x7c,0x24,0x48,0x48,0x8b,0x2e,0x4c,0x8b,0x6e,0x8,0x4c,0x8d,0x7c,0x24,0x50,0x4c,0x8d,0x64,0x24,0x28]

def setupEffect (s : RamState) : Effect :=
  { rip := 0x100bfa
    writes := [⟨(.reg 14 : Operand 64), (Operand.reg 6 : Operand 64).read s⟩,
      ⟨(.mem (stackPtr s + 72) : Operand 64), (Operand.reg 7 : Operand 64).read s⟩,
      ⟨(.reg 5 : Operand 64), memLoad s.external ((Operand.reg 6 : Operand 64).read s) 64⟩,
      ⟨(.reg 13 : Operand 64), memLoad s.external ((Operand.reg 6 : Operand 64).read s + 8) 64⟩,
      ⟨(.reg 15 : Operand 64), stackPtr s + 80⟩,
      ⟨(.reg 12 : Operand 64), stackPtr s + 40⟩] }

theorem setup_loaded {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x100be1 setupBytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xbe1 _ (by decide) (by decide +kernel)

theorem setup [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary SetupPre (codeRange 0x100be1 setupBytes) setupEffect := by
  have next (offset : Nat) (bound : offset < 118431) :
      Extracted.textAddress + BitVec.ofNat 64 offset ≠ boundary.rip :=
    boundary_ne_program outside (inProgram_of_textOffset offset bound)
  have h2 := next 0xbe9 (by decide)
  have h3 := next 0xbec (by decide)
  have h4 := next 0xbf0 (by decide)
  have h5 := next 0xbf5 (by decide)
  have h6 := next 0xbfa (by decide)
  advance_begin (mov_r64_r64_effect_step 0x100be1 0x49 0xf6 (by simp [RexWPrefix]) rfl)
  case next => intro _ _; exact next 0xbe4 (by decide)
  advance_then (P256.Proofs.Common.Der.Memory.mov_m64_r64_effect_step 0x100be4 0x48
    (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 72)) (by decide) rfl rfl)
  case mid =>
    intro s t hp hh ho
    refine ⟨P256.Proofs.Common.Der.Memory.StorePre.of_holds hh (ho true) (by x86_norm)
      (by x86_addr_obs) ?_ ?_, ?_, h2⟩
    · x86_norm
      exact hp.writable
    · x86_norm
      exact hp.apart.sub 3 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      x86_norm
      exact Effect.avoids_of_components_mem_rip (by x86_norm [Effect.components]) hp.apart
  advance_then (mov_r64_m64_effect_step 0x100be9 0x48 (by simp [RexWPrefix]) 5
    (.base 6 .none) (by decide) rfl rfl)
  case mid =>
    intro s t hp hh ho
    refine ⟨LoadPre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_, ?_, h3⟩
    · x86_norm
      change MemReadable s ((Operand.reg 6 : Operand 64).read s) 8
      have h := P256.Proofs.Common.Memory.memReadable_sub hp.readable 0 8 (by decide)
      rw [BitVec.add_zero] at h
      exact h
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
  advance_then (mov_r64_m64_effect_step 0x100bec 0x4c (by simp [RexWPrefix]) 5
    (.base 6 (.d8 8)) (by decide) rfl rfl)
  case mid =>
    intro s t hp hh ho
    refine ⟨LoadPre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_, ?_, h4⟩
    · x86_norm
      exact P256.Proofs.Common.Memory.memReadable_sub hp.readable 8 8 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
  advance_then (lea_r64_effect_step 0x100bf0 0x4c (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d8 80)) (by decide) rfl rfl)
  advance_then (lea_r64_effect_step 0x100bf5 0x4c (by simp [RexWPrefix]) 4
    (.sib 4 none 0 (.d8 40)) (by decide) rfl rfl)
  apply AdvanceTriple.block_end
  intro s t hp hh
  apply hh.weaken
  · x86_norm [setupEffect]
  · x86_norm [setupEffect, stackPtr]
    simp only [Operand.write, Operand.read]
    have low := hp.separate.sub 0 8 (by decide)
    simp only [BitVec.add_zero] at low
    have high := hp.separate.sub 8 8 (by decide)
    rw [memLoad_memStore_of_rangeApart _ _ _ _ 64 low,
      memLoad_memStore_of_rangeApart _ _ _ _ 64 high]
    exact ⟨rfl,⟨rfl,rfl⟩,rfl,rfl,rfl,rfl⟩
  · intro i; cases i <;> x86_norm [setupEffect]
  · x86_norm [setupEffect, stackPtr]
    rfl
  all_goals first
    | (simp only [BitVec.add_zero]; repeat constructor <;> rfl)
    | exact codeRange_slice_subset 0x100be1 setupBytes 3 5
    | exact codeRange_slice_subset 0x100be1 setupBytes 8 3
    | exact codeRange_slice_subset 0x100be1 setupBytes 11 4
    | exact codeRange_slice_subset 0x100be1 setupBytes 15 5
    | exact codeRange_slice_subset 0x100be1 setupBytes 20 5

end P256.Proofs.Generate.Sampler
