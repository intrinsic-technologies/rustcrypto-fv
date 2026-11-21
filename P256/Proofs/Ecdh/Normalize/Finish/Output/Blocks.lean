import P256.Proofs.Program.Code
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Instructions.Bswap
import P256.Proofs.Common.Instructions.CrossPageStore.Mov
import P256.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.MovLoad.Triple

set_option autoImplicit false

namespace P256.Proofs.Ecdh.Normalize.Finish.Output

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program
open P256.Proofs.Common.Instructions (bswap64 bswap_r64_effect_step)
open P256.Proofs.Common.Instructions.CrossPageStore (Pre Writable mov_m64_r64_effect_step_any)
open P256.Proofs.Common.Field (AdvanceTriple)

def outputEffect (s : RamState) : Effect :=
  { rip := 0x10056a
    writes := [
      ⟨(.reg 0 : Operand 64), bswap64 ((Operand.mem (stackPtr s + 1040) : Operand 64).read s)⟩,
      ⟨(.reg 1 : Operand 64), bswap64 ((Operand.mem (stackPtr s + 1032) : Operand 64).read s)⟩,
      ⟨(.reg 2 : Operand 64), bswap64 ((Operand.mem (stackPtr s + 1024) : Operand 64).read s)⟩,
      ⟨(.reg 6 : Operand 64), bswap64 ((Operand.mem (stackPtr s + 1016) : Operand 64).read s)⟩,
      ⟨(.mem (s.regValue .rbx + 0) : Operand 64), bswap64 ((Operand.mem (stackPtr s + 1040) : Operand 64).read s)⟩,
      ⟨(.mem (s.regValue .rbx + 8) : Operand 64), bswap64 ((Operand.mem (stackPtr s + 1032) : Operand 64).read s)⟩,
      ⟨(.mem (s.regValue .rbx + 16) : Operand 64), bswap64 ((Operand.mem (stackPtr s + 1024) : Operand 64).read s)⟩,
      ⟨(.mem (s.regValue .rbx + 24) : Operand 64), bswap64 ((Operand.mem (stackPtr s + 1016) : Operand 64).read s)⟩] }

def outputBytes : List UInt8 := [72, 139, 132, 36, 16, 4, 0, 0, 72, 15, 200, 72, 139, 140, 36, 8, 4, 0, 0, 72, 15, 201, 72, 139, 148, 36, 0, 4, 0, 0, 72, 15, 202, 72, 139, 180, 36, 248, 3, 0, 0, 72, 15, 206, 72, 137, 3, 72, 137, 75, 8, 72, 137, 83, 16, 72, 137, 115, 24]

structure OutputPre (s : RamState) : Prop where
  rip : s.RIP = 0x10052f
  readable : ∀ i ∈ ([1016,1024,1032,1040] : List (BitVec 64)),
    MemReadable s (stackPtr s + i) 8
  writable : Writable s (s.regValue .rbx) 32
  apart : RangeApart (s.regValue .rbx) 32 0x10052f 59

theorem output_block [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary OutputPre (codeRange 0x10052f outputBytes)
      (Effect.post outputEffect) := by
  have apart_slice {a : BitVec 64} (h : RangeApart a 32 0x10052f 59)
      (off pc len : Nat) (hoff : off + 8 ≤ 32) (hpc : pc + len ≤ 59) :
      RangeApart (a + BitVec.ofNat 64 off) 8 (0x10052f + BitVec.ofNat 64 pc) len := by
    intro i hi j hj
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using
      h (off + i) (by omega) (pc + j) (by omega)
  advance_begin (mov_r64_m64_effect_step 0x10052f 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 1040)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    refine ⟨hP.rip, ?_⟩
    x86_norm
    exact hP.readable 1040 (by simp)
  case next =>
    intro s hP
    exact boundary_ne_program outside (inProgram_of_textOffset 0x537 (by decide))
  advance_then (bswap_r64_effect_step 0x100537 0)
  case sub => exact codeRange_slice_subset 0x10052f outputBytes 8 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [P256.Proofs.Common.Instructions.bswapR64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x53a (by decide))
  advance_then (mov_r64_m64_effect_step 0x10053a 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d32 1032)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10052f outputBytes 11 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 1032 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [movR64M64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x542 (by decide))
  advance_then (bswap_r64_effect_step 0x100542 1)
  case sub => exact codeRange_slice_subset 0x10052f outputBytes 19 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [P256.Proofs.Common.Instructions.bswapR64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x545 (by decide))
  advance_then (mov_r64_m64_effect_step 0x100545 0x48 (by simp [RexWPrefix]) 2
    (.sib 4 none 0 (.d32 1024)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10052f outputBytes 22 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 1024 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [movR64M64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x54d (by decide))
  advance_then (bswap_r64_effect_step 0x10054d 2)
  case sub => exact codeRange_slice_subset 0x10052f outputBytes 30 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [P256.Proofs.Common.Instructions.bswapR64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x550 (by decide))
  advance_then (mov_r64_m64_effect_step 0x100550 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d32 1016)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10052f outputBytes 33 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 1016 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [movR64M64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x558 (by decide))
  advance_then (bswap_r64_effect_step 0x100558 6)
  case sub => exact codeRange_slice_subset 0x10052f outputBytes 41 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [P256.Proofs.Common.Instructions.bswapR64Effect, Effect.components, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x55b (by decide))
  advance_then (mov_m64_r64_effect_step_any 0x10055b 0x48 (by simp [RexWPrefix])
    0 (.base 3 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10052f outputBytes 44 3
  case mid =>
    intro s t hP hH hO
    refine ⟨Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable.add 0 (len := 8) (by decide)
    · x86_norm
      exact apart_slice hP.apart 0 44 3 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact apart_slice hP.apart 0 0 59 (by decide) (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x55e (by decide))
  advance_then (mov_m64_r64_effect_step_any 0x10055e 0x48 (by simp [RexWPrefix])
    1 (.base 3 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10052f outputBytes 47 4
  case mid =>
    intro s t hP hH hO
    refine ⟨Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable.add 8 (len := 8) (by decide)
    · x86_norm
      exact apart_slice hP.apart 8 47 4 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact apart_slice hP.apart 8 0 59 (by decide) (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x562 (by decide))
  advance_then (mov_m64_r64_effect_step_any 0x100562 0x48 (by simp [RexWPrefix])
    2 (.base 3 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10052f outputBytes 51 4
  case mid =>
    intro s t hP hH hO
    refine ⟨Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable.add 16 (len := 8) (by decide)
    · x86_norm
      exact apart_slice hP.apart 16 51 4 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact apart_slice hP.apart 16 0 59 (by decide) (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x566 (by decide))
  advance_then (mov_m64_r64_effect_step_any 0x100566 0x48 (by simp [RexWPrefix])
    6 (.base 3 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10052f outputBytes 55 4
  case mid =>
    intro s t hP hH hO
    refine ⟨Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable.add 24 (len := 8) (by decide)
    · x86_norm
      exact apart_slice hP.apart 24 55 4 (by decide) (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact apart_slice hP.apart 24 0 59 (by decide) (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x56a (by decide))
  apply AdvanceTriple.block_end
  intro s u hP hH
  exact hH

end P256.Proofs.Ecdh.Normalize.Finish.Output
