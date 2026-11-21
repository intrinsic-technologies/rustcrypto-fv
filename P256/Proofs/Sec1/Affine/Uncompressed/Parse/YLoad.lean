import P256.Proofs.Program.Code
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Instructions.Bswap
import X86Proofs.Instructions.MovLoad.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Parse

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)
open P256.Proofs.Common.Instructions (bswap64 bswap_r64_effect_step)

structure yLoadPre (s : RamState) : Prop where
  rip : s.RIP = 0x110635
  readable : ∀ off ∈ ([33, 41, 49, 57] : List (BitVec 64)),
    MemReadable s ((Operand.reg 6 : Operand 64).read s + off) 8

def yLoadBytes : List UInt8 :=
  [72, 139, 70, 33, 72, 139, 78, 41, 72, 139, 126, 49, 72, 139, 86, 57, 72, 15, 200, 72, 15, 201, 72, 15, 207, 72, 15, 202]

def yLoadEffect (s : RamState) : Effect :=
  { rip := 0x110651
    writes := [⟨(.reg 0 : Operand 64), bswap64 (memLoad s.external ((Operand.reg 6 : Operand 64).read s + 33) 64)⟩,
      ⟨(.reg 1 : Operand 64), bswap64 (memLoad s.external ((Operand.reg 6 : Operand 64).read s + 41) 64)⟩,
      ⟨(.reg 7 : Operand 64), bswap64 (memLoad s.external ((Operand.reg 6 : Operand 64).read s + 49) 64)⟩,
      ⟨(.reg 2 : Operand 64), bswap64 (memLoad s.external ((Operand.reg 6 : Operand 64).read s + 57) 64)⟩] }

theorem y_load [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary yLoadPre (codeRange 0x110635 yLoadBytes)
      (Effect.post yLoadEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x110635 0x48 (by simp [RexWPrefix]) 0
    (.base 6 (.d8 33)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    exact ⟨h.rip, h.readable 33 (by simp)⟩
  case next =>
    intro _ _
    exact boundary_ne_program outside (inProgram_of_textOffset 0x10639 (by decide))
  advance_then (mov_r64_m64_effect_step 0x110639 0x48 (by simp [RexWPrefix]) 1
    (.base 6 (.d8 41)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110635 yLoadBytes 4 4
  case mid =>
    intro s t hP hH hO
    refine ⟨X86Proofs.LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 41 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1063d (by decide))
  advance_then (mov_r64_m64_effect_step 0x11063d 0x48 (by simp [RexWPrefix]) 7
    (.base 6 (.d8 49)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110635 yLoadBytes 8 4
  case mid =>
    intro s t hP hH hO
    refine ⟨X86Proofs.LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 49 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10641 (by decide))
  advance_then (mov_r64_m64_effect_step 0x110641 0x48 (by simp [RexWPrefix]) 2
    (.base 6 (.d8 57)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110635 yLoadBytes 12 4
  case mid =>
    intro s t hP hH hO
    refine ⟨X86Proofs.LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 57 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10645 (by decide))
  advance_then (bswap_r64_effect_step 0x110645 0)
  case sub => exact codeRange_slice_subset 0x110635 yLoadBytes 16 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem
      (by simp [P256.Proofs.Common.Instructions.bswapR64Effect, Effect.components, Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x10648 (by decide))⟩
  advance_then (bswap_r64_effect_step 0x110648 1)
  case sub => exact codeRange_slice_subset 0x110635 yLoadBytes 19 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem
      (by simp [P256.Proofs.Common.Instructions.bswapR64Effect, Effect.components, Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x1064b (by decide))⟩
  advance_then (bswap_r64_effect_step 0x11064b 7)
  case sub => exact codeRange_slice_subset 0x110635 yLoadBytes 22 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem
      (by simp [P256.Proofs.Common.Instructions.bswapR64Effect, Effect.components, Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x1064e (by decide))⟩
  advance_then (bswap_r64_effect_step 0x11064e 2)
  case sub => exact codeRange_slice_subset 0x110635 yLoadBytes 25 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem
      (by simp [P256.Proofs.Common.Instructions.bswapR64Effect, Effect.components, Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x10651 (by decide))⟩
  advance_finish [yLoadEffect]

end P256.Proofs.Sec1.Affine.Uncompressed.Parse
