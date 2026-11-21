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

structure xLoadPre (s : RamState) : Prop where
  rip : s.RIP = 0x110820
  readable : ∀ off ∈ ([1, 9, 17, 25] : List (BitVec 64)),
    MemReadable s ((Operand.reg 5 : Operand 64).read s + off) 8

def xLoadBytes : List UInt8 :=
  [72, 139, 69, 1, 72, 139, 77, 9, 72, 139, 117, 17, 72, 139, 85, 25, 72, 15, 200, 72, 15, 201, 72, 15, 206, 72, 15, 202]

def xLoadEffect (s : RamState) : Effect :=
  { rip := 0x11083c
    writes := [⟨(.reg 0 : Operand 64), bswap64 (memLoad s.external ((Operand.reg 5 : Operand 64).read s + 1) 64)⟩,
      ⟨(.reg 1 : Operand 64), bswap64 (memLoad s.external ((Operand.reg 5 : Operand 64).read s + 9) 64)⟩,
      ⟨(.reg 6 : Operand 64), bswap64 (memLoad s.external ((Operand.reg 5 : Operand 64).read s + 17) 64)⟩,
      ⟨(.reg 2 : Operand 64), bswap64 (memLoad s.external ((Operand.reg 5 : Operand 64).read s + 25) 64)⟩] }

theorem x_load [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary xLoadPre (codeRange 0x110820 xLoadBytes)
      (Effect.post xLoadEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x110820 0x48 (by simp [RexWPrefix]) 0
    (.base 5 (.d8 1)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    exact ⟨h.rip, h.readable 1 (by simp)⟩
  case next =>
    intro _ _
    exact boundary_ne_program outside (inProgram_of_textOffset 0x10824 (by decide))
  advance_then (mov_r64_m64_effect_step 0x110824 0x48 (by simp [RexWPrefix]) 1
    (.base 5 (.d8 9)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110820 xLoadBytes 4 4
  case mid =>
    intro s t hP hH hO
    refine ⟨X86Proofs.LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 9 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10828 (by decide))
  advance_then (mov_r64_m64_effect_step 0x110828 0x48 (by simp [RexWPrefix]) 6
    (.base 5 (.d8 17)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110820 xLoadBytes 8 4
  case mid =>
    intro s t hP hH hO
    refine ⟨X86Proofs.LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 17 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1082c (by decide))
  advance_then (mov_r64_m64_effect_step 0x11082c 0x48 (by simp [RexWPrefix]) 2
    (.base 5 (.d8 25)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x110820 xLoadBytes 12 4
  case mid =>
    intro s t hP hH hO
    refine ⟨X86Proofs.LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 25 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10830 (by decide))
  advance_then (bswap_r64_effect_step 0x110830 0)
  case sub => exact codeRange_slice_subset 0x110820 xLoadBytes 16 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem
      (by simp [P256.Proofs.Common.Instructions.bswapR64Effect, Effect.components, Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x10833 (by decide))⟩
  advance_then (bswap_r64_effect_step 0x110833 1)
  case sub => exact codeRange_slice_subset 0x110820 xLoadBytes 19 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem
      (by simp [P256.Proofs.Common.Instructions.bswapR64Effect, Effect.components, Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x10836 (by decide))⟩
  advance_then (bswap_r64_effect_step 0x110836 6)
  case sub => exact codeRange_slice_subset 0x110820 xLoadBytes 22 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem
      (by simp [P256.Proofs.Common.Instructions.bswapR64Effect, Effect.components, Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x10839 (by decide))⟩
  advance_then (bswap_r64_effect_step 0x110839 2)
  case sub => exact codeRange_slice_subset 0x110820 xLoadBytes 25 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem
      (by simp [P256.Proofs.Common.Instructions.bswapR64Effect, Effect.components, Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x1083c (by decide))⟩
  advance_finish [xLoadEffect]

end P256.Proofs.Sec1.Affine.Uncompressed.Parse
