import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Instructions.Bswap
import P256.Proofs.Program.Code
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point.Encode.Block

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Instructions
open P256.Proofs.Common.Field (AdvanceTriple)

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10d153
  readable : ∀ off ∈ ([528,536,544,552] : List Nat),
    MemReadable s (stackPtr s + BitVec.ofNat 64 off) 8
  writable : ∀ off ∈ ([432,440,448,456] : List Nat),
    MemWritable s (stackPtr s + BitVec.ofNat 64 off) 8
  codeApart : ∀ off ∈ ([432,440,448,456] : List Nat), ∀ codeOffset len : Nat,
    codeOffset+len ≤ 118431 → RangeApart (stackPtr s + BitVec.ofNat 64 off) 8
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) len

def bytes : List UInt8 :=
  [0x48, 0x8b, 0x84, 0x24, 0x28, 0x2, 0x0, 0x0, 0x48, 0xf, 0xc8, 0x48, 0x8b, 0x8c, 0x24, 0x20, 0x2, 0x0, 0x0, 0x48, 0xf, 0xc9, 0x48, 0x8b, 0x94, 0x24, 0x18, 0x2, 0x0, 0x0, 0x48, 0xf, 0xca, 0x48, 0x8b, 0xb4, 0x24, 0x10, 0x2, 0x0, 0x0, 0x48, 0xf, 0xce, 0x48, 0x89, 0x84, 0x24, 0xb0, 0x1, 0x0, 0x0, 0x48, 0x89, 0x8c, 0x24, 0xb8, 0x1, 0x0, 0x0, 0x48, 0x89, 0x94, 0x24, 0xc0, 0x1, 0x0, 0x0, 0x48, 0x89, 0xb4, 0x24, 0xc8, 0x1, 0x0, 0x0]

def effect (s : RamState) : Effect :=
  { rip := 0x10d19f
    writes := [
      ⟨(.reg 0 : Operand 64), bswap64 (memLoad s.external (stackPtr s+552) 64)⟩,
      ⟨(.reg 1 : Operand 64), bswap64 (memLoad s.external (stackPtr s+544) 64)⟩,
      ⟨(.reg 2 : Operand 64), bswap64 (memLoad s.external (stackPtr s+536) 64)⟩,
      ⟨(.reg 6 : Operand 64), bswap64 (memLoad s.external (stackPtr s+528) 64)⟩,
      ⟨(.mem (stackPtr s+432) : Operand 64), bswap64 (memLoad s.external (stackPtr s+552) 64)⟩,
      ⟨(.mem (stackPtr s+440) : Operand 64), bswap64 (memLoad s.external (stackPtr s+544) 64)⟩,
      ⟨(.mem (stackPtr s+448) : Operand 64), bswap64 (memLoad s.external (stackPtr s+536) 64)⟩,
      ⟨(.mem (stackPtr s+456) : Operand 64), bswap64 (memLoad s.external (stackPtr s+528) 64)⟩] }

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem correct [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10d153 bytes) (Effect.post effect) := by
  advance_begin (mov_r64_m64_effect_step 0x10d153 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 552)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    exact ⟨h.rip,h.readable 552 (by simp)⟩
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0xd15b (by decide))
  advance_then (bswap_r64_effect_step 0x10d15b 0)
  case sub => exact codeRange_slice_subset 0x10d153 bytes 8 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, Effect.Avoids.of_noMem (by simp [bswapR64Effect,Effect.components,Component.Covers]) _, ?_⟩
    exact boundary_ne_program outside (inProgram_of_textOffset 0xd15e (by decide))
  advance_then (mov_r64_m64_effect_step 0x10d15e 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 544)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d153 bytes 11 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.readable 544 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [movR64M64Effect,Effect.components,Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd166 (by decide))
  advance_then (bswap_r64_effect_step 0x10d166 1)
  case sub => exact codeRange_slice_subset 0x10d153 bytes 19 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, Effect.Avoids.of_noMem (by simp [bswapR64Effect,Effect.components,Component.Covers]) _, ?_⟩
    exact boundary_ne_program outside (inProgram_of_textOffset 0xd169 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10d169 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 536)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d153 bytes 22 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.readable 536 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [movR64M64Effect,Effect.components,Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd171 (by decide))
  advance_then (bswap_r64_effect_step 0x10d171 2)
  case sub => exact codeRange_slice_subset 0x10d153 bytes 30 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, Effect.Avoids.of_noMem (by simp [bswapR64Effect,Effect.components,Component.Covers]) _, ?_⟩
    exact boundary_ne_program outside (inProgram_of_textOffset 0xd174 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10d174 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 528)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d153 bytes 33 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.readable 528 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [movR64M64Effect,Effect.components,Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd17c (by decide))
  advance_then (bswap_r64_effect_step 0x10d17c 6)
  case sub => exact codeRange_slice_subset 0x10d153 bytes 41 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, Effect.Avoids.of_noMem (by simp [bswapR64Effect,Effect.components,Component.Covers]) _, ?_⟩
    exact boundary_ne_program outside (inProgram_of_textOffset 0xd17f (by decide))
  advance_then (mov_m64_r64_effect_step 0x10d17f 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 432)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d153 bytes 44 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable 432 (by simp)
    · x86_norm [stackPtr]
      exact hP.codeApart 432 (by simp) 0xd17f 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hP.codeApart 432 (by simp) 0xd153 76 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd187 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10d187 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 440)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d153 bytes 52 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable 440 (by simp)
    · x86_norm [stackPtr]
      exact hP.codeApart 440 (by simp) 0xd187 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hP.codeApart 440 (by simp) 0xd153 76 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd18f (by decide))
  advance_then (mov_m64_r64_effect_step 0x10d18f 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 448)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d153 bytes 60 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable 448 (by simp)
    · x86_norm [stackPtr]
      exact hP.codeApart 448 (by simp) 0xd18f 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hP.codeApart 448 (by simp) 0xd153 76 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd197 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10d197 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 456)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d153 bytes 68 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable 456 (by simp)
    · x86_norm [stackPtr]
      exact hP.codeApart 456 (by simp) 0xd197 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hP.codeApart 456 (by simp) 0xd153 76 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd19f (by decide))
  advance_finish [effect,stackPtr,Operand.read_reg64,State.regValue,gprNumber,rexR,rexB,modrmReg,modrmRm]

end P256.Proofs.Signing.Core.Iteration.Point.Encode.Block
