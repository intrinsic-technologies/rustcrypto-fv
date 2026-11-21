import P256.Proofs.Verifying.Core.Digest.Finish.CopyBlock
import P256.Proofs.Common.Instructions.Bswap

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Finish.Tail.Encode

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions (bswap64 bswap_r64_effect_step)

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10e04c
  readable : ∀ i ∈ ([128,136,144,152] : List Nat), MemReadable s (rspOf s+BitVec.ofNat 64 i) 8
  writable : ∀ i ∈ ([392,400,408,416] : List Nat), MemWritable s (rspOf s+BitVec.ofNat 64 i) 8
  apart : ∀ i ∈ ([392,400,408,416] : List Nat), ∀ off len : Nat, off+len ≤ 118431 →
    RangeApart (rspOf s+BitVec.ofNat 64 i) 8 (Extracted.textAddress+BitVec.ofNat 64 off) len

def bytes : List UInt8 :=
  [0x48,0x8b,0x84,0x24,0x98,0x0,0x0,0x0,0x48,0xf,0xc8,0x48,0x8b,0x8c,0x24,0x90,0x0,0x0,0x0,0x48,0xf,0xc9,0x48,0x8b,0x94,0x24,0x80,0x0,0x0,0x0,0x48,0x8b,0xb4,0x24,0x88,0x0,0x0,0x0,0x48,0xf,0xce,0x48,0xf,0xca,0x48,0x89,0x84,0x24,0x88,0x1,0x0,0x0,0x48,0x89,0x8c,0x24,0x90,0x1,0x0,0x0,0x48,0x89,0xb4,0x24,0x98,0x1,0x0,0x0,0x48,0x89,0x94,0x24,0xa0,0x1,0x0,0x0]

def effect (s : RamState) : Effect :=
  { rip := 0x10e098
    writes := [
      ⟨(.reg 0 : Operand 64), bswap64 (memLoad s.external (rspOf s+152) 64)⟩,
      ⟨(.reg 1 : Operand 64), bswap64 (memLoad s.external (rspOf s+144) 64)⟩,
      ⟨(.reg 2 : Operand 64), bswap64 (memLoad s.external (rspOf s+128) 64)⟩,
      ⟨(.reg 6 : Operand 64), bswap64 (memLoad s.external (rspOf s+136) 64)⟩,
      ⟨(.mem (rspOf s+392) : Operand 64), bswap64 (memLoad s.external (rspOf s+152) 64)⟩,
      ⟨(.mem (rspOf s+400) : Operand 64), bswap64 (memLoad s.external (rspOf s+144) 64)⟩,
      ⟨(.mem (rspOf s+408) : Operand 64), bswap64 (memLoad s.external (rspOf s+136) 64)⟩,
      ⟨(.mem (rspOf s+416) : Operand 64), bswap64 (memLoad s.external (rspOf s+128) 64)⟩] }

set_option maxHeartbeats 1200000 in
theorem block [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10e04c bytes) (Effect.post effect) := by
  advance_begin (mov_r64_m64_effect_step 0x10e04c 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 152)) (by decide) rfl rfl)
  case pre => intro s hp; exact ⟨hp.rip,hp.readable 152 (by simp)⟩
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0xe054 (by decide))
  advance_then (bswap_r64_effect_step 0x10e054 0)
  case sub => exact codeRange_slice_subset 0x10e04c bytes 8 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm),?_,?_⟩
    · apply Effect.Avoids.of_noMem
      simp [P256.Proofs.Common.Instructions.bswapR64Effect,Effect.components,Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xe057 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10e057 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 144)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10e04c bytes 11 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,?_,?_⟩
    · x86_norm
      exact hP.readable 144 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xe05f (by decide))
  advance_then (bswap_r64_effect_step 0x10e05f 1)
  case sub => exact codeRange_slice_subset 0x10e04c bytes 19 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm),?_,?_⟩
    · apply Effect.Avoids.of_noMem
      simp [P256.Proofs.Common.Instructions.bswapR64Effect,Effect.components,Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xe062 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10e062 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 128)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10e04c bytes 22 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,?_,?_⟩
    · x86_norm
      exact hP.readable 128 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xe06a (by decide))
  advance_then (mov_r64_m64_effect_step 0x10e06a 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 136)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10e04c bytes 30 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_,?_,?_⟩
    · x86_norm
      exact hP.readable 136 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xe072 (by decide))
  advance_then (bswap_r64_effect_step 0x10e072 6)
  case sub => exact codeRange_slice_subset 0x10e04c bytes 38 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm),?_,?_⟩
    · apply Effect.Avoids.of_noMem
      simp [P256.Proofs.Common.Instructions.bswapR64Effect,Effect.components,Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xe075 (by decide))
  advance_then (bswap_r64_effect_step 0x10e075 2)
  case sub => exact codeRange_slice_subset 0x10e04c bytes 41 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm),?_,?_⟩
    · apply Effect.Avoids.of_noMem
      simp [P256.Proofs.Common.Instructions.bswapR64Effect,Effect.components,Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xe078 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10e078 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 392)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10e04c bytes 44 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_,?_,?_⟩
    · x86_norm
      exact hP.writable 392 (by simp)
    · x86_norm
      exact hP.apart 392 (by simp) 0xe078 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 392 (by simp) 0xe04c 76 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xe080 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10e080 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 400)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10e04c bytes 52 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_,?_,?_⟩
    · x86_norm
      exact hP.writable 400 (by simp)
    · x86_norm
      exact hP.apart 400 (by simp) 0xe080 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 400 (by simp) 0xe04c 76 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xe088 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10e088 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 408)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10e04c bytes 60 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_,?_,?_⟩
    · x86_norm
      exact hP.writable 408 (by simp)
    · x86_norm
      exact hP.apart 408 (by simp) 0xe088 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 408 (by simp) 0xe04c 76 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xe090 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10e090 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 416)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10e04c bytes 68 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_,?_,?_⟩
    · x86_norm
      exact hP.writable 416 (by simp)
    · x86_norm
      exact hP.apart 416 (by simp) 0xe090 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 416 (by simp) 0xe04c 76 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xe098 (by decide))
  advance_finish [effect]

end P256.Proofs.Verifying.Core.Finish.Tail.Encode
