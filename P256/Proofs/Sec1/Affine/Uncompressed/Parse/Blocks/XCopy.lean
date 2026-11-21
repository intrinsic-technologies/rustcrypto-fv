import P256.Proofs.SignatureFromDer.Parser.ReadSlice.Execution
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Encoding.Serialize.Tail.ByteOps.Store
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovLoad.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Parse.Blocks

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SignatureFromDer.Parser.ReadSlice
open P256.Proofs.Common.Instructions (mov_m8_r8_legacy_effect_step mov_m8_r8_effect_step)
open P256.Proofs.Common.Instructions.CrossPageStore (Writable)

structure XCopyPre (s : RamState) : Prop where
  rip : s.RIP = 0x11095f
  readable : ∀ off ∈ ([376, 384, 392, 400] : List Nat),
    MemReadable s (stackPtr s + BitVec.ofNat 64 off) 8
  writable : ∀ off n, (off,n) ∈ ([(192, 8), (184, 8), (176, 8), (168, 8)] : List (Nat × Nat)) →
    Writable s (stackPtr s + BitVec.ofNat 64 off) n
  codeApart : ∀ off n, (off,n) ∈ ([(168,8), (176,8), (184,8), (192,8)] : List (Nat × Nat)) →
    RangeApart (stackPtr s + BitVec.ofNat 64 off) n 0x11095f 64

def xCopyBytes : List UInt8 :=
  [0x48, 0x8b, 0x84, 0x24, 0x90, 0x1, 0x0, 0x0, 0x48, 0x89, 0x84, 0x24, 0xc0, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x84, 0x24, 0x88, 0x1, 0x0, 0x0, 0x48, 0x89, 0x84, 0x24, 0xb8, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x84, 0x24, 0x78, 0x1, 0x0, 0x0, 0x48, 0x8b, 0x8c, 0x24, 0x80, 0x1, 0x0, 0x0, 0x48, 0x89, 0x8c, 0x24, 0xb0, 0x0, 0x0, 0x0, 0x48, 0x89, 0x84, 0x24, 0xa8, 0x0, 0x0, 0x0]

def xCopyEffect (s : RamState) : Effect :=
  { rip := 0x11099f
    writes := [⟨(.mem (stackPtr s + 168) : Operand 64), memLoad s.external (stackPtr s + 376) 64⟩,
      ⟨(.mem (stackPtr s + 176) : Operand 64), memLoad s.external (stackPtr s + 384) 64⟩,
      ⟨(.mem (stackPtr s + 184) : Operand 64), memLoad s.external (stackPtr s + 392) 64⟩,
      ⟨(.mem (stackPtr s + 192) : Operand 64), memLoad s.external (stackPtr s + 400) 64⟩,
      ⟨(.reg 0 : Operand 64), memLoad s.external (stackPtr s + 376) 64⟩,
      ⟨(.reg 1 : Operand 64), memLoad s.external (stackPtr s + 384) 64⟩] }

set_option maxHeartbeats 800000 in
theorem x_copy_correct [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary XCopyPre (codeRange 0x11095f xCopyBytes)
      xCopyEffect := by
  advance_begin (mov_r64_m64_effect_step 0x11095f 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 400)) (by decide) rfl rfl)
  case pre =>
    intro s h
    refine ⟨h.rip, ?_⟩
    x86_norm
    exact h.readable 400 (by simp)
  case next =>
    intro _ _
    exact boundary_ne_program outside (inProgram_of_textOffset 0x10967 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x110967 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 192)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11095f xCopyBytes 8 8
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 192 8 (by simp)
    · x86_norm
      exact (hP.codeApart 192 8 (by simp)).sub 8 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 192 8 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1096f (by decide))
  advance_then (mov_r64_m64_effect_step 0x11096f 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 392)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11095f xCopyBytes 16 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 392 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10977 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x110977 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 184)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11095f xCopyBytes 24 8
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 184 8 (by simp)
    · x86_norm
      exact (hP.codeApart 184 8 (by simp)).sub 24 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 184 8 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1097f (by decide))
  advance_then (mov_r64_m64_effect_step 0x11097f 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 376)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11095f xCopyBytes 32 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 376 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10987 (by decide))
  advance_then (mov_r64_m64_effect_step 0x110987 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 384)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11095f xCopyBytes 40 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 384 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1098f (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x11098f 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 176)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11095f xCopyBytes 48 8
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 176 8 (by simp)
    · x86_norm
      exact (hP.codeApart 176 8 (by simp)).sub 48 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 176 8 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10997 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x110997 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 168)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11095f xCopyBytes 56 8
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true)
      (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 168 8 (by simp)
    · x86_norm
      exact (hP.codeApart 168 8 (by simp)).sub 56 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 168 8 (by simp)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1099f (by decide))
  apply P256.Proofs.Common.Field.AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · x86_norm [xCopyEffect, stackPtr, Operand.read_reg64,
      gprNumber, rexR, rexB, UInt8.toBitVec_ofNat, BitVec.reduceExtractLsb', BitVec.reduceToNat,
      Nat.reduceShiftLeft, Nat.reduceAdd, BitVec.reduceOfNat]
    all_goals repeat first | constructor | rfl
  · x86_norm [xCopyEffect, stackPtr, Operand.read_reg64]
    all_goals repeat first | constructor | rfl
  · intro f; cases f <;> x86_norm [xCopyEffect, stackPtr, Operand.read_reg64]
    all_goals repeat first | constructor | rfl
  · x86_norm [xCopyEffect, stackPtr, Operand.read_reg64]
    all_goals repeat first | constructor | rfl

end P256.Proofs.Sec1.Affine.Uncompressed.Parse.Blocks
