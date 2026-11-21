import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.Code
import P256.Proofs.Verifying.Core.Scalars.Memory
import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Scalars.FirstSetup.Block

open P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10dca0
  readable4 : ∀ offset ∈ ([128, 136, 144, 152] : List Nat), MemReadable s (rspOf s + BitVec.ofNat 64 offset) 8
  writable : ∀ offset ∈ ([128, 136, 144, 152, 768, 776, 784, 792] : List Nat), MemWritable s (rspOf s + BitVec.ofNat 64 offset) 8
  codeApart : ∀ offset ∈ ([128, 136, 144, 152, 768, 776, 784, 792] : List Nat), ∀ codeOffset len : Nat,
    codeOffset + len ≤ 120 → RangeApart (rspOf s + BitVec.ofNat 64 offset) 8
      (0x10dca0 + BitVec.ofNat 64 codeOffset) len

def bytes : List UInt8 :=
  [0x48,0x8b,0x84,0x24,0x80,0x00,0x00,0x00,0x48,0x8b,0x8c,0x24,0x88,0x00,0x00,0x00,0x48,0x89,0x84,0x24,0x00,0x03,0x00,0x00,0x48,0x89,0x8c,0x24,0x08,0x03,0x00,0x00,0x48,0x8b,0x94,0x24,0x90,0x00,0x00,0x00,0x48,0x89,0x94,0x24,0x10,0x03,0x00,0x00,0x48,0x8b,0xb4,0x24,0x98,0x00,0x00,0x00,0x48,0x89,0xb4,0x24,0x18,0x03,0x00,0x00,0x48,0x89,0xb4,0x24,0x98,0x00,0x00,0x00,0x48,0x89,0x94,0x24,0x90,0x00,0x00,0x00,0x48,0x89,0x8c,0x24,0x88,0x00,0x00,0x00,0x48,0x89,0x84,0x24,0x80,0x00,0x00,0x00,0x48,0x8d,0xbc,0x24,0x20,0x03,0x00,0x00,0x48,0x8d,0xb4,0x24,0xc8,0x03,0x00,0x00,0x48,0x8d,0x94,0x24,0x80,0x00,0x00,0x00]

def effect (s : RamState) : Effect :=
  { rip := 0x10dd18
    writes := [
      ⟨(Operand.reg 0 : Operand 64), (Operand.mem (rspOf s + 128) : Operand 64).read s⟩,
      ⟨(Operand.reg 1 : Operand 64), (Operand.mem (rspOf s + 136) : Operand 64).read s⟩,
      ⟨(Operand.reg 2 : Operand 64), rspOf s + 128⟩,
      ⟨(Operand.reg 6 : Operand 64), rspOf s + 968⟩,
      ⟨(Operand.reg 7 : Operand 64), rspOf s + 800⟩,
      ⟨(Operand.mem (rspOf s + 128) : Operand 64), (Operand.mem (rspOf s + 128) : Operand 64).read s⟩,
      ⟨(Operand.mem (rspOf s + 136) : Operand 64), (Operand.mem (rspOf s + 136) : Operand 64).read s⟩,
      ⟨(Operand.mem (rspOf s + 144) : Operand 64), (Operand.mem (rspOf s + 144) : Operand 64).read s⟩,
      ⟨(Operand.mem (rspOf s + 152) : Operand 64), (Operand.mem (rspOf s + 152) : Operand 64).read s⟩,
      ⟨(Operand.mem (rspOf s + 768) : Operand 64), (Operand.mem (rspOf s + 128) : Operand 64).read s⟩,
      ⟨(Operand.mem (rspOf s + 776) : Operand 64), (Operand.mem (rspOf s + 136) : Operand 64).read s⟩,
      ⟨(Operand.mem (rspOf s + 784) : Operand 64), (Operand.mem (rspOf s + 144) : Operand 64).read s⟩,
      ⟨(Operand.mem (rspOf s + 792) : Operand 64), (Operand.mem (rspOf s + 152) : Operand 64).read s⟩] }

theorem extracted_bytes : Extracted.textBytes.toListFrom 0xdca0 120 = bytes := by decide +kernel

set_option maxHeartbeats 1200000 in
theorem block [Bindings] (boundary : ReturnBoundary)
    (outside : ∀ i ≤ 120, (0x10dca0 : BitVec 64) + BitVec.ofNat 64 i ≠ boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10dca0 bytes) (Effect.post effect) := by
  advance_begin (mov_r64_m64_effect_step 0x10dca0 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 128)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.readable4 128 (by simp)⟩
  case next =>
    intro _ _
    exact outside 8 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10dca8 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 136)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dca0 bytes 8 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable4 136 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 16 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10dcb0 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 768)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dca0 bytes 16 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 768 (by simp)
    · x86_norm
      exact hP.codeApart 768 (by simp) 16 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 768 (by simp) 0 120 (by decide)
    · exact outside 24 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10dcb8 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 776)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dca0 bytes 24 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 776 (by simp)
    · x86_norm
      exact hP.codeApart 776 (by simp) 24 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 776 (by simp) 0 120 (by decide)
    · exact outside 32 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10dcc0 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 144)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dca0 bytes 32 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable4 144 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 40 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10dcc8 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 784)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dca0 bytes 40 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 784 (by simp)
    · x86_norm
      exact hP.codeApart 784 (by simp) 40 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 784 (by simp) 0 120 (by decide)
    · exact outside 48 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10dcd0 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 152)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dca0 bytes 48 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable4 152 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 56 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10dcd8 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 792)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dca0 bytes 56 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 792 (by simp)
    · x86_norm
      exact hP.codeApart 792 (by simp) 56 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 792 (by simp) 0 120 (by decide)
    · exact outside 64 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10dce0 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 152)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dca0 bytes 64 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 152 (by simp)
    · x86_norm
      exact hP.codeApart 152 (by simp) 64 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 152 (by simp) 0 120 (by decide)
    · exact outside 72 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10dce8 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 144)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dca0 bytes 72 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 144 (by simp)
    · x86_norm
      exact hP.codeApart 144 (by simp) 72 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 144 (by simp) 0 120 (by decide)
    · exact outside 80 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10dcf0 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 136)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dca0 bytes 80 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 136 (by simp)
    · x86_norm
      exact hP.codeApart 136 (by simp) 80 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 136 (by simp) 0 120 (by decide)
    · exact outside 88 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10dcf8 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 128)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dca0 bytes 88 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 128 (by simp)
    · x86_norm
      exact hP.codeApart 128 (by simp) 88 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 128 (by simp) 0 120 (by decide)
    · exact outside 96 (by decide)
  advance_then (lea_r64_effect_step 0x10dd00 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 800)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dca0 bytes 96 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 104 (by decide)
  advance_then (lea_r64_effect_step 0x10dd08 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 968)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dca0 bytes 104 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 112 (by decide)
  advance_then (lea_r64_effect_step 0x10dd10 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 128)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10dca0 bytes 112 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 120 (by decide)
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [effect]
  · x86_norm [effect, P256.Proofs.Verifying.Core.Scalars.operand_write_reg_external,
      P256.Proofs.Verifying.Core.Scalars.operand_write_mem_external]
    all_goals try simp only [BitVec.add_zero]
    all_goals repeat constructor <;> rfl
  · intro i
    cases i <;> x86_norm [effect]
  · x86_norm [effect]

end P256.Proofs.Verifying.Core.Scalars.FirstSetup.Block
