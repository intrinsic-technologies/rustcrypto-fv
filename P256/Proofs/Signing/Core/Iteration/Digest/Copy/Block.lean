import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.Code
import P256.Proofs.Verifying.Core.Scalars.Memory
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Digest.Copy.Block

open P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10cca1
  readable4 : ∀ offset ∈ ([1328, 1336, 1344, 1352] : List Nat), MemReadable s (rspOf s + BitVec.ofNat 64 offset) 8
  writable : ∀ offset ∈ ([528, 536, 544, 552] : List Nat), MemWritable s (rspOf s + BitVec.ofNat 64 offset) 8
  codeApart : ∀ offset ∈ ([528, 536, 544, 552] : List Nat), ∀ codeOffset len : Nat,
    codeOffset + len ≤ 75 → RangeApart (rspOf s + BitVec.ofNat 64 offset) 8
      (0x10cca1 + BitVec.ofNat 64 codeOffset) len

def bytes : List UInt8 :=
  [0x48, 0x8b, 0x84, 0x24, 0x48, 0x5, 0x0, 0x0, 0x48, 0x89, 0x84, 0x24, 0x28, 0x2, 0x0, 0x0, 0x48, 0x8b, 0x84, 0x24, 0x40, 0x5, 0x0, 0x0, 0x48, 0x89, 0x84, 0x24, 0x20, 0x2, 0x0, 0x0, 0x48, 0x8b, 0x84, 0x24, 0x30, 0x5, 0x0, 0x0, 0x48, 0x8b, 0x8c, 0x24, 0x38, 0x5, 0x0, 0x0, 0x48, 0x89, 0x8c, 0x24, 0x18, 0x2, 0x0, 0x0, 0x48, 0x89, 0x84, 0x24, 0x10, 0x2, 0x0, 0x0, 0x48, 0x8d, 0xbc, 0x24, 0x10, 0x5, 0x0, 0x0, 0x48, 0x89, 0xee]

def effect (s : RamState) : Effect :=
  { rip := 0x10ccec
    writes := [
      ⟨(Operand.reg 0 : Operand 64), (Operand.mem (rspOf s + 1328) : Operand 64).read s⟩,
      ⟨(Operand.reg 1 : Operand 64), (Operand.mem (rspOf s + 1336) : Operand 64).read s⟩,
      ⟨(Operand.reg 6 : Operand 64), (Operand.reg 5 : Operand 64).read s⟩,
      ⟨(Operand.reg 7 : Operand 64), rspOf s + 1296⟩,
      ⟨(Operand.mem (rspOf s + 528) : Operand 64), (Operand.mem (rspOf s + 1328) : Operand 64).read s⟩,
      ⟨(Operand.mem (rspOf s + 536) : Operand 64), (Operand.mem (rspOf s + 1336) : Operand 64).read s⟩,
      ⟨(Operand.mem (rspOf s + 544) : Operand 64), (Operand.mem (rspOf s + 1344) : Operand 64).read s⟩,
      ⟨(Operand.mem (rspOf s + 552) : Operand 64), (Operand.mem (rspOf s + 1352) : Operand 64).read s⟩] }

set_option maxHeartbeats 1200000 in
theorem block [Bindings] (boundary : ReturnBoundary)
    (outside : ∀ i ≤ 75, (0x10cca1 : BitVec 64) + BitVec.ofNat 64 i ≠ boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10cca1 bytes) (Effect.post effect) := by
  advance_begin (mov_r64_m64_effect_step 0x10cca1 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 1352)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.readable4 1352 (by simp)⟩
  case next =>
    intro _ _
    exact outside 8 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10cca9 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 552)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10cca1 bytes 8 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 552 (by simp)
    · x86_norm
      exact hP.codeApart 552 (by simp) 8 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 552 (by simp) 0 75 (by decide)
    · exact outside 16 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10ccb1 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 1344)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10cca1 bytes 16 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable4 1344 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 24 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10ccb9 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 544)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10cca1 bytes 24 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 544 (by simp)
    · x86_norm
      exact hP.codeApart 544 (by simp) 24 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 544 (by simp) 0 75 (by decide)
    · exact outside 32 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10ccc1 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 1328)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10cca1 bytes 32 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable4 1328 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 40 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10ccc9 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 1336)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10cca1 bytes 40 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable4 1336 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 48 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10ccd1 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 536)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10cca1 bytes 48 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 536 (by simp)
    · x86_norm
      exact hP.codeApart 536 (by simp) 48 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 536 (by simp) 0 75 (by decide)
    · exact outside 56 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10ccd9 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 528)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10cca1 bytes 56 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 528 (by simp)
    · x86_norm
      exact hP.codeApart 528 (by simp) 56 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 528 (by simp) 0 75 (by decide)
    · exact outside 64 (by decide)
  advance_then (lea_r64_effect_step 0x10cce1 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 1296)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10cca1 bytes 64 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 72 (by decide)
  advance_then (mov_r64_r64_effect_step 0x10cce9 0x48 0xee (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10cca1 bytes 72 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 75 (by decide)
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

end P256.Proofs.Signing.Core.Iteration.Digest.Copy.Block
