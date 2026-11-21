import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.Code
import P256.Proofs.Verifying.Core.Scalars.Memory
import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose
import X86Proofs.Program.ReadWrite.Bytes
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Candidate.Copy.Block

open P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10cad9
  readable : ∀ offset ∈ ([40, 48, 56, 64] : List Nat),
    MemReadable s (rspOf s + BitVec.ofNat 64 offset) 8
  writable : ∀ offset ∈ ([104, 112, 120, 128] : List Nat),
    MemWritable s (rspOf s + BitVec.ofNat 64 offset) 8
  codeApart : ∀ offset ∈ ([104, 112, 120, 128] : List Nat), ∀ codeOffset len : Nat,
    codeOffset + len ≤ 51 → RangeApart (rspOf s + BitVec.ofNat 64 offset) 8
      (0x10cad9 + BitVec.ofNat 64 codeOffset) len

theorem read_store (s : RamState) (m : Ram) (c d : BitVec 64) (v : BitVec 64)
    (hc : c ∈ [104, 112, 120, 128]) (hd : d ∈ [40, 48, 56, 64]) :
    memLoad (memStore m (rspOf s + c) v) (rspOf s + d) 64 =
      memLoad m (rspOf s + d) 64 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc hd
  rcases hc with rfl | rfl | rfl | rfl
  all_goals rcases hd with rfl | rfl | rfl | rfl
  all_goals exact P256.Proofs.Common.Field.Montgomery.Schoolbook.memLoad_memStore_rangeApart m _ _ v 64 (RangeApart.offsets (rspOf s) (by decide) (by decide) (.inr (by decide)))

def bytes : List UInt8 :=
  [0x48, 0x8b, 0x44, 0x24, 0x40, 0x48, 0x89, 0x84, 0x24, 0x80, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x78, 0x48, 0x8b, 0x44, 0x24, 0x28, 0x48, 0x8b, 0x4c, 0x24, 0x30, 0x48, 0x89, 0x4c, 0x24, 0x70, 0x48, 0x89, 0x44, 0x24, 0x68, 0x48, 0x89, 0xef, 0x48, 0x8d, 0x74, 0x24, 0x68]

def effect (s : RamState) : Effect :=
  { rip := 0x10cb0c
    writes := [
      ⟨(.reg 0 : Operand 64), (Operand.mem (rspOf s + 40) : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), (Operand.mem (rspOf s + 48) : Operand 64).read s⟩,
      ⟨(.reg 7 : Operand 64), s.regValue .rbp⟩,
      ⟨(.reg 6 : Operand 64), rspOf s + 104⟩,
      ⟨(.mem (rspOf s + 104) : Operand 64), (Operand.mem (rspOf s + 40) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 112) : Operand 64), (Operand.mem (rspOf s + 48) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 120) : Operand 64), (Operand.mem (rspOf s + 56) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 128) : Operand 64), (Operand.mem (rspOf s + 64) : Operand 64).read s⟩] }

set_option maxHeartbeats 1200000 in
theorem block [Bindings] (boundary : ReturnBoundary)
    (outside : ∀ i ≤ 51, (0x10cad9 : BitVec 64) + BitVec.ofNat 64 i ≠ boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10cad9 bytes) (Effect.post effect) := by
  advance_begin (mov_r64_m64_effect_step 0x10cad9 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 64)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.readable 64 (by simp)⟩
  case next =>
    intro _ _
    exact outside 5 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10cade 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 128)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10cad9 bytes 5 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 128 (by simp)
    · x86_norm
      exact hP.codeApart 128 (by simp) 5 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 128 (by simp) 0 51 (by decide)
    · exact outside 13 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10cae6 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 56)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10cad9 bytes 13 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 56 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 18 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10caeb 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 120)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10cad9 bytes 18 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 120 (by simp)
    · x86_norm
      exact hP.codeApart 120 (by simp) 18 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 120 (by simp) 0 51 (by decide)
    · exact outside 23 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10caf0 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10cad9 bytes 23 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 40 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 28 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10caf5 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 48)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10cad9 bytes 28 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 48 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 33 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10cafa 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 112)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10cad9 bytes 33 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 112 (by simp)
    · x86_norm
      exact hP.codeApart 112 (by simp) 33 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 112 (by simp) 0 51 (by decide)
    · exact outside 38 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10caff 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 104)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10cad9 bytes 38 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 104 (by simp)
    · x86_norm
      exact hP.codeApart 104 (by simp) 38 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 104 (by simp) 0 51 (by decide)
    · exact outside 43 (by decide)
  advance_then (mov_r64_r64_effect_step 0x10cb04 0x48 0xef (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10cad9 bytes 43 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 46 (by decide)
  advance_then (lea_r64_effect_step 0x10cb07 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 104)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10cad9 bytes 46 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 51 (by decide)
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [effect]
  · x86_norm [effect, read_store, P256.Proofs.Verifying.Core.Scalars.operand_write_reg_external,
      P256.Proofs.Verifying.Core.Scalars.operand_write_mem_external]
    all_goals repeat constructor <;> rfl
  · intro i
    cases i <;> x86_norm [effect]
  · x86_norm [effect]

end P256.Proofs.Signing.Core.Iteration.Candidate.Copy.Block
