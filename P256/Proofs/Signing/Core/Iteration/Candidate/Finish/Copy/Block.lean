import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.Code
import P256.Proofs.Verifying.Core.Scalars.Memory
import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Candidate.Finish.Copy.Block

open P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10cba6
  readable : ∀ offset ∈ ([432, 440, 448, 456] : List Nat), MemReadable s (rspOf s + BitVec.ofNat 64 offset) 8
  writable : ∀ offset ∈ ([8, 16, 24, 32] : List Nat), MemWritable s (rspOf s + BitVec.ofNat 64 offset) 8
  codeApart : ∀ offset ∈ ([8, 16, 24, 32] : List Nat), ∀ codeOffset len : Nat,
    codeOffset + len ≤ 52 → RangeApart (rspOf s + BitVec.ofNat 64 offset) 8
      (0x10cba6 + BitVec.ofNat 64 codeOffset) len

theorem read_store (s : RamState) (m : Ram) (c d : BitVec 64) (v : BitVec 64)
    (hc : c ∈ [8, 16, 24, 32]) (hd : d ∈ [432, 440, 448, 456]) :
    memLoad (memStore m (rspOf s + c) v) (rspOf s + d) 64 =
      memLoad m (rspOf s + d) 64 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc hd
  rcases hc with rfl | rfl | rfl | rfl
  all_goals rcases hd with rfl | rfl | rfl | rfl
  all_goals exact P256.Proofs.Common.Field.Montgomery.Schoolbook.memLoad_memStore_rangeApart m _ _ v 64 (RangeApart.offsets (rspOf s) (by decide) (by decide) (.inl (by decide)))

def bytes : List UInt8 :=
  [0x48, 0x8b, 0x8c, 0x24, 0xb0, 0x1, 0x0, 0x0, 0x48, 0x8b, 0x94, 0x24, 0xb8, 0x1, 0x0, 0x0, 0x48, 0x89, 0x4c, 0x24, 0x8, 0x48, 0x89, 0x54, 0x24, 0x10, 0x48, 0x8b, 0x8c, 0x24, 0xc0, 0x1, 0x0, 0x0, 0x48, 0x89, 0x4c, 0x24, 0x18, 0x48, 0x8b, 0x8c, 0x24, 0xc8, 0x1, 0x0, 0x0, 0x48, 0x89, 0x4c, 0x24, 0x20]

def effect (s : RamState) : Effect :=
  { rip := 0x10cbda
    writes := [⟨(.reg 1 : Operand 64), (Operand.mem (rspOf s + 456) : Operand 64).read s⟩, ⟨(.reg 2 : Operand 64), (Operand.mem (rspOf s + 440) : Operand 64).read s⟩, ⟨(.mem (rspOf s + 8) : Operand 64), (Operand.mem (rspOf s + 432) : Operand 64).read s⟩, ⟨(.mem (rspOf s + 16) : Operand 64), (Operand.mem (rspOf s + 440) : Operand 64).read s⟩, ⟨(.mem (rspOf s + 24) : Operand 64), (Operand.mem (rspOf s + 448) : Operand 64).read s⟩, ⟨(.mem (rspOf s + 32) : Operand 64), (Operand.mem (rspOf s + 456) : Operand 64).read s⟩] }

set_option maxHeartbeats 1200000 in
theorem block [Bindings] (boundary : ReturnBoundary)
    (outside : ∀ i ≤ 52, (0x10cba6 : BitVec 64) + BitVec.ofNat 64 i ≠ boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10cba6 bytes) (Effect.post effect) := by
  advance_begin (mov_r64_m64_effect_step 0x10cba6 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 432)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.readable 432 (by simp)⟩
  case next =>
    intro _ _
    exact outside 8 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10cbae 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 440)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10cba6 bytes 8 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 440 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 16 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10cbb6 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10cba6 bytes 16 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 8 (by simp)
    · x86_norm
      exact hP.codeApart 8 (by simp) 16 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 8 (by simp) 0 52 (by decide)
    · exact outside 21 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10cbbb 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10cba6 bytes 21 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 16 (by simp)
    · x86_norm
      exact hP.codeApart 16 (by simp) 21 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 16 (by simp) 0 52 (by decide)
    · exact outside 26 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10cbc0 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 448)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10cba6 bytes 26 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 448 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 34 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10cbc8 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10cba6 bytes 34 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 24 (by simp)
    · x86_norm
      exact hP.codeApart 24 (by simp) 34 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 24 (by simp) 0 52 (by decide)
    · exact outside 39 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10cbcd 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 456)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10cba6 bytes 39 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 456 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 47 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10cbd5 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10cba6 bytes 47 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 32 (by simp)
    · x86_norm
      exact hP.codeApart 32 (by simp) 47 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 32 (by simp) 0 52 (by decide)
    · exact outside 52 (by decide)
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

end P256.Proofs.Signing.Core.Iteration.Candidate.Finish.Copy.Block
