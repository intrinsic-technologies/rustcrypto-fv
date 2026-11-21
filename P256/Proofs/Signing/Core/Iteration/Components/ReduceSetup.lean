import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose
import P256.Proofs.Program.Code
import P256.Proofs.Verifying.Core.Scalars.Memory
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Mov.Triple
import P256.Proofs.Common.EffectCompose.Memory

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Components.ReduceSetup

open P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Verifying.Core.Scalars (operand_write_mem_external operand_write_reg_external)

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10d21a
  readable : ∀ off ∈ ([1328, 1336, 1344, 1352] : List Nat), MemReadable s (rspOf s+BitVec.ofNat 64 off) 8
  writable : ∀ off ∈ ([528, 536, 544, 552] : List Nat), MemWritable s (rspOf s+BitVec.ofNat 64 off) 8
  apart : ∀ off ∈ ([528, 536, 544, 552] : List Nat), ∀ i len : Nat, i+len ≤ 83 →
    RangeApart (rspOf s+BitVec.ofNat 64 off) 8 (0x10d21a+BitVec.ofNat 64 i) len

theorem read_store (s : RamState) (m : Ram) (c d : BitVec 64) (v : BitVec 64)
    (hc : c ∈ [528, 536, 544, 552]) (hd : d ∈ [1328, 1336, 1344, 1352]) :
    memLoad (memStore m (rspOf s+c) v) (rspOf s+d) 64 = memLoad m (rspOf s+d) 64 := by
  have apart : RangeApart (rspOf s+c) 8 (rspOf s+d) 8 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc hd
    rcases hc with rfl|rfl|rfl|rfl
    all_goals rcases hd with rfl|rfl|rfl|rfl
    all_goals apply RangeApart.offsets (rspOf s) (by decide) (by decide)
    all_goals first | exact .inl (by decide) | exact .inr (by decide)
  exact P256.Proofs.Common.Field.Montgomery.Schoolbook.memLoad_memStore_rangeApart m _ _ v (k := 64) apart

def bytes : List UInt8 :=
  [0x4c, 0x8d, 0xb4, 0x24, 0x70, 0x8, 0x0, 0x0, 0x48, 0x8b, 0x84, 0x24, 0x48, 0x5, 0x0, 0x0, 0x48, 0x89, 0x84, 0x24, 0x28, 0x2, 0x0, 0x0, 0x48, 0x8b, 0x84, 0x24, 0x40, 0x5, 0x0, 0x0, 0x48, 0x89, 0x84, 0x24, 0x20, 0x2, 0x0, 0x0, 0x48, 0x8b, 0x84, 0x24, 0x30, 0x5, 0x0, 0x0, 0x48, 0x8b, 0x8c, 0x24, 0x38, 0x5, 0x0, 0x0, 0x48, 0x89, 0x8c, 0x24, 0x18, 0x2, 0x0, 0x0, 0x48, 0x89, 0x84, 0x24, 0x10, 0x2, 0x0, 0x0, 0x48, 0x8d, 0xbc, 0x24, 0xb0, 0x0, 0x0, 0x0, 0x48, 0x89, 0xee]

def effect (s : RamState) : Effect :=
  { rip := 0x10d26d
    writes := [
      ⟨(.reg 14 : Operand 64), rspOf s+2160⟩,
      ⟨(.reg 0 : Operand 64), memLoad s.external (rspOf s+1328) 64⟩,
      ⟨(.reg 1 : Operand 64), memLoad s.external (rspOf s+1336) 64⟩,
      ⟨(.reg 7 : Operand 64), rspOf s+176⟩,
      ⟨(.reg 6 : Operand 64), (Operand.reg 5 : Operand 64).read s⟩,
      ⟨(.mem (rspOf s+552) : Operand 64), memLoad s.external (rspOf s+1352) 64⟩,
      ⟨(.mem (rspOf s+544) : Operand 64), memLoad s.external (rspOf s+1344) 64⟩,
      ⟨(.mem (rspOf s+536) : Operand 64), memLoad s.external (rspOf s+1336) 64⟩,
      ⟨(.mem (rspOf s+528) : Operand 64), memLoad s.external (rspOf s+1328) 64⟩] }

set_option maxHeartbeats 1200000 in
theorem block [Bindings] (boundary : ReturnBoundary)
    (outside : ∀ i ≤ 83, (0x10d21a : BitVec 64)+BitVec.ofNat 64 i ≠ boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10d21a bytes) (Effect.post effect) := by
  advance_begin (lea_r64_effect_step 0x10d21a 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 2160)) (by decide +kernel) rfl rfl)
  case next => intro _ _; exact outside 8 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10d222 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 1352)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d21a bytes 8 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 1352 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 16 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10d22a 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 552)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d21a bytes 16 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 552 (by simp)
    · x86_norm
      exact hP.apart 552 (by simp) 16 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 552 (by simp) 0 83 (by decide)
    · exact outside 24 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10d232 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 1344)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d21a bytes 24 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 1344 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 32 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10d23a 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 544)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d21a bytes 32 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 544 (by simp)
    · x86_norm
      exact hP.apart 544 (by simp) 32 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 544 (by simp) 0 83 (by decide)
    · exact outside 40 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10d242 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 1328)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d21a bytes 40 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 1328 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 48 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10d24a 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 1336)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d21a bytes 48 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 1336 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 56 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10d252 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 536)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d21a bytes 56 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 536 (by simp)
    · x86_norm
      exact hP.apart 536 (by simp) 56 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 536 (by simp) 0 83 (by decide)
    · exact outside 64 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10d25a 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 528)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d21a bytes 64 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 528 (by simp)
    · x86_norm
      exact hP.apart 528 (by simp) 64 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 528 (by simp) 0 83 (by decide)
    · exact outside 72 (by decide)
  advance_then (lea_r64_effect_step 0x10d262 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 176)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d21a bytes 72 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 80 (by decide)
  advance_then (mov_r64_r64_effect_step 0x10d26a 0x48 0xee (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10d21a bytes 80 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 83 (by decide)
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [effect]
  · x86_norm [effect,read_store,operand_write_reg_external,operand_write_mem_external]
    all_goals simp [gprNumber, rexR, modrmReg]
  · intro i; cases i <;> x86_norm [effect]
  · x86_norm [effect]

end P256.Proofs.Signing.Core.Iteration.Components.ReduceSetup
