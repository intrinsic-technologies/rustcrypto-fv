import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.Code
import P256.Proofs.Verifying.Core.Scalars.Memory
import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Digest.Invert.Copy.Block

open P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10cd1b
  readable : ∀ offset ∈ ([528, 536, 544, 552] : List Nat), MemReadable s (rspOf s + BitVec.ofNat 64 offset) 8
  writable : ∀ offset ∈ ([336, 344, 352, 360] : List Nat), MemWritable s (rspOf s + BitVec.ofNat 64 offset) 8
  codeApart : ∀ offset ∈ ([336, 344, 352, 360] : List Nat), ∀ codeOffset len : Nat,
    codeOffset + len ≤ 64 → RangeApart (rspOf s + BitVec.ofNat 64 offset) 8
      (0x10cd1b + BitVec.ofNat 64 codeOffset) len

theorem read_store (s : RamState) (m : Ram) (c d : BitVec 64) (v : BitVec 64)
    (hc : c ∈ [336, 344, 352, 360]) (hd : d ∈ [528, 536, 544, 552]) :
    memLoad (memStore m (rspOf s + c) v) (rspOf s + d) 64 =
      memLoad m (rspOf s + d) 64 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc hd
  rcases hc with rfl | rfl | rfl | rfl
  all_goals rcases hd with rfl | rfl | rfl | rfl
  all_goals exact P256.Proofs.Common.Field.Montgomery.Schoolbook.memLoad_memStore_rangeApart m _ _ v 64 (RangeApart.offsets (rspOf s) (by decide) (by decide) (.inl (by decide)))

def bytes : List UInt8 :=
  [0x48, 0x8b, 0x84, 0x24, 0x10, 0x2, 0x0, 0x0, 0x48, 0x8b, 0x8c, 0x24, 0x18, 0x2, 0x0, 0x0, 0x48, 0x89, 0x84, 0x24, 0x50, 0x1, 0x0, 0x0, 0x48, 0x89, 0x8c, 0x24, 0x58, 0x1, 0x0, 0x0, 0x48, 0x8b, 0x84, 0x24, 0x20, 0x2, 0x0, 0x0, 0x48, 0x89, 0x84, 0x24, 0x60, 0x1, 0x0, 0x0, 0x48, 0x8b, 0x84, 0x24, 0x28, 0x2, 0x0, 0x0, 0x48, 0x89, 0x84, 0x24, 0x68, 0x1, 0x0, 0x0]

def effect (s : RamState) : Effect :=
  { rip := 0x10cd5b
    writes := [⟨(.reg 0 : Operand 64), (Operand.mem (rspOf s + 552) : Operand 64).read s⟩, ⟨(.reg 1 : Operand 64), (Operand.mem (rspOf s + 536) : Operand 64).read s⟩, ⟨(.mem (rspOf s + 336) : Operand 64), (Operand.mem (rspOf s + 528) : Operand 64).read s⟩, ⟨(.mem (rspOf s + 344) : Operand 64), (Operand.mem (rspOf s + 536) : Operand 64).read s⟩, ⟨(.mem (rspOf s + 352) : Operand 64), (Operand.mem (rspOf s + 544) : Operand 64).read s⟩, ⟨(.mem (rspOf s + 360) : Operand 64), (Operand.mem (rspOf s + 552) : Operand 64).read s⟩] }

set_option maxHeartbeats 1200000 in
theorem block [Bindings] (boundary : ReturnBoundary)
    (outside : ∀ i ≤ 64, (0x10cd1b : BitVec 64) + BitVec.ofNat 64 i ≠ boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10cd1b bytes) (Effect.post effect) := by
  advance_begin (mov_r64_m64_effect_step 0x10cd1b 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 528)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.readable 528 (by simp)⟩
  case next =>
    intro _ _
    exact outside 8 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10cd23 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 536)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10cd1b bytes 8 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 536 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 16 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10cd2b 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 336)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10cd1b bytes 16 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 336 (by simp)
    · x86_norm
      exact hP.codeApart 336 (by simp) 16 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 336 (by simp) 0 64 (by decide)
    · exact outside 24 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10cd33 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 344)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10cd1b bytes 24 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 344 (by simp)
    · x86_norm
      exact hP.codeApart 344 (by simp) 24 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 344 (by simp) 0 64 (by decide)
    · exact outside 32 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10cd3b 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 544)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10cd1b bytes 32 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 544 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 40 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10cd43 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 352)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10cd1b bytes 40 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 352 (by simp)
    · x86_norm
      exact hP.codeApart 352 (by simp) 40 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 352 (by simp) 0 64 (by decide)
    · exact outside 48 (by decide)
  advance_then (mov_r64_m64_effect_step 0x10cd4b 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 552)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10cd1b bytes 48 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 552 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact outside 56 (by decide)
  advance_then (mov_m64_r64_effect_step 0x10cd53 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 360)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10cd1b bytes 56 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 360 (by simp)
    · x86_norm
      exact hP.codeApart 360 (by simp) 56 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 360 (by simp) 0 64 (by decide)
    · exact outside 64 (by decide)
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

end P256.Proofs.Signing.Core.Iteration.Digest.Invert.Copy.Block
