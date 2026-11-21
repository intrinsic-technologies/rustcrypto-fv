import P256.Proofs.Nonce.UpdateValue.Finish.StoreRun
import P256.Proofs.Nonce.UpdateValue.Prepare.Memory
import P256.Proofs.Program.ScalarFrame.Output

set_option autoImplicit false

namespace P256.Proofs.Nonce.UpdateValue.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field

variable [Bindings] {initial s t : RamState} {boundary : ReturnBoundary} {state : State}

theorem store_writes (pre : UpdateValuePre initial boundary state)
    (input : Finalized initial s state) :
    WritesWithin (storeEffect s).components
      #v[registerRegion initial .rdi 64, ScalarFrame.workRegion initial 1168] := by
  have pointer : valuePointer s = initial.regValue .rdi + 32 := input.valuePointer
  have rsp : stackPtr s = scratch initial := input.rsp
  intro c hc a ha
  simp only [storeEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component, Operand.component, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
  all_goals try exact ha.elim
  · change (Component.mem (stackPtr s + 96) 8).Covers a at ha
    rw [rsp] at ha
    exact ⟨_, by simp, Prepare.work_contains_scratch pre (offset := 96) (by decide) ha⟩
  · change (Component.mem (stackPtr s + 88) 8).Covers a at ha
    rw [rsp] at ha
    exact ⟨_, by simp, Prepare.work_contains_scratch pre (offset := 88) (by decide) ha⟩
  · change (Component.mem (stackPtr s + 80) 8).Covers a at ha
    rw [rsp] at ha
    exact ⟨_, by simp, Prepare.work_contains_scratch pre (offset := 80) (by decide) ha⟩
  · change (Component.mem (stackPtr s + 72) 8).Covers a at ha
    rw [rsp] at ha
    exact ⟨_, by simp, Prepare.work_contains_scratch pre (offset := 72) (by decide) ha⟩
  · change (Component.mem (valuePointer s + 24) 8).Covers a at ha
    rw [pointer] at ha
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at ha
    exact ⟨_, by simp, ScalarFrame.output_contains pre.callee (offset := 56)
      (by decide) ha⟩
  · change (Component.mem (valuePointer s + 16) 8).Covers a at ha
    rw [pointer] at ha
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at ha
    exact ⟨_, by simp, ScalarFrame.output_contains pre.callee (offset := 48)
      (by decide) ha⟩
  · change (Component.mem (valuePointer s + 8) 8).Covers a at ha
    rw [pointer] at ha
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at ha
    exact ⟨_, by simp, ScalarFrame.output_contains pre.callee (offset := 40)
      (by decide) ha⟩
  · change (Component.mem (valuePointer s + 0) 8).Covers a at ha
    rw [pointer] at ha
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at ha
    exact ⟨_, by simp, ScalarFrame.output_contains pre.callee (offset := 32)
      (by decide) ha⟩

theorem store_frame (pre : UpdateValuePre initial boundary state)
    (input : Finalized initial s state) (ready : ReadyToStep t)
    (effect : (storeEffect s).Holds s t) : FrameState initial t := by
  exact input.toFrameState.after_effect pre.callee (by decide) ready effect.agrees
    (store_writes pre input) (by simp [storeEffect, Effect.components])

theorem store_key (pre : UpdateValuePre initial boundary state)
    (input : Finalized initial s state) (effect : (storeEffect s).Holds s t) :
    (MemoryRegion.mk (initial.regValue .rdi).toNat 32).HasBytes t.external state.key := by
  apply hasBytes_copy input.drbg.1
  intro i hi
  apply effect.agrees.byte
  intro c hc covered
  have pointer : valuePointer s = initial.regValue .rdi + 32 := input.valuePointer
  have rsp : stackPtr s = scratch initial := input.rsp
  have stack_apart {offset : Nat} (bound : offset + 8 ≤ 440)
      (h : (Component.mem (stackPtr s + BitVec.ofNat 64 offset) 8).Covers
        (initial.regValue .rdi + BitVec.ofNat 64 i)) : False := by
    rw [rsp] at h
    exact pre.separation _
      (memoryRegion_contains_add pre.stateBounded (Nat.le_refl _) (Nat.le_refl _)
        (show i < 64 by omega)) (work_substack pre (Prepare.work_contains_scratch pre bound h))
  have value_apart {offset : Nat} (bound : offset ≤ 24)
      (h : (Component.mem (valuePointer s + BitVec.ofNat 64 offset) 8).Covers
        (initial.regValue .rdi + BitVec.ofNat 64 i)) : False := by
    obtain ⟨j, hj, eq⟩ := h
    rw [pointer] at eq
    have low : (initial.regValue .rdi).toNat + 64 < 2^32 := pre.stateBounded
    have addr (k : Nat) (hk : k < 64) :
        (initial.regValue .rdi + BitVec.ofNat 64 k).toNat =
          (initial.regValue .rdi).toNat + k := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : k < 2^64),
        Nat.mod_eq_of_lt (by omega)]
    have e : initial.regValue .rdi + BitVec.ofNat 64 i =
        initial.regValue .rdi + BitVec.ofNat 64 (32 + offset + j) := by
      simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using eq
    have en := congrArg BitVec.toNat e
    rw [addr i (by omega), addr (32 + offset + j) (by omega)] at en
    omega
  simp only [storeEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component, Operand.component, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
  all_goals try exact covered.elim
  · exact stack_apart (offset := 96) (by decide) covered
  · exact stack_apart (offset := 88) (by decide) covered
  · exact stack_apart (offset := 80) (by decide) covered
  · exact stack_apart (offset := 72) (by decide) covered
  · exact value_apart (offset := 24) (by decide) covered
  · exact value_apart (offset := 16) (by decide) covered
  · exact value_apart (offset := 8) (by decide) covered
  · exact value_apart (offset := 0) (by decide) covered

end P256.Proofs.Nonce.UpdateValue.Finish
