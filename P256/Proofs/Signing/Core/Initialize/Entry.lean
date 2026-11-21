import P256.Proofs.Signing.Core.Initialize.Prologue
import P256.Proofs.Signing.Core.Initialize.Setup
import P256.Proofs.Signing.Core.Initialize.Memory

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Initialize

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open NextNonce (scalarFrame coreFrame base_add base_nat)
open SecretKeyFromBytes.Scalar (Nat256At)

variable [Bindings] {s t u : RamState} {boundary : ReturnBoundary}

theorem setup_pre (pre : SignPre s boundary)
    (frame : Frame s t) (rip : t.RIP = 0x10c9d1) : SetupPre t := by
  refine ⟨rip, ?_, ?_⟩
  · intro offset member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact writable pre frame (by decide) (by decide)
  · intro offset member pc len bound
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ScalarFrame.stack_code pre.toCalleePre (scalarFrame frame) (by decide) (by decide) bound

theorem setup_local_writes (frame : Frame s t) : LocalWrites s (setupEffect t).components := by
  intro c member a covered
  simp only [setupEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_mem, Write.component_reg, Nat.reduceDiv,
    List.append_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact covered.elim
  all_goals obtain ⟨i, hi, rfl⟩ := covered
  all_goals rw [frame.rsp]
  · exact ⟨72 + i, by omega, by rw [BitVec.ofNat_add, ← BitVec.add_assoc]; rfl⟩
  · exact ⟨296 + i, by omega, by rw [BitVec.ofNat_add, ← BitVec.add_assoc]; rfl⟩
  · exact ⟨280 + i, by omega, by rw [BitVec.ofNat_add, ← BitVec.add_assoc]; rfl⟩
  · exact ⟨272 + i, by omega, by rw [BitVec.ofNat_add, ← BitVec.add_assoc]; rfl⟩
  · exact ⟨288 + i, by omega, by rw [BitVec.ofNat_add, ← BitVec.add_assoc]; rfl⟩
  · exact ⟨80 + i, by omega, by rw [BitVec.ofNat_add, ← BitVec.add_assoc]; rfl⟩

theorem setup_frame (pre : SignPre s boundary)
    (frame : Frame s t) (rip : t.RIP = 0x10c9d1) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧
      (setupEffect t).Holds t u := by
  obtain ⟨fuel, u, run, ready, _, effect⟩ := setup_block boundary pre.outerBoundary t
    (readyToStep frame.machine frame.bindingsSupported)
    (programText_slice (programLoaded_codeIn frame.loaded) 0xc9d1 setupBytes
      (by decide) (by decide +kernel)) (setup_pre pre frame rip)
  exact ⟨fuel, u, run, after_effect pre frame ready effect.agrees (setup_local_writes frame)
    (by simp [setupEffect, Effect.components]), effect⟩

theorem setup_order (pre : SignPre s boundary)
    (frame : Frame s t) (finalFrame : Frame s u) (effect : (setupEffect t).Holds t u) :
    Nat256At u (frameBase s + 272) Operations.domain.n := by
  have writes := effect.writes
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at writes
  rcases writes with ⟨_, _, _, _, _, w3, w1, _, w0, w2, _, _, _⟩
  refine SecretKeyFromBytes.Scalar.nat256At_of_memLoad_limbs (by decide +kernel) ?_ ?_
  · have h := (ScalarFrame.stack_readable pre.toCalleePre (scalarFrame finalFrame)
      (offset := 272) (len := 32) (by decide) (by decide)).mem
    rwa [finalFrame.rsp] at h
  intro j hj
  have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · calc
      _ = (0xf3b9cac2fc632551 : BitVec 64) := by
        simpa only [Write.AllHold, frame.rsp, memLoad_external, BitVec.add_assoc,
          BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Nat.reduceMul, BitVec.add_zero] using w0
      _ = _ := by decide +kernel
  · calc
      _ = (0xbce6faada7179e84 : BitVec 64) := by
        simpa only [Write.AllHold, frame.rsp, memLoad_external, BitVec.add_assoc,
          BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Nat.reduceMul, BitVec.add_zero] using w1
      _ = _ := by decide +kernel
  · calc
      _ = (0xffffffffffffffff : BitVec 64) := by
        simpa only [Write.AllHold, frame.rsp, memLoad_external, BitVec.add_assoc,
          BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Nat.reduceMul, BitVec.add_zero] using w2
      _ = _ := by decide +kernel
  · calc
      _ = (0xffffffff00000000 : BitVec 64) := by
        simpa only [Write.AllHold, frame.rsp, memLoad_external, BitVec.add_assoc,
          BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Nat.reduceMul, BitVec.add_zero] using w3
      _ = _ := by decide +kernel

end P256.Proofs.Signing.Core.Initialize
