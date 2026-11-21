import P256.Proofs.Nonce.Update.Prepare.Assemble.State
import P256.Proofs.Nonce.Update.Prepare.Assemble.OuterSetup
import P256.Proofs.HMAC.Key.Output.Bytes

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Prepare.Assemble

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem OuterSetup.pre [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {state : State} (pre : DrbgCalleePre initial boundary 0x109f30 1856 state)
    (current : InnerCopied initial s state) : Pre s := by
  refine ⟨current.rip, ?_, ?_, ?_⟩
  · intro offset member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ScalarFrame.stack_readable pre.callee current.toFrameState (by decide) (by decide)
  · intro offset member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals change MemWritable s (stackPtr s + _) 8
    all_goals rw [ScalarFrame.scalar_stack_address current.rsp (by decide) (by decide)]
    all_goals exact writable_of_grow (stack_sub_writable8 pre.stack
                (fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp)) (by decide) (by decide))
                current.allocated
  · intro offset member pc len bound
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ScalarFrame.stack_code pre.callee current.toFrameState (by decide) (by decide) bound

theorem OuterSetup.context [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {state : State} (pre : DrbgCalleePre initial boundary 0x109f30 1856 state)
    (current : Context initial s state) (ready : ReadyToStep t) (h : (effect s).Holds s t) :
    Context initial t state := by
  apply current.after_agrees pre ready h.agrees
  · intro r member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals simp [effect, Effect.components, Write.component, Operand.component]
  · intro c member a covered
    simp only [effect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals try exact covered.elim
    all_goals change (Component.mem (stackPtr s + _) _).Covers a at covered
    all_goals rw [show stackPtr s = scratch initial from current.rsp] at covered
    all_goals exact work_contains_scratch pre (by decide) covered

theorem OuterSetup.inner_bytes {s t : RamState} (h : (effect s).Holds s t) :
    ∀ i < 104, t.external[rspOf s + 496 + BitVec.ofNat 64 i]? =
      s.external[rspOf s + 496 + BitVec.ofNat 64 i]? := by
  intro i hi
  apply h.agrees.byte
  intro c member covered
  simp only [effect, Effect.components, List.map_cons, List.map_nil,
    Write.component, Operand.component, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
  all_goals try exact covered
  all_goals obtain ⟨j, hj, eq⟩ := covered
  all_goals exact OffsetsApart.ne (len₂ := 104) (by unfold OffsetsApart; decide +kernel) (rspOf s) hj hi (by decide) eq.symm

theorem OuterSetup.words {s t : RamState} (h : (effect s).Holds s t) :
    ∀ j < 8, memLoad t.external (rspOf s + 432 + BitVec.ofNat 64 (8*j)) 64 =
      memLoad s.external (rspOf s + 88 + BitVec.ofNat 64 (8*j)) 64 := by
  have stores := h.writes
  simp only [effect, Write.AllHold, Operand.read] at stores
  rcases stores with ⟨_, _, h0, h1, h2, h3, h4, h5, h6, h7⟩
  intro j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [rspOf, Operand.read, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
      BitVec.add_assoc, BitVec.reduceAdd] using h0
  · simpa only [rspOf, Operand.read, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
      BitVec.add_assoc, BitVec.reduceAdd] using h1
  · simpa only [rspOf, Operand.read, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
      BitVec.add_assoc, BitVec.reduceAdd] using h2
  · simpa only [rspOf, Operand.read, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
      BitVec.add_assoc, BitVec.reduceAdd] using h3
  · simpa only [rspOf, Operand.read, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
      BitVec.add_assoc, BitVec.reduceAdd] using h4
  · simpa only [rspOf, Operand.read, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
      BitVec.add_assoc, BitVec.reduceAdd] using h5
  · simpa only [rspOf, Operand.read, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
      BitVec.add_assoc, BitVec.reduceAdd] using h6
  · simpa only [rspOf, Operand.read, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
      BitVec.add_assoc, BitVec.reduceAdd] using h7

theorem copy_outer [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {state : State} (pre : DrbgCalleePre initial boundary 0x109f30 1856 state)
    (current : InnerCopied initial s state) :
    ∃ fuel t, Advances boundary fuel s t ∧ CopyReady initial t state := by
  obtain ⟨fuel, t, run, ready, _, effect⟩ := OuterSetup.run boundary pre.outerBoundary s
    (readyToStep current.machine current.bindingsSupported) (OuterSetup.code current.loaded)
    (OuterSetup.pre pre current)
  have context := OuterSetup.context pre current.toContext ready effect
  have rsp : rspOf s = scratch initial := current.rsp
  have copied := HMAC.Key.Output.bytes_of_words
    (ScalarFrame.stack_readable pre.callee current.toFrameState (offset := 88) (len := 64)
      (by decide) (by decide))
    (by
      rw [rsp, ← show stackPtr t = scratch initial from context.rsp]
      exact ScalarFrame.stack_readable pre.callee context.toFrameState (offset := 432) (len := 64)
        (by decide) (by decide)) (OuterSetup.words effect)
  refine ⟨fuel, t, run, context, effect.rip, ?_⟩
  · refine ⟨hasBytes_copy current.key ?_, ?_⟩
    · simpa only [rsp] using copied
    · have inner := current.inner.copy (b := scratch initial + 496) (by
        simpa only [rsp] using OuterSetup.inner_bytes effect)
      simpa only [ByteArray.append_empty, BitVec.add_assoc,
        show (432 : BitVec 64) + 64 = 496 from rfl] using inner

end P256.Proofs.Nonce.Update.Prepare.Assemble
