import P256.Proofs.Verifying.Message.Hash.Long.Setup
import P256.Proofs.Verifying.Message.Hash.Entry

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash.Long.Setup

open P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem writes [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} (pre : Message.Pre initial boundary message)
    (state : Frame initial s) :
    WritesWithin (effect s).components #v[ScalarFrame.workRegion initial 9992] := by
  intro c hc a ha
  simp only [effect, Effect.components, Write.component, Operand.component,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  change (Component.mem (stackPtr s + BitVec.ofNat 64 568) 8).Covers a at ha
  rw [ScalarFrame.scalar_stack_address (frameOffset := 1176) (offset := 568)
    state.rsp (by decide) (by decide)] at ha
  exact ⟨ScalarFrame.workRegion initial 9992, by simp,
    ScalarFrame.work_contains pre.toCalleePre (offset := 608) (by decide) (by decide) ha⟩

theorem frame [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} (pre : Message.Pre initial boundary message)
    (state : Frame initial s) (ready : ReadyToStep t) (result : (effect s).Holds s t) :
    Frame initial t := by
  apply state.after_effect pre.toCalleePre (by decide) ready result.agrees _
    (by simp [effect, Effect.components, Write.component, Operand.component])
    (by simp [effect, Effect.components, Write.component, Operand.component])
    (by simp [effect, Effect.components, Write.component, Operand.component])
    (by simp [effect, Effect.components, Write.component, Operand.component])
  intro c hc a ha
  obtain ⟨region, member, inside⟩ := writes pre state c hc a ha
  exact ⟨region, by simpa using Or.inr member, inside⟩

theorem pre [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} (input : Message.Pre initial boundary message)
    (state : Frame initial s) (rip : s.RIP = 0x10d6b6) : Pre s := by
  refine ⟨rip, ?_, ?_⟩
  · change MemWritable s (stackPtr s + BitVec.ofNat 64 568) 8
    rw [ScalarFrame.scalar_stack_address (frameOffset := 1176) (offset := 568)
      state.rsp (by decide) (by decide)]
    exact writable_of_grow (stack_sub_writable8 input.stack
      (fun a ha hp => input.avoids _ (by simp) a ha (.inr hp)) (by decide) (by decide)) state.allocated
  · exact ScalarFrame.stack_code input.toCalleePre state (by decide) (by decide)
      (codeOffset := 0xd6b6) (by decide)

theorem kept {s t : RamState} (result : (effect s).Holds s t)
    {offset len : Nat} (bound : offset + len ≤ 568) :
    ∀ i < len, t.external[stackPtr s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      s.external[stackPtr s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  intro i hi
  apply result.agrees.byte
  intro c hc covered
  simp only [effect, Effect.components, Write.component, Operand.component,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  all_goals try exact covered.elim
  obtain ⟨j, hj, eq⟩ := covered
  rw [BitVec.add_assoc, BitVec.add_assoc] at eq
  have eqn := congrArg BitVec.toNat ((BitVec.add_right_inj (stackPtr s)).mp eq)
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat] at eqn
  omega

end P256.Proofs.Verifying.Message.Hash.Long.Setup
