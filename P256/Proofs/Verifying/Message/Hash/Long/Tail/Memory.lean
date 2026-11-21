import P256.Proofs.Verifying.Message.Hash.Long.Tail.Store
import P256.Proofs.Verifying.Message.Frame

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash.Long.Tail

open P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem store_byte {s t : RamState} (effect : (Store.effect s).Holds s t)
    {offset len : Nat} (bound : offset + len < 2^64)
    (apart : offset + len ≤ 535 ∨ 536 ≤ offset)
    {i : Nat} (hi : i < len) :
    t.external[stackPtr s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      s.external[stackPtr s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  apply effect.agrees.memory
  intro c hc covered
  simp only [Store.effect, Effect.components, Write.component, Operand.component,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  all_goals try exact covered.elim
  obtain ⟨j, hj, eq⟩ := covered
  change stackPtr s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i =
    stackPtr s + 535 + BitVec.ofNat 64 j at eq
  rw [BitVec.add_assoc, BitVec.add_assoc] at eq
  have hn := congrArg BitVec.toNat ((BitVec.add_right_inj (stackPtr s)).mp eq)
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat] at hn
  omega

theorem store_load {s t : RamState} (effect : (Store.effect s).Holds s t)
    {offset width : Nat} (bound : offset + width / 8 < 2^64)
    (apart : offset + width / 8 ≤ 535 ∨ 536 ≤ offset) :
    memLoad t.external (stackPtr s + BitVec.ofNat 64 offset) width =
      memLoad s.external (stackPtr s + BitVec.ofNat 64 offset) width := by
  apply memLoad_congr
  intro i hi
  exact congrArg (fun b : Option UInt8 => b.getD 0) (store_byte effect bound apart hi)

theorem store_writes [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre initial boundary 0x10d570 72 24 9992) (state : Frame initial s) :
    WritesWithin (Store.effect s).components #v[ScalarFrame.workRegion initial 9992] := by
  intro c hc a covered
  simp only [Store.effect, Effect.components, Write.component, Operand.component,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  all_goals try exact covered.elim
  change (Component.mem (stackPtr s + BitVec.ofNat 64 535) 1).Covers a at covered
  rw [ScalarFrame.scalar_stack_address (frameOffset := 1176) (offset := 535)
    state.rsp (by decide) (by decide)] at covered
  exact ⟨ScalarFrame.workRegion initial 9992, by simp,
    ScalarFrame.work_contains pre (offset := 641) (by decide) (by decide) covered⟩

theorem store_frame [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre initial boundary 0x10d570 72 24 9992) (state : Frame initial s)
    (ready : ReadyToStep t) (effect : (Store.effect s).Holds s t) : Frame initial t := by
  apply state.after_effect pre (by decide) ready effect.agrees _
    (by simp [Store.effect, Effect.components, Write.component, Operand.component])
    (by simp [Store.effect, Effect.components, Write.component, Operand.component])
    (by simp [Store.effect, Effect.components, Write.component, Operand.component])
    (by simp [Store.effect, Effect.components, Write.component, Operand.component])
  intro c hc a covered
  obtain ⟨region, member, inside⟩ := store_writes pre state c hc a covered
  exact ⟨region, by simpa using Or.inr member, inside⟩

end P256.Proofs.Verifying.Message.Hash.Long.Tail
