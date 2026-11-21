import P256.Proofs.Signing.Wrapper.Hash.Absorb.Long.Tail.Store
import P256.Proofs.Signing.Wrapper.Hash.Frame

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash.Absorb.Long.Tail

open P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem store_byte {s t : RamState} (effect : (Store.effect s).Holds s t)
    {offset len : Nat} (bound : offset + len < 2^64)
    (apart : offset + len ≤ 239 ∨ 240 ≤ offset)
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
    stackPtr s + 239 + BitVec.ofNat 64 j at eq
  rw [BitVec.add_assoc, BitVec.add_assoc] at eq
  have hn := congrArg BitVec.toNat ((BitVec.add_right_inj (stackPtr s)).mp eq)
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat] at hn
  omega

theorem store_load {s t : RamState} (effect : (Store.effect s).Holds s t)
    {offset width : Nat} (bound : offset + width / 8 < 2^64)
    (apart : offset + width / 8 ≤ 239 ∨ 240 ≤ offset) :
    memLoad t.external (stackPtr s + BitVec.ofNat 64 offset) width =
      memLoad s.external (stackPtr s + BitVec.ofNat 64 offset) width := by
  apply memLoad_congr
  intro i hi
  exact congrArg (fun b : Option UInt8 => b.getD 0) (store_byte effect bound apart hi)

theorem store_writes [Bindings] {initial start s : RamState} {secret message : ByteArray}
    (pre : Context initial secret message) (state : Frame initial start s) :
    WritesWithin (Store.effect s).components #v[workRegion initial] := by
  intro c hc a covered
  simp only [Store.effect, Effect.components, Write.component, Operand.component,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  all_goals try exact covered.elim
  change (Component.mem (stackPtr s + BitVec.ofNat 64 239) 1).Covers a at covered
  rw [ScalarFrame.scalar_stack_address (frameOffset := 520) (offset := 239)
    state.rsp (by decide) (by decide)] at covered
  exact ⟨workRegion initial, by simp,
    work_contains pre (offset := 281) (by decide) (by decide) covered⟩

theorem store_frame [Bindings] {initial start s t : RamState} {secret message : ByteArray}
    {fuel : Nat} (pre : Context initial secret message) (state : Frame initial start s)
    (run : Advances (returnBoundary initial) fuel s t)
    (ready : ReadyToStep t) (effect : (Store.effect s).Holds s t) : Frame initial start t := by
  apply state.after_effect pre run ready effect.agrees (store_writes pre state)
  · exact (effect.agrees.read (n := 64) (r := 4) (by
      simp [Store.effect, Effect.components, Write.component, Operand.component])).trans state.rsp
  · simp [Store.effect, Effect.components, Write.component, Operand.component]

end P256.Proofs.Signing.Wrapper.Hash.Absorb.Long.Tail
