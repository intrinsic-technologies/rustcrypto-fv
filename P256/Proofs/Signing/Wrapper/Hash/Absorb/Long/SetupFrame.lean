import P256.Proofs.Signing.Wrapper.Hash.Absorb.Long.Setup
import P256.Proofs.Signing.Wrapper.Hash.Enter

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash.Absorb.Long.Setup

open P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem writes [Bindings] {initial start s : RamState} {secret message : ByteArray}
    (pre : HashEntry initial start secret message) (state : Frame initial start s) :
    WritesWithin (effect s).components #v[workRegion initial] := by
  intro c hc a ha
  simp only [effect, Effect.components, Write.component, Operand.component,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  all_goals try exact ha.elim
  change (Component.mem (stackPtr s + BitVec.ofNat 64 272) 8).Covers a at ha
  rw [ScalarFrame.scalar_stack_address (frameOffset := 520) (offset := 272)
    state.rsp (by decide) (by decide)] at ha
  exact ⟨workRegion initial, by simp,
    work_contains pre.context (offset := 248) (by decide) (by decide) ha⟩

theorem frame [Bindings] {initial start s t : RamState} {secret message : ByteArray} {fuel : Nat}
    (pre : HashEntry initial start secret message) (state : Frame initial start s)
    (run : Advances (returnBoundary initial) fuel s t) (ready : ReadyToStep t) (result : (effect s).Holds s t) :
    Frame initial start t := by
  exact state.after_effect pre.context run ready result.agrees (writes pre state)
    ((result.agrees.read (n := 64) (r := 4)
      (by simp [effect, Effect.components, Write.component, Operand.component])).trans state.rsp)
    (by simp [effect, Effect.components, Write.component, Operand.component])

theorem pre [Bindings] {initial start s : RamState} {secret message : ByteArray}
    (input : HashEntry initial start secret message) (state : Frame initial start s)
    (rip : s.RIP = 0x102820) : Pre s := by
  refine ⟨rip, ?_, ?_⟩
  · have h := stack_writable input.context state (offset := 272) (len := 8)
      (by decide) (by decide)
    exact ⟨h.low, h.mem, h.tables⟩
  · exact stack_code input.context state (offset := 272) (len := 8)
      (codeOffset := 0x2820) (by decide) (by decide)

theorem kept {s t : RamState} (result : (effect s).Holds s t)
    {offset len : Nat} (bound : offset + len ≤ 272) :
    ∀ i < len, t.external[stackPtr s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      s.external[stackPtr s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  intro i hi
  apply result.agrees.byte
  intro c hc covered
  simp only [effect, Effect.components, Write.component, Operand.component,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  all_goals try exact covered.elim
  obtain ⟨j, hj, eq⟩ := covered
  rw [BitVec.add_assoc, BitVec.add_assoc] at eq
  have eqn := congrArg BitVec.toNat ((BitVec.add_right_inj (stackPtr s)).mp eq)
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat] at eqn
  omega

end P256.Proofs.Signing.Wrapper.Hash.Absorb.Long.Setup
