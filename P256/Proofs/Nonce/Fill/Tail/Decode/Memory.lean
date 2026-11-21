import P256.Proofs.Nonce.Fill.Tail.Decode.State
import P256.Proofs.Nonce.Fill.Work
import P256.Proofs.Nonce.Fill.Memory
import P256.Proofs.Common.Encoding.Serialize.Convert.SavePointer

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Tail.Decode

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Common.Encoding.Serialize (read_mem_of_agrees)

variable [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
  {orderAddress : BitVec 64} {original state : Nonce.State}

theorem context_after_store {offset len : Nat}
    (pre : Pre initial boundary orderAddress original)
    (input : Context initial s orderAddress state) (ready : ReadyToStep t)
    (agrees : AgreesExcept [.mem (stackPtr s + BitVec.ofNat 64 offset) len, .rip] s t)
    (bound : offset + len ≤ 184)
    (apart : ∀ slot : Nat, slot ∈ [40, 48, 56, 64, 136, 144] →
      OffsetsApart (BitVec.ofNat 64 slot) (if slot = 56 then 4 else 8) (BitVec.ofNat 64 offset) len) :
    Context initial t orderAddress state := by
  have writes : WritesWithin [.mem (stackPtr s + BitVec.ofNat 64 offset) len, .rip]
      #v[Stack.region initial 2096] := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · refine ⟨Stack.region initial 2096, by simp, ?_⟩
      rw [input.rsp, frameBase_add initial (by omega)] at ha
      exact ScalarFrame.stack_contains pre.toCalleePre (by omega) (by omega) ha
    · exact ha.elim
  have frame := input.toFrame.after_effect pre ready agrees (by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · refine ⟨ScalarFrame.workRegion initial 2096, by simp [workRegions], ?_⟩
      rw [input.rsp, frameBase_add initial (by omega)] at ha
      exact ScalarFrame.work_contains pre.toCalleePre (by omega) (by omega) ha
    · exact ha.elim) (by simp)
  have word (slot n : Nat) (hs : slot ∈ [40, 48, 56, 64, 136, 144]) (hn : n / 8 ≤ if slot = 56 then 4 else 8) :
      memLoad t.external (frameBase initial + BitVec.ofNat 64 slot) n =
        memLoad s.external (frameBase initial + BitVec.ofNat 64 slot) n := by
    apply read_mem_of_agrees agrees
    intro i hi c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · rintro ⟨j, hj, eq⟩
      rw [input.rsp] at eq
      have sizeBound : (if slot = 56 then 4 else 8 : Nat) ≤ 8 := by split <;> omega
      exact OffsetsApart.ne (apart slot hs) (base := frameBase initial) (hl := by omega) (hi := by omega) (hj := hj) eq
    · exact id
  refine ⟨frame, ⟨(word 40 64 (by simp) (by decide)).trans input.outputSlot,
    (word 48 64 (by simp) (by decide)).trans input.lengthSlot,
    (word 56 32 (by simp) (by decide)).trans input.bitsSlot,
    (word 64 64 (by simp) (by decide)).trans input.statePointerSlot,
    (word 136 64 (by simp) (by decide)).trans input.valuePointerSlot,
    (word 144 64 (by simp) (by decide)).trans input.generatorPointerSlot⟩,
    (agrees.read (n := 64) (r := 13) (by simp)).trans input.r13,
    (agrees.read (n := 64) (r := 15) (by simp)).trans input.r15, ?_⟩
  apply input.generator.of_frame pre.outputBounded pre.orderBounded
    (agrees.memoryWriteFrame writes)
  · intro region hr
    have eq : region = Stack.region initial 2096 := by simpa using hr
    subst region
    exact pre.separation 1 2 (by decide)
  · intro region hr
    have eq : region = Stack.region initial 2096 := by simpa using hr
    subst region
    exact pre.orderDisjoint _ (by simp)

end P256.Proofs.Nonce.Fill.Tail.Decode
