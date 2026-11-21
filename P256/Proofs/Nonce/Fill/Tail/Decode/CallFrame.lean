import P256.Proofs.Nonce.Fill.Tail.Decode.Memory
import P256.Proofs.Nonce.Fill.CallResult.Frame
import P256.Proofs.Nonce.Fill.Call
import P256.Proofs.Program.CalleeStackFrame

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Tail.Decode

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

variable [Bindings] {initial s called t : RamState} {boundary : ReturnBoundary}
  {orderAddress : BitVec 64} {original state : Nonce.State}

theorem context_after_call (pre : Pre initial boundary orderAddress original)
    (input : Context initial s orderAddress state) {target : RamState → BitVec 64} {ret : BitVec 64}
    (effect : (callEffect target ret s).Holds s called)
    {outputRegister : Syntax.Reg} {offset : Nat}
    (bound : offset + 32 ≤ 184)
    (apart : ∀ slot : Nat, slot ∈ [40,48,56,64,136,144] →
      offset + 32 ≤ slot ∨ slot + 8 ≤ offset)
    (output : called.regValue outputRegister = frameBase initial + BitVec.ofNat 64 offset)
    (result : CalleeResult called t boundary 32 128 outputRegister) :
    Context initial t orderAddress state := by
  have bounds := stack_bounds pre.stack
  have rsp : stackPtr called = stackPtr initial - 240 :=
    effect.writes.1.trans (call_address input.toFrame)
  have sp : (stackPtr called).toNat = (stackPtr initial).toNat - 240 := by
    rw [rsp]
    exact stack_sub_toNat pre.stack (offset := 240) (by decide)
  have dst : called.regValue outputRegister = stackPtr initial - BitVec.ofNat 64 (232-offset) :=
    output.trans (frameBase_add initial (by omega))
  have dn : (called.regValue outputRegister).toNat = (stackPtr initial).toNat - (232-offset) := by
    rw [dst]
    exact stack_sub_toNat pre.stack (by omega)
  have resultMemory := result.stack_frame (savedBytes := 48) pre.stack rsp dst
    (by decide) (by decide) (by omega) (by omega)
  have memory : MemoryWriteFrame s t #v[ScalarFrame.workRegion initial 2096] := by
    apply memoryWriteFrame_trans (t := called) (effect.agrees.memoryWriteFrame ?_) resultMemory
    intro c hc a cover
    simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact cover.elim
    · refine ⟨ScalarFrame.workRegion initial 2096, by simp, ?_⟩
      rw [call_address input.toFrame] at cover
      exact ScalarFrame.work_contains pre.toCalleePre (offset := 240) (by decide) (by decide) cover
    · exact cover.elim
  have frame : Frame initial t := input.toFrame.after_call_result pre effect result (by
    intro a ha
    exact memory a (fun region hr hin => ha region (by simpa [workRegions] using Or.inr (Or.inr hr)) hin))
  have full : MemoryWriteFrame s t #v[Stack.region initial 2096] := by
    intro a ha
    apply memory a
    intro region hr hin
    have eq : region = ScalarFrame.workRegion initial 2096 := by simpa using hr
    subst region
    exact ha _ (by simp) (work_substack pre hin)
  have word (slot n : Nat) (member : slot ∈ [40,48,56,64,136,144]) (span : n / 8 ≤ 8) :
      memLoad t.external (frameBase initial + BitVec.ofNat 64 slot) n =
        memLoad s.external (frameBase initial + BitVec.ofNat 64 slot) n := by
    have slotBound : slot ≤ 144 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      omega
    have address : frameBase initial + BitVec.ofNat 64 slot =
        stackPtr initial - BitVec.ofNat 64 (232-slot) := frameBase_add initial (by omega)
    have low := stack_sub_toNat pre.stack (offset := 232-slot) (by omega)
    apply memLoad_congr
    intro i hi
    change (t.external[_]?).getD 0 = (s.external[_]?).getD 0
    have an : (frameBase initial + BitVec.ofNat 64 slot + BitVec.ofNat 64 i).toNat =
        (stackPtr initial).toNat - (232-slot) + i := by
      rw [address, BitVec.toNat_add, low, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : i < 2^64), Nat.mod_eq_of_lt (by omega)]
    rw [result.frame _]
    · rw [address, ScalarFrame.call_byte (frameOffset := 232) (by decide) input.rsp effect
        (offset := 232-slot) (len := n/8) (by omega) (by omega) hi]
    · intro region hr hin
      have cases : region = registerRegion called outputRegister 32 ∨ region = Stack.region called 128 := by
        simpa using hr
      rcases cases with rfl | rfl
      · have outside := apart slot member
        change (called.regValue outputRegister).toNat ≤ _ ∧
          _ < (called.regValue outputRegister).toNat + 32 at hin
        rw [an, dn] at hin
        omega
      · have high := hin.2
        rw [stack_region_end] at high
        change _ < (stackPtr called).toNat + 8 at high
        rw [an, sp] at high
        omega
  have saved (r : Syntax.Reg) (member : r ∈ [.rbx,.rbp,.r12,.r13,.r14,.r15]) :
      t.regValue r = s.regValue r := by
    apply (result.calleeSaved r member).trans
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · exact effect.agrees.read (n := 64) (r := 3) (by simp)
    · exact effect.agrees.read (n := 64) (r := 5) (by simp)
    · exact effect.agrees.read (n := 64) (r := 12) (by simp)
    · exact effect.agrees.read (n := 64) (r := 13) (by simp)
    · exact effect.agrees.read (n := 64) (r := 14) (by simp)
    · exact effect.agrees.read (n := 64) (r := 15) (by simp)
  refine ⟨frame, ⟨(word 40 64 (by simp) (by decide)).trans input.outputSlot,
    (word 48 64 (by simp) (by decide)).trans input.lengthSlot,
    (word 56 32 (by simp) (by decide)).trans input.bitsSlot,
    (word 64 64 (by simp) (by decide)).trans input.statePointerSlot,
    (word 136 64 (by simp) (by decide)).trans input.valuePointerSlot,
    (word 144 64 (by simp) (by decide)).trans input.generatorPointerSlot⟩,
    (saved .r13 (by simp)).trans input.r13, (saved .r15 (by simp)).trans input.r15, ?_⟩
  apply input.generator.of_frame pre.outputBounded pre.orderBounded full
  · intro region hr
    have eq : region = Stack.region initial 2096 := by simpa using hr
    subst region
    exact pre.separation 1 2 (by decide)
  · intro region hr
    have eq : region = Stack.region initial 2096 := by simpa using hr
    subst region
    exact pre.orderDisjoint _ (by simp)

end P256.Proofs.Nonce.Fill.Tail.Decode
