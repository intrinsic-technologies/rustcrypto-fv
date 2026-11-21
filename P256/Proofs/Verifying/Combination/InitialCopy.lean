import P256.Proofs.Verifying.Combination.Entry
import P256.Proofs.Verifying.Combination.Call
import P256.Proofs.Verifying.Combination.Input
import P256.Proofs.Program.Copy
import P256.Proofs.Program.CalleeStackInput
import P256.Proofs.Program.FieldCall.Memory

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem initial_copy [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {p q : Projective} {u v : Nat} (pre : Pre s boundary)
    (input : InputAt s (s.regValue .rsi) p q u v) :
    ∃ fuel t, Advances boundary fuel s t ∧ State s t ∧ t.RIP = 0x106544 ∧
      InputAt t (stackPtr s - 5472) p q u v ∧
      t.regValue .rbx = stackPtr s - 5472 ∧ t.regValue .r14 = 0x11c930 ∧
      (Operand.mem (stackPtr s - 6544) : Operand 64).read t = s.regValue .rsi ∧
      (Operand.mem (stackPtr s - 6536) : Operand 64).read t = s.regValue .rdi := by
  obtain ⟨n, a, runA, stateA, ripA, sourceA, r15A, dstA, bxA, targetA, countA, outputA⟩ :=
    entry pre
  obtain ⟨b, runB, stateB, effect⟩ := call_copy pre stateA 0x6541
    (by decide) (by decide +kernel) ripA targetA
  have sourceB : b.regValue .rsi = s.regValue .rsi :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans sourceA
  have dstB : b.regValue .rdi = stackPtr s - 5472 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans dstA
  have ret : (returnBoundary b).rip = 0x106544 := (callEffect_stack effect).1
  have callee : CalleePre b boundary 0x11c930 256 256 8 :=
    CalleePre.of_input_and_stack pre
      (⟨6560, 5472, by decide, by decide, by decide, by decide⟩ : StackBufferLayout 8808 256 8)
      stateB.bindingsSupported stateB.machine stateB.directionFlag stateB.loaded stateB.allocated
      effect.rip stateB.rsp sourceB dstB (ret ▸ inProgram_of_textOffset 0x6544 (by decide))
  obtain ⟨t, result, bytes, _⟩ := memcpy_correct callee
    ((effect.agrees.read (n := 64) (r := 2) (by simp)).trans countA) (by decide)
  have work := FieldCall.stack_result_work_frame (frameOffset := 6552) pre stateB result dstB
    (by decide) (by decide) (by decide) (by decide)
  have finalState : State s t := FieldCall.after_result pre stateB result (by decide) work
  obtain ⟨m, runT⟩ := result.execution
  refine ⟨n + 1 + m, t, (runA.trans runB).trans runT, finalState,
    result.rip.trans ret, ?_, ?_, ?_, ?_, ?_⟩
  · apply input.of_bytes_eq
    intro i hi
    have h := bytes i hi
    rw [sourceB, dstB] at h
    exact h.trans (input_byte pre stateB.frame hi)
  · exact (result.calleeSaved .rbx (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 3) (by simp)).trans bxA)
  · exact (result.calleeSaved .r14 (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 14) (by simp)).trans targetA)
  · have kept : (Operand.mem (stackPtr s - 6544) : Operand 64).read t =
        (Operand.mem (stackPtr s - 6544) : Operand 64).read a := by
      apply memLoad_congr
      intro i hi
      change (t.external[stackPtr s - 6544 + BitVec.ofNat 64 i]?).getD 0 =
        (a.external[stackPtr s - 6544 + BitVec.ofNat 64 i]?).getD 0
      have h := FieldCall.stack_result_byte (frameOffset := 6552) pre stateB result dstB
        (offset := 6544) (len := 8) (by decide) (by decide) (by decide) (by decide)
        (Or.inr (by decide)) hi
      have hc := scalar_call_byte (frameOffset := 6552) (by decide) stateA effect
        (offset := 6544) (len := 8) (by decide) (by decide) hi
      exact congrArg (fun x : Option UInt8 => x.getD 0) (h.trans hc)
    exact kept.trans r15A
  · have kept : (Operand.mem (stackPtr s - 6536) : Operand 64).read t =
        (Operand.mem (stackPtr s - 6536) : Operand 64).read a := by
      apply memLoad_congr
      intro i hi
      change (t.external[stackPtr s - 6536 + BitVec.ofNat 64 i]?).getD 0 =
        (a.external[stackPtr s - 6536 + BitVec.ofNat 64 i]?).getD 0
      have h := FieldCall.stack_result_byte (frameOffset := 6552) pre stateB result dstB
        (offset := 6536) (len := 8) (by decide) (by decide) (by decide) (by decide)
        (Or.inr (by decide)) hi
      have hc := scalar_call_byte (frameOffset := 6552) (by decide) stateA effect
        (offset := 6536) (len := 8) (by decide) (by decide) hi
      exact congrArg (fun x : Option UInt8 => x.getD 0) (h.trans hc)
    exact kept.trans outputA

end P256.Proofs.Verifying.Combination
