import P256.Proofs.Signing.Core.Iteration.Memory

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open NextNonce (scalarFrame coreFrame base_add base_nat)

variable [Bindings] {s t v u : RamState} {boundary : ReturnBoundary}
  {target : BitVec 64} {ret : BitVec 64} {inputBytes outputBytes reserve left output : Nat}

theorem local_call_pre (pre : SignPre s boundary) (frame : Frame s t)
    (ready : ReadyToStep v) (effect : (callEffect (fun _ => target) ret t).Holds t v)
    (retIn : InProgram ret) (capacity : 2288 + reserve ≤ 4584)
    (leftBound : left + inputBytes ≤ 2280) (outputBound : output + outputBytes ≤ 2280)
    (leftBelow : left ≤ 2280) (outputBelow : output ≤ 2280)
    (apart : left + inputBytes ≤ output ∨ output + outputBytes ≤ left)
    (si : t.regValue .rsi = frameBase s + BitVec.ofNat 64 left)
    (di : t.regValue .rdi = frameBase s + BitVec.ofNat 64 output) :
    CalleePre v boundary target inputBytes outputBytes reserve := by
  let layout : StackCallLayout 4584 inputBytes outputBytes reserve :=
    ⟨2288, 2280-left, 2280-output, by decide, capacity, by omega, by omega,
      by omega, by omega, by omega⟩
  have called := (scalarFrame frame).after_call pre.toCalleePre (by decide) (by decide) ready effect
  apply CalleePre.of_stack pre.toCalleePre layout called.bindingsSupported called.machine
    called.directionFlag called.loaded called.allocated effect.rip called.rsp
  · exact ((effect.agrees.read (n := 64) (r := 6) (by simp)).trans si).trans
      (base_add s leftBelow)
  · exact ((effect.agrees.read (n := 64) (r := 7) (by simp)).trans di).trans
      (base_add s outputBelow)
  · change InProgram (stackTop v)
    rw [(callEffect_stack effect).1]
    exact retIn

theorem local_call_copy (frame : Frame s t)
    (effect : (callEffect (fun _ => target) ret t).Holds t v)
    {offset len : Nat} (bound : offset + len ≤ 2280) :
    ∀ i < len, v.external[frameBase s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      t.external[frameBase s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  rw [base_add s (by omega)]
  intro i hi
  exact ScalarFrame.call_byte (frameOffset := 2280) (by decide) frame.rsp effect
    (offset := 2280-offset) (len := len) (by omega) (by omega) hi

theorem local_result_copy (pre : SignPre s boundary) (frame : Frame s t)
    (effect : (callEffect (fun _ => target) ret t).Holds t v)
    (result : CalleeResult v u boundary outputBytes reserve)
    (di : t.regValue .rdi = frameBase s + BitVec.ofNat 64 output)
    {offset len : Nat} (bound : offset + len ≤ 2280) (outputBelow : output ≤ 2280)
    (apart : offset + len ≤ output ∨ output + outputBytes ≤ offset) :
    ∀ i < len, u.external[frameBase s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      t.external[frameBase s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  have sp := effect.writes.1.trans (ScalarFrame.scalar_call_address (scalarFrame frame))
  have dst := ((effect.agrees.read (n := 64) (r := 7) (by simp)).trans di).trans
    (base_add s outputBelow)
  intro i hi
  refine Eq.trans ?_ (local_call_copy frame effect bound i hi)
  rw [base_add s (by omega)]
  exact result.stack_byte (frameOffset := 2280) (outputOffset := 2280-output)
    (offset := 2280-offset) (len := len) pre.stack sp dst (by decide) (by omega)
    (by omega) (by omega) (by omega) hi

theorem after_call (pre : SignPre s boundary) (frame : Frame s t)
    (ready : ReadyToStep v) (effect : (callEffect (fun _ => target) ret t).Holds t v)
    (result : CalleeResult v u boundary outputBytes reserve)
    (capacity : 2288 + reserve ≤ 4584) (bound : output + outputBytes ≤ 2232)
    (di : t.regValue .rdi = frameBase s + BitVec.ofNat 64 output) : Frame s u := by
  have called := (scalarFrame frame).after_call pre.toCalleePre (by decide) (by decide) ready effect
  have dst := ((effect.agrees.read (n := 64) (r := 7) (by simp)).trans di).trans
    (base_add s (by omega))
  have memory := result.stack_frame pre.stack called.rsp dst capacity
    (savedBytes := 48) (by decide) (by omega) (by omega)
  have memory' : MemoryWriteFrame v u #v[registerRegion s .rdi 65, ScalarFrame.workRegion s 4584] :=
    fun a ha => memory a (fun region hr => ha region (by simpa using Or.inr hr))
  refine ⟨result.machine, result.bindingsSupported, result.loaded, result.directionFlag,
    fun a ha => result.allocated a (called.allocated a ha),
    memoryWriteFrame_trans called.frame (ScalarFrame.output_work_frame pre.toCalleePre memory'),
    ?_, ?_, ?_, result.mxcsr.trans called.mxcsr, result.fp87.trans called.fp87⟩
  · have sp : stackPtr u = stackPtr v + 8 := result.rsp
    rw [sp, called.rsp]
    simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  · intro entry he
    have hb : entry.2 ≤ 48 := by
      simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (ScalarFrame.output_work_read pre.toCalleePre (by decide) memory' hb (by omega)).trans
      (called.saved entry he)
  · have h := ScalarFrame.output_work_read pre.toCalleePre (by decide) memory'
      (offset := 0) (n := 64) (by decide) (by decide)
    simp only [BitVec.sub_zero] at h
    exact h.trans called.returnAddress

end P256.Proofs.Signing.Core.Iteration
