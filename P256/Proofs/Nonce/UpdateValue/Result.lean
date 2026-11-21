import P256.Proofs.Nonce.UpdateValue.Pre
import P256.Proofs.Program.CalleeStackFrame

set_option autoImplicit false

namespace P256.Proofs.Nonce.UpdateValue

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame

variable [Bindings] {initial s t : RamState} {boundary : ReturnBoundary} {state : State}

theorem frame_after_result {depth newDepth : BitVec 64} {outputBytes reserve : Nat}
    {outputRegister : Syntax.Reg}
    (pre : UpdateValuePre initial boundary state)
    (frame : FrameState initial s 64 1168 depth)
    (result : CalleeResult s t boundary outputBytes reserve outputRegister)
    (memory : MemoryWriteFrame s t #v[workRegion initial 1168])
    (rsp : stackPtr t = stackPtr initial - newDepth) :
    FrameState initial t 64 1168 newDepth := by
  have mem : MemoryWriteFrame s t #v[registerRegion initial .rdi 64, workRegion initial 1168] := by
    intro a ha
    apply memory a
    intro r hr
    exact ha r (by simpa using Or.inr hr)
  refine ⟨result.bindingsSupported, result.machine, result.loaded, result.directionFlag,
    fun a ha => result.allocated a (frame.allocated a ha),
    memoryWriteFrame_trans frame.frame (output_work_frame pre.callee mem), rsp, ?_, ?_,
    result.mxcsr.trans frame.mxcsr, result.fp87.trans frame.fp87⟩
  · intro e he
    have bound : e.2 ≤ 48 := by
      simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (output_work_read pre.callee (by decide) mem bound (by omega)).trans (frame.saved e he)
  · have h := output_work_read pre.callee (by decide) mem (offset := 0) (n := 64)
      (by decide) (by decide)
    simp only [BitVec.sub_zero] at h
    exact h.trans frame.returnAddress

theorem work_substack (pre : UpdateValuePre initial boundary state) {a : Nat}
    (inside : (workRegion initial 1168).Contains a) : (Stack.region initial 1168).Contains a := by
  change (stackPtr initial).toNat - 1168 ≤ a ∧
    a < (stackPtr initial).toNat - 1168 + 1120 at inside
  have bounds := stack_bounds pre.stack
  change (stackPtr initial).toNat - 1168 ≤ a ∧
    a < (Stack.region initial 1168).start + (Stack.region initial 1168).size
  rw [stack_region_end]
  constructor <;> omega

theorem result_stack_byte {outputBytes reserve stackOffset outputOffset offset len : Nat}
    (pre : UpdateValuePre initial boundary state)
    (result : CalleeResult s t boundary outputBytes reserve)
    (rsp : stackPtr s = stackPtr initial - BitVec.ofNat 64 stackOffset)
    (output : s.regValue .rdi = stackPtr initial - BitVec.ofNat 64 outputOffset)
    (stackBound : stackOffset ≤ 1168) (outputBound : outputOffset ≤ 1168)
    (bound : offset ≤ 1168) (above : offset + 8 ≤ stackOffset)
    (apart : outputOffset + len ≤ offset ∨ offset + outputBytes ≤ outputOffset)
    {i : Nat} (hi : i < len) (span : len ≤ offset + 8) :
    t.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      s.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  have bounds := stack_bounds pre.stack
  have addr : (stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat =
      (stackPtr initial).toNat - offset + i := by
    rw [BitVec.toNat_add, stack_sub_toNat pre.stack bound, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : i < 2^64), Nat.mod_eq_of_lt (by omega)]
  have sp : (stackPtr s).toNat = (stackPtr initial).toNat - stackOffset := by
    rw [rsp, stack_sub_toNat pre.stack stackBound]
  have out : (s.regValue .rdi).toNat = (stackPtr initial).toNat - outputOffset := by
    rw [output, stack_sub_toNat pre.stack outputBound]
  apply result.frame
  intro region hr hin
  have cases : region = registerRegion s .rdi outputBytes ∨ region = Stack.region s reserve := by
    simpa using hr
  rcases cases with rfl | rfl
  · change (s.regValue .rdi).toNat ≤ _ ∧ _ < (s.regValue .rdi).toNat + outputBytes at hin
    rw [out, addr] at hin
    omega
  · change (stackPtr s).toNat - reserve ≤ _ ∧
      _ < (Stack.region s reserve).start + (Stack.region s reserve).size at hin
    rw [stack_region_end, sp, addr] at hin
    omega

end P256.Proofs.Nonce.UpdateValue
