import P256.Proofs.Field.Inverse.Setup.Call
import P256.Proofs.Field.Inverse.State
import P256.Proofs.Program.CalleeStackFrame

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program

theorem safeGcd_result_frame [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (rsp : stackPtr t = stackPtr s - 176)
    (output : t.regValue .rdi = stackPtr s - 168)
    (result : CalleeResult t u boundary 40 704) :
    MemoryWriteFrame t u #v[registerRegion s .rdi 40, ScalarFrame.Work.region s 880 128] := by
  have memory := result.stack_frame pre.stack rsp output (savedBytes := 128)
    (by decide) (by decide) (by decide) (by decide)
  intro a ha
  apply memory a
  intro region hr hin
  have eq : region = ScalarFrame.Work.region s 880 128 := by simpa using hr
  subst region
  exact ha _ (by simp) hin

theorem safeGcd_result_read [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (rsp : stackPtr t = stackPtr s - 176)
    (output : t.regValue .rdi = stackPtr s - 168)
    (result : CalleeResult t u boundary 40 704)
    {offset n : Nat} (bound : offset ≤ 128) (size : n/8 ≤ offset+8) :
    memLoad u.external (stackPtr s - BitVec.ofNat 64 offset) n =
      memLoad t.external (stackPtr s - BitVec.ofNat 64 offset) n :=
  ScalarFrame.Work.read pre (by decide) (safeGcd_result_frame pre rsp output result) bound size


theorem safeGcd_result_saved [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (rsp : stackPtr t = stackPtr s - 176)
    (output : t.regValue .rdi = stackPtr s - 168)
    (saved : SavedWords s t) (result : CalleeResult t u boundary 40 704) :
    SavedWords s u := by
  have read (offset : Nat) (bound : offset ≤ 128) :
      memLoad u.external (stackPtr s - BitVec.ofNat 64 offset) 64 =
        memLoad t.external (stackPtr s - BitVec.ofNat 64 offset) 64 :=
    safeGcd_result_read pre rsp output result bound (by omega)
  refine ⟨(read 16 (by decide)).trans saved.1, (read 8 (by decide)).trans saved.2.1, ?_⟩
  have ret := read 0 (by decide)
  simp only [BitVec.sub_zero] at ret
  exact ret.trans saved.2.2

theorem safeGcd_result_registers [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (agrees : AgreesExcept (callComponents s) s t)
    (result : CalleeResult t u boundary 40 704) :
    (∀ r ∈ [Syntax.Reg.r12, .r13, .r14, .r15], u.regValue r = s.regValue r) ∧
      u.MXCSR = s.MXCSR ∧ u.FP87_Control = s.FP87_Control := by
  refine ⟨?_, result.mxcsr.trans (agrees.mxcsr (by
    simp [callComponents, setupComponents, entryComponents, pushSequenceFrame])),
    result.fp87.trans (agrees.fcw (by
      simp [callComponents, setupComponents, entryComponents, pushSequenceFrame]))⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (result.calleeSaved .r12 (by decide)).trans
      (agrees.read (n := 64) (r := 12) (by
        simp [callComponents, setupComponents, entryComponents, pushSequenceFrame]))
  · exact (result.calleeSaved .r13 (by decide)).trans
      (agrees.read (n := 64) (r := 13) (by
        simp [callComponents, setupComponents, entryComponents, pushSequenceFrame]))
  · exact (result.calleeSaved .r14 (by decide)).trans
      (agrees.read (n := 64) (r := 14) (by
        simp [callComponents, setupComponents, entryComponents, pushSequenceFrame]))
  · exact (result.calleeSaved .r15 (by decide)).trans
      (agrees.read (n := 64) (r := 15) (by
        simp [callComponents, setupComponents, entryComponents, pushSequenceFrame]))


theorem safeGcd_call_state [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (child : SafeGcdPre t boundary)
    (agrees : AgreesExcept (callComponents s) s t)
    (rbx : t.regValue .rbx = s.regValue .rdi) (saved : SavedWords s t) :
    SavedState s t := by
  refine ⟨child.bindingsSupported, child.machine, child.loaded, child.directionFlag,
    agrees.grow, ?_, ?_, rbx,
    agrees.mxcsr (by simp [callComponents, setupComponents, entryComponents, pushSequenceFrame]),
    agrees.fcw (by simp [callComponents, setupComponents, entryComponents, pushSequenceFrame]),
    saved⟩
  · intro a ha
    apply safeGcd_call_frame pre agrees a
    intro r hr
    have eq : r = Stack.region s 880 := by simpa using hr
    rw [eq]
    exact ha _ (by simp)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact agrees.read (n := 64) (r := 12) (by simp [callComponents, setupComponents, entryComponents, pushSequenceFrame])
    · exact agrees.read (n := 64) (r := 13) (by simp [callComponents, setupComponents, entryComponents, pushSequenceFrame])
    · exact agrees.read (n := 64) (r := 14) (by simp [callComponents, setupComponents, entryComponents, pushSequenceFrame])
    · exact agrees.read (n := 64) (r := 15) (by simp [callComponents, setupComponents, entryComponents, pushSequenceFrame])

theorem safeGcd_result_state [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (state : SavedState s t)
    (rsp : stackPtr t = stackPtr s - 176) (output : t.regValue .rdi = stackPtr s - 168)
    (ret : (returnBoundary t).rip = 0x11411e) (result : CalleeResult t u boundary 40 704) :
    FrameState s u ∧ u.RIP = 0x11411e := by
  have frame := safeGcd_result_frame pre rsp output result
  refine ⟨⟨⟨result.bindingsSupported, result.machine, result.loaded, result.directionFlag,
    fun a ha => result.allocated a (state.allocated a ha),
    memoryWriteFrame_trans state.frame (ScalarFrame.Work.frame pre frame), ?_,
    (result.calleeSaved .rbx (by simp)).trans state.rbx,
    result.mxcsr.trans state.mxcsr, result.fp87.trans state.fp87,
    safeGcd_result_saved pre rsp output state.saved result⟩, ?_⟩, result.rip.trans ret⟩
  · intro r hr
    apply (result.calleeSaved r ?_).trans (state.registers r hr)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp
  · change u.regValue .rsp = _
    rw [result.rsp]
    change stackPtr t + 8 = _
    rw [rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl

end P256.Proofs.Field.Inverse
