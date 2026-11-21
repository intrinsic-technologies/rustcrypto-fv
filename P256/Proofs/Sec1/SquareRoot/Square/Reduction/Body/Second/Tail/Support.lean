import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.First.Support
import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Second.Prefix
import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Second.Model
import P256.Proofs.Common.Instructions.Setb.Memory.Triple
import P256.Proofs.Common.Instructions.Mul.Memory.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Second.Tail

open P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

variable [Bindings] {s t u : RamState} {boundary : ReturnBoundary}

theorem after_store (pre : ReductionPre s boundary)
    (frame : ScalarFrame.FrameState s t 32 112 112) (ready : ReadyToStep u)
    {offset len : Nat} (ho : offset + len ≤ 64)
    (agrees : AgreesExcept [.mem (stackPtr t + BitVec.ofNat 64 offset) len, .rip] t u) :
    ScalarFrame.FrameState s u 32 112 112 := by
  apply frame.after_effect pre.toCalleePre (by decide) ready agrees ?_ (by simp)
  intro c hc a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · refine ⟨ScalarFrame.workRegion s 112, by simp, ?_⟩
    apply ScalarFrame.work_contains pre.toCalleePre (offset := 112-offset) (len := len)
      (by omega) (by omega)
    rw [ScalarFrame.scalar_stack_address (frameOffset := 112) frame.rsp
      (offset := offset) (by decide) (by omega)] at ha
    exact ha
  · exact ha.elim

theorem byte_writable (pre : ReductionPre s boundary)
    (frame : ScalarFrame.FrameState s t 32 112 112) :
    MemWritable t (stackPtr t + 7) 1 := by
  have h := ScalarFrame.stack_writable pre.toCalleePre frame
    (offset := 7) (len := 1) (by decide) (by decide) (by decide)
  exact ⟨h.low, h.mem, h.tables⟩

omit [Bindings] in
theorem mulM64Effect_components (p : BitVec 64) (am : AddrMode) (t : RamState) :
    (mulM64Effect p am t).components = [.reg 0, .reg 2, .flags, .rip] := rfl


theorem prefix_values {v : Nat} (state : First s t v)
    (hpref : (prefixEffect t).Holds t u) :
    let a := t.regValue .r14
    let p0 := Field.Montgomery.product64 a 0xffffffffffffffff
    let p1 := Field.Montgomery.product64 a 0xffffffff
    let x := Field.Montgomery.add64 p1.1 (t.regValue .r15)
    u.regValue .r12 = a ∧ u.regValue .rbp = p0.2 ∧ u.regValue .r13 = x.1 ∧
    u.regValue .r8 = (Field.Montgomery.adc64 p1.2 0 x.2).1 ∧
    (StatusFlags.ofRFLAGS u.RFLAGS).CF = (Field.Montgomery.add64 p0.1 a).2 := by
  have h1 : (Operand.reg 1 : Operand 64).read t = 1 := state.rcx
  have h5 : (Operand.reg 5 : Operand 64).read t = 0xffffffffffffffff := state.rbp
  have h13 : (Operand.reg 13 : Operand 64).read t = 0xffffffff := state.r13
  have ha : (Operand.reg 1 : Operand 64).read t * (Operand.reg 14 : Operand 64).read t =
      t.regValue .r14 := by
    rw [h1]
    exact BitVec.one_mul _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hh := hpref.writes.1
    change u.regValue .r12 = (Operand.reg 1 : Operand 64).read t *
      (Operand.reg 14 : Operand 64).read t at hh
    rwa [ha] at hh
  · have hh := hpref.writes.2.2.2.1
    change u.regValue .rbp = mulHigh64 ((Operand.reg 1 : Operand 64).read t *
      (Operand.reg 14 : Operand 64).read t) ((Operand.reg 5 : Operand 64).read t) at hh
    rw [ha, h5] at hh
    exact hh
  · have hh := hpref.writes.2.2.2.2.2.2
    change u.regValue .r13 = (addSpec ((Operand.reg 1 : Operand 64).read t *
      (Operand.reg 14 : Operand 64).read t * (Operand.reg 13 : Operand 64).read t)
      ((Operand.reg 15 : Operand 64).read t)).1 at hh
    rw [ha, h13] at hh
    exact hh
  · have hh := hpref.writes.2.2.2.2.2.1
    change u.regValue .r8 = (Carry.adcSpec (mulHigh64
      ((Operand.reg 1 : Operand 64).read t * (Operand.reg 14 : Operand 64).read t)
      ((Operand.reg 13 : Operand 64).read t)) 0 (BitVec.ofBool (addSpec
        ((Operand.reg 1 : Operand 64).read t * (Operand.reg 14 : Operand 64).read t *
          (Operand.reg 13 : Operand 64).read t) ((Operand.reg 15 : Operand 64).read t)).2.CF)).1 at hh
    rw [ha, h13] at hh
    exact hh
  · have hh := hpref.flags.1
    change (StatusFlags.ofRFLAGS u.RFLAGS).CF = (addSpec
      ((Operand.reg 1 : Operand 64).read t * (Operand.reg 14 : Operand 64).read t *
        (Operand.reg 5 : Operand 64).read t) ((Operand.reg 14 : Operand 64).read t)).2.CF at hh
    rw [ha, h5] at hh
    exact hh

end P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Second.Tail
