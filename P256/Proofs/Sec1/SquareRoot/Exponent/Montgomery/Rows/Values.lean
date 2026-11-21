import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Rows.Execution
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Rows.Input
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Rows.SecondValues
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Rows.ThirdValues

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Montgomery.Rows

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem trace_fourthState [Bindings] {entry : BitVec 64} {boundary : ReturnBoundary}
    {s t : RamState} {a b : Vector (BitVec 64) 4}
    (pre : Pre entry boundary a b s) (trace : Trace entry s t) :
    FourthState trace.s8
      (nextRow (nextRow (firstRow a[0] a[1] b) a[1] a[2] b) a[2] a[3] b) a[3] b := by
  have start : SecondState s (firstRow a[0] a[1] b) a[1] b :=
    ⟨pre.saved, pre.digit, pre.first, pre.second, pre.low, pre.mid, pre.high, pre.carry⟩
  have st1 := secondStart_values trace.e1 start
  have st2 := secondMiddle_values trace.e2 st1
  have st3 := secondHigh_values trace.e3 st2
  have f1 := secondStart_frame trace.e1
  have f2 := scratch_trans f1 (secondMiddle_frame trace.e2)
  have f3 := scratch_trans f2 (secondHigh_frame trace.e3)
  have ptr1 := secondStart_pointer trace.e1
  have ptr2 := (secondMiddle_pointer trace.e2).trans ptr1
  have ptr3 := (secondHigh_pointer trace.e3).trans ptr2
  have hn2 : (Operand.mem (savedPtr trace.s3+16#64) : Operand 64).read trace.s3 = a[2] := by
    rw [ptr3]
    exact (input_word_preserved f3 pre.inputApart (2 : Fin 4)).trans (pre.inputWords 2)
  have st4 := secondTop_values trace.e4 st3 hn2
  have st5 := thirdStart_values trace.e5 st4
  have st6 := thirdMiddle_values trace.e6 st5
  have st7 := thirdHigh_values trace.e7 st6
  have f4 := scratch_trans f3 (secondTop_frame trace.e4)
  have f5 := scratch_trans f4 (thirdStart_frame trace.e5)
  have f6 := scratch_trans f5 (thirdMiddle_frame trace.e6)
  have f7 := scratch_trans f6 (thirdHigh_frame trace.e7)
  have ptr4 := (secondTop_pointer trace.e4).trans ptr3
  have ptr5 := (thirdStart_pointer trace.e5).trans ptr4
  have ptr6 := (thirdMiddle_pointer trace.e6).trans ptr5
  have ptr7 := (thirdHigh_pointer trace.e7).trans ptr6
  have hn3 : (Operand.mem (savedPtr trace.s7+24#64) : Operand 64).read trace.s7 = a[3] := by
    rw [ptr7]
    exact (input_word_preserved f7 pre.inputApart (3 : Fin 4)).trans (pre.inputWords 3)
  exact thirdTop_values trace.e8 st7 hn3

end P256.Proofs.Sec1.SquareRoot.Montgomery.Rows
