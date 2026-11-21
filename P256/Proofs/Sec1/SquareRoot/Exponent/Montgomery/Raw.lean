import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.FirstRow.Execution
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.FirstRow.Result
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Inputs
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Rows
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Reduction
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Return
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Interface
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Code
import P256.Proofs.Field.Montgomery.Arithmetic

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot

open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem raw_mul_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {entry : BitVec 64} {a b : Nat}
    (he : Montgomery.Entry entry) (pre : MontgomeryPre s boundary entry)
    (left : Nat256At s (s.regValue .rsi) a)
    (right : Nat256At s (s.regValue .rdx) b)
    (bound : a * b < P256.Spec.Operations.domain.p * 2^256) :
    ∃ t, CalleeResult s t boundary 32 160 ∧
      Nat256At t (s.regValue .rdi)
        (Field.Montgomery.subtractP (Field.Montgomery.reduceFour (a*b))) := by
  obtain ⟨s1, run1, ready1, loaded1, rip1, rsp1, memory1, frame1⟩ :=
    Montgomery.prologue_correct he pre.toCalleePre
  have pre1 := Montgomery.initialize_pre he pre frame1 rip1 rsp1
  have input1 := Montgomery.prologue_inputs pre frame1 left right pre.modulus pre.inverse
  obtain ⟨n2, s2, run2, ready2, loaded2, frame2, trace2⟩ :=
    Montgomery.firstRow_execution he pre.outerBoundary ready1 loaded1 pre1
  obtain ⟨trace2⟩ := trace2
  have pre2 := Montgomery.firstRow_trace_result he pre.outerBoundary pre1 input1
    trace2 ready2 loaded2
  obtain ⟨s3, row3⟩ := Montgomery.Rows.rows_correct pre2
  have hvalue := Montgomery.multiplyWords_limbs (Montgomery.wordsOfNat a) (Montgomery.wordsOfNat b)
  rw [Montgomery.wordsOfNat_value left.1, Montgomery.wordsOfNat_value right.1] at hvalue
  let r := Montgomery.multiplyWords (Montgomery.wordsOfNat a) (Montgomery.wordsOfNat b)
  have hvalue' : (P256.Proofs.SecretKeyFromBytes.Scalar.Limbs.mk r.first r.second r.top.low r.top.mid).toNat +
      2^256*r.top.high.toNat = Field.Montgomery.reduceFour (a*b) := hvalue
  have pre3 : Montgomery.Reduction.Pre entry boundary s3
      ⟨r.first, r.second, r.top.low, r.top.mid⟩ r.top.high := by
    refine ⟨he, row3.ready, row3.loaded, pre.outerBoundary, row3.memory, row3.rip,
      row3.input, row3.modulus, ?_⟩
    rw [hvalue']
    exact Field.Montgomery.reduceFour_lt_two_mul_p _ bound
  obtain ⟨s4, result4⟩ := Montgomery.Reduction.reduction_correct pre3
  have frame23 := Montgomery.Reduction.scratch_trans frame2 row3.frame
  have frame234 := Montgomery.Reduction.scratch_then_components frame23 result4.frame
  have pre4 := Montgomery.epilogue_pre_of_frame pre.toCalleePre frame1 rsp1 memory1
    frame234 result4.ready result4.loaded result4.rip
  have fullframe1 := Montgomery.prologue_frame frame1
  have rdi1 : s1.regValue .rdi = s.regValue .rdi :=
    frame1.read (r := 7) (n := 64) (by simp [P256.Proofs.Common.Field.SquareRoot.Multiply.prologueComponents])
  have fullframe234 := Montgomery.components_frame rsp1 rdi1 frame234
  have fullframe : X86Proofs.AgreesExcept (Montgomery.frame s) s s4 :=
    (fullframe1.trans fullframe234).mono (by simp)
  obtain ⟨n3, run3⟩ := row3.advances
  obtain ⟨n4, run4⟩ := result4.advances
  obtain ⟨t, result, ext⟩ := Montgomery.finish_correct he pre4
    ⟨7+n2+n3+n4, ((run1.trans run2).trans run3).trans run4⟩ fullframe
  have rdi3 : s3.regValue .rdi = s.regValue .rdi :=
    row3.rdi.trans ((Montgomery.Reduction.scratch_rdi frame2).trans rdi1)
  have output := result4.output
  rw [rdi3, hvalue'] at output
  exact ⟨t, result, output.1, by simpa only [ext] using output.2⟩


end P256.Proofs.Sec1.SquareRoot
