import P256.Proofs.Scalar.Multiply.Schoolbook
import P256.Proofs.Scalar.Multiply.Copy
import P256.Proofs.Scalar.Multiply.Reduction
import P256.Proofs.Scalar.Multiply.Epilogue

set_option autoImplicit false

namespace P256.Proofs.Scalar.Multiply

open P256.Proofs.Program
open P256.Proofs.Field.Montgomery.Wrapper (scratch)
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem multiply_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {a b : Nat} (pre : MultiplyPre s boundary)
    (leftInput : Nat256At s (s.regValue .rsi) a)
    (rightInput : Nat256At s (s.regValue .rdx) b) :
    ∃ t, CalleeResult s t boundary 32 280 ∧
      Nat256At t (s.regValue .rdi) (a * b % Operations.domain.n) := by
  obtain ⟨schoolFuel, product, schoolRun, schoolState, schoolRip, productBytes⟩ :=
    schoolbook_stage pre leftInput rightInput
  obtain ⟨copyFuel, copied, copyRun, copyState, copyEffect⟩ :=
    copy_stage pre schoolState schoolRip
  have bytes : Bytes copied.external (scratch s) 64
      (fun i => UInt8.ofNat ((a*b) / 256^i % 256)) :=
    fun i hi => (copy_bytes pre schoolState copyEffect i hi).trans (productBytes i hi)
  have left : copied.regValue .rsi = scratch s :=
    copyEffect.writes.2.2.2.1.trans schoolState.rsp
  have right : copied.regValue .rdx = scratch s + 32 :=
    copyEffect.writes.2.2.1.trans (congrArg (fun a : BitVec 64 => a + 32) schoolState.rsp)
  have destination : copied.regValue .rdi = s.regValue .rdi :=
    copyEffect.writes.2.2.2.2.1.trans schoolState.rbx
  have bound : a*b < 2^256 * 2^256 :=
    Nat.mul_lt_mul_of_lt_of_lt leftInput.1 rightInput.1
  obtain ⟨reduceFuel, reduced, reduceRun, reduceState, reduceRip, output⟩ :=
    reduction_stage pre.toCalleePre copyState copyEffect.rip left right destination bytes bound
  obtain ⟨final, result, memory⟩ := finish_return pre reduceState reduceRip
    ((schoolRun.trans copyRun).trans reduceRun)
  refine ⟨final, result, output.1, ?_⟩
  intro i hi
  rw [memory]
  exact output.2 i hi

end P256.Proofs.Scalar.Multiply
