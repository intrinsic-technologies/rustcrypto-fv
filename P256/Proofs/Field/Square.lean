import P256.Proofs.Field.Square.Stage
import P256.Proofs.Field.Montgomery.Wrapper.Copy
import P256.Proofs.Field.Montgomery.Wrapper.Reduction
import P256.Proofs.Field.Montgomery.Wrapper.Epilogue

set_option autoImplicit false

namespace P256.Proofs.Field

open P256.Proofs.Program
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem field_square_correct [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    {x : Nat} (hpre : CalleePre s boundary 0x113800 32 32 280)
    (hx : MontgomeryAt s (s.regValue .rsi) x) :
    ∃ t, CalleeResult s t boundary 32 280 ∧
      MontgomeryAt t (s.regValue .rdi) (x * x % Operations.domain.p) := by
  obtain ⟨schoolFuel, product, schoolRun, schoolState, schoolRip, productBytes⟩ :=
    Square.schoolbook_stage hpre hx.2
  obtain ⟨copyFuel, copied, copyRun, copyState, copyEffect⟩ :=
    Montgomery.Wrapper.copy_stage_at true hpre schoolState schoolRip
  have bytes : Bytes copied.external (Montgomery.Wrapper.scratch s) 64
      (fun i => UInt8.ofNat (((x * 2^256 % Operations.domain.p) *
        (x * 2^256 % Operations.domain.p)) / 256^i % 256)) :=
    fun i hi => (Montgomery.Wrapper.copy_bytes_at hpre schoolState copyEffect i hi).trans
      (productBytes i hi)
  have left : copied.regValue .rsi = Montgomery.Wrapper.scratch s :=
    copyEffect.writes.2.2.2.1.trans schoolState.rsp
  have right : copied.regValue .rdx = Montgomery.Wrapper.scratch s + 32 :=
    copyEffect.writes.2.2.1.trans (congrArg (fun a : BitVec 64 => a + 32) schoolState.rsp)
  have destination : copied.regValue .rdi = s.regValue .rdi :=
    copyEffect.writes.2.2.2.2.1.trans schoolState.rbx
  have bound : (x * 2^256 % Operations.domain.p) * (x * 2^256 % Operations.domain.p) <
      Montgomery.p * 2^256 :=
    Nat.mul_lt_mul_of_lt_of_lt (Nat.mod_lt _ Montgomery.p_pos)
      (Nat.lt_trans (Nat.mod_lt _ Montgomery.p_pos) Montgomery.p_lt_radix)
  obtain ⟨reduceFuel, reduced, reduceRun, reduceState, reduceRip, output⟩ :=
    Montgomery.Wrapper.reduction_stage_at true hpre copyState copyEffect.rip
      left right destination bytes bound
  obtain ⟨final, result, memory⟩ := Montgomery.Wrapper.finish_return_at true hpre reduceState reduceRip
    ((schoolRun.trans copyRun).trans reduceRun)
  refine ⟨final, result, montgomeryAt_product ?_⟩
  refine ⟨output.1, ?_⟩
  intro i hi
  rw [memory]
  exact output.2 i hi

end P256.Proofs.Field
