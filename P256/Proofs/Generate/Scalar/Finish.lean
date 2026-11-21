import P256.Proofs.Generate.Scalar.Choice
import P256.Proofs.Generate.Scalar.Tag
import P256.Proofs.Generate.Scalar.Return

set_option autoImplicit false

namespace P256.Proofs.Generate.Scalar

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program
open SecretKeyFromBytes.Scalar (Nat256At)

theorem finish_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary} {value : Nat}
    (pre : Pre s boundary) (state : State s t) (rip : t.RIP = 0x112fa6)
    (rsp : stackPtr t = stackPtr s - 56) (output : t.regValue .rbx = s.regValue .rdi)
    (bound : value < 2^256) (decoded : Decoded t value)
    (flag : t.regValue .rdi = if value < Operations.domain.n then 1 else 0)
    (execution : ∃ n, Advances boundary n s t) :
    ∃ u, CalleeResult s u boundary 33 72 ∧ Nat256At u (s.regValue .rdi) value ∧
      u.external[s.regValue .rdi + 32]? = some (if value < Operations.domain.n then 1 else 0) ∧
      u.regValue .rax = s.regValue .rdi := by
  obtain ⟨a, runA, stateA, ripA, rspA, axA, agA⟩ := choice_stage pre state rip rsp
  have decodedA := decoded.of_agrees agA (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp)
  have outputA : a.regValue .rbx = s.regValue .rdi :=
    (agA.read (n := 64) (r := 3) (by simp)).trans output
  have flagA : a.regValue .rax = if decide (value < Operations.domain.n) then 1 else 0 := by
    change a.regValue .rax = ((t.regValue .rdi).setWidth 8).setWidth 64 at axA
    rw [axA, flag]
    split <;> simp_all
  obtain ⟨nB, b, runB, stateB, ripB, scalarB, agB⟩ :=
    output_limbs pre stateA ripA outputA bound decodedA
  have outputB : b.regValue .rbx = s.regValue .rdi :=
    (agB.read (n := 64) (r := 3) (by simp)).trans outputA
  have flagB : b.regValue .rax = if decide (value < Operations.domain.n) then 1 else 0 :=
    (agB.read (n := 64) (r := 0) (by simp)).trans flagA
  obtain ⟨c, runC, stateC, ripC, rspC, axC, scalarC, tagC⟩ :=
    output_tag pre stateB ripB outputB flagB scalarB
  have spC : stackPtr c = stackPtr s - 56 :=
    rspC.trans ((agB.read (n := 64) (r := 4) (by simp)).trans rspA)
  obtain ⟨n, run⟩ := execution
  obtain ⟨u, result, memory, ax⟩ := scalar_return pre stateC ripC spC
    ⟨n+6+nB+2, ((run.trans runA).trans runB).trans runC⟩
  refine ⟨u, result, ?_, ?_, ax.trans axC⟩
  · simpa only [Nat256At, memory] using scalarC
  · simpa only [memory, decide_eq_true_eq] using tagC

end P256.Proofs.Generate.Scalar
