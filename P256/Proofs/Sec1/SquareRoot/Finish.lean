import P256.Proofs.Sec1.SquareRoot.Validity
import P256.Proofs.Sec1.SquareRoot.Choice
import P256.Proofs.Sec1.SquareRoot.SelectResult
import P256.Proofs.Sec1.SquareRoot.OutputResult
import P256.Proofs.Sec1.SquareRoot.Return
import P256.Proofs.Sec1.SquareRoot.Value

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program

theorem finish_square_root [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {x fuel : Nat} (pre : Pre s boundary) (state : FrameState s t)
    (run : Advances boundary fuel s t) (rip : t.RIP = 0x11450a)
    (original : Field.MontgomeryAt t (stackPtr s - 392) x)
    (copy : Field.MontgomeryAt t (stackPtr s - 576) (candidate x))
    (square : Field.MontgomeryAt t (stackPtr s - 536)
      (candidate x * candidate x % P256.Spec.Operations.domain.p)) :
    ∃ u, CalleeResult s u boundary 40 2176 ∧ SquareRootResultAt u (s.regValue .rdi) x := by
  let select := decide (candidate x * candidate x % P256.Spec.Operations.domain.p = x)
  obtain ⟨n1, t1, run1, state1, rip1, di1, mem1⟩ := validity_stage pre state rip original square
  obtain ⟨t2, run2, state2, rip2, ax2, bytes2⟩ := choice_stage pre state1 rip1
  have di1' : t1.regValue .rdi = if select then 1 else 0 := by
    dsimp only [select]
    simp only [decide_eq_true_eq]
    simpa only [eq_comm] using di1
  have ax2' : t2.regValue .rax = if select then 1 else 0 := by
    change t2.regValue .rax = ((t1.regValue .rdi).setWidth 8).setWidth 64 at ax2
    rw [ax2, di1']
    cases select <;> rfl
  have copy2 : Field.MontgomeryAt t2 (stackPtr s - 576) (candidate x) := by
    apply copy.of_bytes_eq
    intro i hi
    exact (bytes2 (by decide) (by decide) i hi).trans
      (congrArg (fun m : Ram => m[_]?) mem1)
  obtain ⟨n3, t3, run3, state3⟩ := select_prepare pre state2 rip2 ax2' copy2
  obtain ⟨n4, t4, run4, state4, rip4, bp4, selected4⟩ := select_stage pre state3
  obtain ⟨n5, t5, run5, state5, rip5, output5, valid5⟩ :=
    output_stage pre state4 rip4 bp4 selected4
  obtain ⟨u, result, memory⟩ := finish_return pre state5 rip5
    (((((run.trans run1).trans run2).trans run3).trans run4).trans run5)
  refine ⟨u, result, result_of_selected original.1 ?_ ?_⟩
  · have out := output5.of_bytes_eq (t := u) (fun i _ => congrArg (fun m : Ram => m[_]?) memory)
    simpa only [select, decide_eq_true_eq] using out
  · rw [memory]
    simpa only [select, decide_eq_true_eq] using valid5

end P256.Proofs.Sec1.SquareRoot
