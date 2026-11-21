import P256.Proofs.Sec1.SquareRoot.Exponent.Finish.Copy
import P256.Proofs.Sec1.SquareRoot.Exponent.Finish.Epilogue
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot

open P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem exponent_finish [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre s boundary x) (h : ExponentFinishState s t x)
    (execution : ∃ fuel, Advances boundary fuel s t) :
    ∃ u, CalleeResult s u boundary 32 1584 ∧ Field.MontgomeryAt u (s.regValue .rdi)
      (x ^ sqrtExponent % P256.Spec.Operations.domain.p) := by
  obtain ⟨v, run, frame, rip, output⟩ := exponent_copy_setup ctx.toCalleePre h
  obtain ⟨w, step, ready, effect⟩ := jmp_rel8_effect_step 0x11592a 0x22 (by decide +kernel) v
    (readyToStep frame.machine frame.bindingsSupported)
    (programText_slice (programLoaded_codeIn frame.loaded) 0x1592a [0xeb, 0x22]
      (by decide +kernel) (by decide +kernel)) rip
  have ripW : w.RIP = 0x11594e := effect.rip
  have next : Advances boundary 1 v w := Advances.of_step step (.inl (by
    rw [ripW]
    exact boundary_ne_program ctx.outerBoundary
      (inProgram_of_textOffset 0x1594e (by decide))))
  have frameW := frame.of_registers ready effect.agrees (by simp) (by simp [Component.Covers])
  have memory : w.external = v.external := effect.agrees.external (by simp [Component.Covers])
  obtain ⟨fuel, runS⟩ := execution
  obtain ⟨u, result, memoryU⟩ := exponent_epilogue ctx.toCalleePre frameW
    ⟨fuel + 9 + 1, (runS.trans run).trans next⟩ ripW
  refine ⟨u, result, montgomeryAt_of_memory (fun a => ?_) output⟩
  exact congrArg (fun m : Ram => m[a]?) (memoryU.trans memory)

end P256.Proofs.Sec1.SquareRoot
