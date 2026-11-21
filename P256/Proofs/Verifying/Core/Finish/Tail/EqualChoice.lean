import P256.Proofs.Verifying.Core.Finish.Tail.EqualFrame
import P256.Proofs.Generate.Zero.Prefix
import P256.Proofs.Generate.Zero.Mask
import P256.Proofs.Program.ScalarFrame.Choice

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Finish.Tail.Equal

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame
open SecretKeyFromBytes.Scalar
open Generate.Zero (prefixClobbers prefix_correct mask_arguments maskBytes)

theorem choice [Bindings] {s : RamState} {boundary : ReturnBoundary} {x y : Nat}
    (pre : CalleePre s boundary 0x1132e0 32 32 32)
    (left : Nat256At s (s.regValue .rdi) x)
    (right : Nat256At s (s.regValue .rsi) y) :
    ∃ t, (∃ n, Advances boundary n s t) ∧ ReadyToStep t ∧
      AgreesExcept (clobbers s) s t ∧ t.RIP = 0x1132fd ∧
      stackPtr t = stackPtr s-8 ∧
      (t.regValue .rax).setWidth 8 = if x=y then 1 else 0 := by
  obtain ⟨a,state⟩ := prefix_correct (offset := 0x132e0) (disp := 0x5f7d) pre
    (by constructor <;> decide +kernel) left right
  obtain ⟨b,runB,readyB,agreesB,ripB,valueB⟩ := mask_arguments boundary 0x1132f3 state.ready
    (programText_slice (programLoaded_codeIn state.loaded) 0x132f3 maskBytes
      (by decide) (by decide +kernel)) state.rip
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x132f5 (by decide)))
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x132f8 (by decide)))
  have ab : AgreesExcept (clobbers s) s b :=
    (state.agrees.trans agreesB).mono (by simp [clobbers,prefixClobbers])
  have spB : stackPtr b = stackPtr s-8 :=
    (agreesB.read (n := 64) (r := 4) (by simp)).trans state.rsp
  have diB : b.regValue .rdi = if x=y then 1 else 0 := by
    rw [valueB,state.value]
    split <;> rfl
  obtain ⟨t,runT,readyT,spT,ripT,valueT,agT⟩ := choice_step pre
    (frameOffset := 8) (by decide) (by decide) readyB (loaded pre ab) ab.grow spB
    0x132f8 0x5d73 (by decide) (by decide +kernel) (by decide +kernel) ripB
  have finalAgrees : AgreesExcept (clobbers s) s t :=
    (ab.trans agT).mono (by simp [clobbers,prefixClobbers,choiceClobbers])
  obtain ⟨n,runA⟩ := state.execution
  refine ⟨t,⟨n+2+6,(runA.trans runB).trans runT⟩,readyT,finalAgrees,ripT,spT.trans spB,?_⟩
  change t.regValue .rax = ((b.regValue .rdi).setWidth 8).setWidth 64 at valueT
  rw [valueT,diB]
  split <;> rfl

end P256.Proofs.Verifying.Core.Finish.Tail.Equal
