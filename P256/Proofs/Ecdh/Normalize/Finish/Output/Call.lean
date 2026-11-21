import P256.Proofs.Ecdh.Normalize.Finish.Output.Prepare
import P256.Proofs.Ecdh.Normalize.Conversion
import P256.Proofs.Program.FieldCall.Unary

set_option autoImplicit false

namespace P256.Proofs.Ecdh.Normalize.Finish.Output

open P256.Spec.Program P256.Spec.Program.Routines Program Program.ScalarFrame Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

def conversionLayout : StackCallLayout 3464 32 32 40 :=
  ⟨2064,1808,1040,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩

theorem conversion [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (pre : CalleePre s boundary 0x100000 32 32 3464) (state : Prepared s t boundary x) :
    ∃ u, FrameState s u 32 3464 2056 ∧ (∃ fuel, Advances boundary fuel s u) ∧
      u.RIP = 0x10052f ∧ u.regValue .rbx = s.regValue .rdi ∧
      Nat256At u (stackPtr s - 1040) x := by
  obtain ⟨n,u,run,frame,rip,value,saved,_,_⟩ := FieldCall.unary_call (x := x) (resultAt := fun u a => Nat256At u a x) pre state.toFrameState
    conversionLayout rfl (by decide) 0x52a 0x77d1
    (by decide) (by decide +kernel) (by decide) (by decide)
    (inProgram_of_textOffset 0x7d00 (by decide))
    (fun _ hp hx => Conversion.callee_correct hp hx) state.rip state.rsi state.rdi state.x
  obtain ⟨m,before⟩ := state.execution
  exact ⟨u,frame,⟨m+n,before.trans run⟩,rip,(saved .rbx (by simp)).trans state.output,value⟩

end P256.Proofs.Ecdh.Normalize.Finish.Output
