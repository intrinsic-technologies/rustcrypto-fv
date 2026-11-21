import P256.Proofs.Verifying.Core.Digest.Finish.Copy
import P256.Proofs.Verifying.Core.Normalize.CopyFacts

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Normalize.CopyX

open P256.Spec P256.Spec.Program Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame

theorem copyEffect_eq (p : BitVec 64) (s : RamState) :
    Digest.Finish.CopyBlock.effect p s =
      Copy32.effect (p+51) stackPtr (fun t => stackPtr t+128) s := by
  have hs : rspOf s = stackPtr s := rfl
  simp only [Digest.Finish.CopyBlock.effect,Copy32.effect,BitVec.add_assoc]
  congr 8 <;> bv_omega

theorem run [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (pre : Core.Pre s boundary) (state : Frame s t) (rip : t.RIP = 0x10deaa)
    (input : Field.MontgomeryAt t (stackPtr s-1176) x) :
    ∃ n u, Advances boundary n t u ∧ Frame s u ∧ u.RIP = 0x10dedd ∧
      Field.MontgomeryAt u (stackPtr s-1048) x ∧
      AgreesExcept (Copy32.components (stackPtr s-1048)) t u := by
  obtain ⟨n,u,execution,frame,effect,output,_⟩ := Digest.Finish.copy pre state
    0xdeaa (by decide) (by decide +kernel) rip input.2
  have destination : frameBase s+128#64 = stackPtr s-1048 := by
    simp only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  rw [destination] at output
  refine ⟨n,u,execution,frame,effect.rip,⟨input.1,output⟩,?_⟩
  change (Digest.Finish.CopyBlock.effect _ t).Holds t u at effect
  rw [copyEffect_eq] at effect
  have agrees := Copy32.frame effect
  change AgreesExcept (Copy32.components (stackPtr t+128)) t u at agrees
  rw [state.rsp] at agrees
  change AgreesExcept (Copy32.components (frameBase s+128#64)) t u at agrees
  rw [destination] at agrees
  exact agrees

end P256.Proofs.Verifying.Core.Normalize.CopyX
