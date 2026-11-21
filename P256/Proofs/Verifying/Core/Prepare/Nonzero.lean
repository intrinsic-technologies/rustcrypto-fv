import P256.Proofs.Verifying.Core.Prepare.Compare
import P256.Proofs.Verifying.Core.Prepare.InvertChoice
import P256.Proofs.Verifying.Core.Prepare.Choice
import P256.Proofs.Verifying.Core.Prepare.AcceptScalar

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Prepare

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame
open SecretKeyFromBytes.Scalar

def nonzeroClobbers (s : RamState) : List Component :=
  compareClobbers s ++ [.mem (frameBase s+128) 1]

theorem nonzero [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (pre : Core.Pre s boundary) (state : Frame s t) (second : Bool)
    (rip : t.RIP = if second then 0x10db5f else 0x10dab2)
    (left : Nat256At t (stackPtr s-1176) x)
    (right : Nat256At t (stackPtr s-1048) 0)
    (di : t.regValue .rdi = stackPtr s-1176)
    (si : t.regValue .rsi = stackPtr s-1048) (positive : 0 < x) :
    ∃ n u, Advances boundary n t u ∧ Frame s u ∧
      u.RIP = (if second then 0x10db7f else 0x10dad2) ∧
      AgreesExcept (nonzeroClobbers s) t u := by
  obtain ⟨n,a,ha,sa,ipa,va,ga⟩ := compare pre state second rip left right di si
  have azero : (a.regValue .rax).setWidth 8 = 0 := by
    simp only [va,show x ≠ 0 by omega,ite_false]
  obtain ⟨b,hb,sb,ipb,vb,gb⟩ := invert_choice pre sa second ipa azero
  obtain ⟨c,hc,sc,ipc,vc,gc⟩ := choice_call pre sb second ipb
  have cone : (c.regValue .rax).setWidth 8 = 1 := by rw [vc,vb]; rfl
  obtain ⟨u,hu,su,ipu,gu⟩ := accept_scalar pre sc second ipc cone
  refine ⟨n+3+6+3,u,((ha.trans hb).trans hc).trans hu,su,ipu,?_⟩
  apply (((ga.trans gb).trans gc).trans gu).mono
  simp [nonzeroClobbers,compareClobbers,choiceClobbers]

end P256.Proofs.Verifying.Core.Prepare
