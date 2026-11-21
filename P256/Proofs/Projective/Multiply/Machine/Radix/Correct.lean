import P256.Proofs.Projective.Multiply.Machine.Radix.Start
import P256.Proofs.Projective.Multiply.Machine.Radix.Nibbles
import P256.Proofs.Projective.Multiply.Machine.Radix.Recenter
import P256.Proofs.Projective.Multiply.Machine.Radix.Copy
import P256.Proofs.Projective.Multiply.Machine.Radix.Return

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Radix

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Program

theorem radix_correct (bindings : Bindings) : Contract bindings := by
  intro s boundary d pre scalar
  obtain ⟨t,n,run,st,ip,out⟩ := start_correct pre scalar
  obtain ⟨m,u,nibbles,su,ag⟩ := nibbles_correct pre st.toState ip st.encoded st.last
  obtain ⟨k,v,recentered,sv,av⟩ := recenter_correct pre su
  have output : v.regValue .rbx = s.regValue .rdi :=
    ((ag.trans av).read (n := 64) (r := 3) (by simp [digitComponents])).trans out
  obtain ⟨w,l,copied,sw,ipw,outw,bytes⟩ := copy_correct pre sv output
  obtain ⟨final,result,memory,rax⟩ := radix_return pre sw
    (((run.trans nibbles).trans recentered).trans copied) ipw outw
  refine ⟨final,result,rax,?_⟩
  rw [memory]
  exact bytes

end P256.Proofs.Projective.Multiply.Machine.Radix
