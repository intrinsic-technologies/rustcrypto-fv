import P256.Proofs.Generate.Sampler.Finish.Copy
import P256.Proofs.Generate.Sampler.Finish.Call
import P256.Proofs.Generate.Sampler.Finish.Movsq
import P256.Proofs.Generate.Sampler.Finish.Epilogue

set_option autoImplicit false

namespace P256.Proofs.Generate.Sampler.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Program Program.ScalarFrame SecretKeyFromBytes.Scalar

theorem finish [Bindings] {s t : RamState} {boundary : ReturnBoundary} {input : ByteArray} {d : Nat}
    (pre : Pre s boundary input) (state : State s t) (rip : t.RIP = 0x100d1d)
    (scalar : Nat256At t (stackPtr s - 256) d)
    (pointer : memLoad t.external (stackPtr s - 192) 64 = s.regValue .rdi)
    (execution : ∃ fuel, Advances boundary fuel s t) :
    ∃ u, Result s u boundary ∧ Nat256At u (s.regValue .rdi) d ∧
      Sec1.AffineAt u (s.regValue .rdi + 32) (Points.mul d Operations.domain.G) ∧
      u.regValue .rax = s.regValue .rdi := by
  have inputAddr : stackPtr t + 8 = stackPtr s - 256 :=
    scalar_stack_address (frameOffset := 264) state.rsp (by decide) (by decide)
  have pointerAddr : stackPtr t + 72 = stackPtr s - 192 :=
    scalar_stack_address (frameOffset := 264) state.rsp (by decide) (by decide)
  have xt : Nat256At t (stackPtr t + 8) d := by rw [inputAddr]; exact scalar
  obtain ⟨na,a,ha,sa,ipa,xa,ga⟩ := copy pre state false rip xt
  change Nat256At a (stackPtr a + 40) d at xa
  have spa : stackPtr a = stackPtr t := sa.rsp.trans state.rsp.symm
  have pa : memLoad a.external (stackPtr a + 72) 64 = s.regValue .rdi := by
    rw [spa]
    apply Eq.trans (b := memLoad t.external (stackPtr t + 72) 64)
    rotate_left
    · rw [pointerAddr]; exact pointer
    apply memLoad_congr
    intro i hi
    apply memByte_congr
    exact copy_byte ga (src := 72) (len := 8)
      (by unfold OffsetsApart; decide +kernel) (by decide) i hi
  have original : Nat256At a (stackPtr a+8) d := by
    rw [spa]
    refine ⟨xt.1,fun i hi => ?_⟩
    exact (copy_byte ga (src := 8) (len := 32)
      (by unfold OffsetsApart; decide +kernel) (by decide) i hi).trans (xt.2 i hi)
  obtain ⟨nb,b,hb,sb,ipb,xb,pb,ob⟩ := public_point pre sa ipa original xa pa
  obtain ⟨nc,c,hc,sc,ipc,xc,gc⟩ := copy pre sb true ipb xb
  change Nat256At c (stackPtr c + 80) d at xc
  have spc : stackPtr c = stackPtr b := sc.rsp.trans sb.rsp.symm
  have pc : Sec1.AffineAt c (stackPtr c + 112) (Points.mul d Operations.domain.G) := by
    rw [spc]
    apply pb.of_bytes_eq
    intro i hi
    exact copy_byte gc (src := 112) (len := 65)
      (by unfold OffsetsApart; decide +kernel) (by decide) i hi
  have oc : memLoad c.external (stackPtr c + 72) 64 = s.regValue .rdi := by
    rw [spc]
    refine Eq.trans ?_ ob
    apply memLoad_congr
    intro i hi
    apply memByte_congr
    exact copy_byte gc (src := 72) (len := 8)
      (by unfold OffsetsApart; decide +kernel) (by decide) i hi
  obtain ⟨v,hv,sv,ipv,source,count,destination,rax,mem,sp⟩ := prepare_output pre sc ipc oc
  have xv : Nat256At v (stackPtr v + 80) d := by simpa only [Nat256At,mem,sp] using xc
  have pv : Sec1.AffineAt v (stackPtr v + 112) (Points.mul d Operations.domain.G) := by
    rw [sp]
    exact pc.of_bytes_eq (fun i hi => by rw [mem])
  obtain ⟨w,hw,sw,ipw,xw,pw,axw⟩ := movsq pre sv ipv destination source count xv pv
  obtain ⟨n,hn⟩ := execution
  obtain ⟨u,result,memory,axu⟩ := epilogue pre sw ipw
    ⟨n+na+nb+nc+4+13, ((((hn.trans ha).trans hb).trans hc).trans hv).trans hw⟩
  refine ⟨u,result,?_,?_,axu.trans (axw.trans rax)⟩
  · simpa only [Nat256At,memory] using xw
  · exact pw.of_bytes_eq (fun i hi => by rw [memory])

end P256.Proofs.Generate.Sampler.Finish
