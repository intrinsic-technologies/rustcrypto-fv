import P256.Proofs.Sec1.Affine.Uncompressed.Curve.SquareY
import P256.Proofs.Sec1.Affine.Uncompressed.Curve.CubeX
import P256.Proofs.Sec1.Affine.Uncompressed.Curve.LinearX
import P256.Proofs.Sec1.Affine.Uncompressed.Curve.Sum

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Curve

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure EquationReady [Bindings] (s t : RamState) (bytes : ByteArray) : Prop extends Frame s t where
  rip : t.RIP = 0x110b5a
  output : t.regValue .rbx = s.regValue .rdi
  squarePointer : t.regValue .rbp = stackPtr s-184
  equationPointer : t.regValue .r14 = stackPtr s-480
  xValid : t.regValue .r15 = if xCoordinate bytes < P256.Spec.Operations.domain.p then 1 else 0
  yValid : t.external[stackPtr s-748]? = some (if yCoordinate bytes < P256.Spec.Operations.domain.p then 1 else 0)
  xValue : MontgomeryAt t (stackPtr s-280) (canonical (xCoordinate bytes))
  yValue : MontgomeryAt t (stackPtr s-312) (canonical (yCoordinate bytes))
  square : MontgomeryAt t (stackPtr s-184)
    (canonical (yCoordinate bytes)*canonical (yCoordinate bytes)%P256.Spec.Operations.domain.p)
  equation : MontgomeryAt t (stackPtr s-480)
    ((canonical (xCoordinate bytes)*canonical (xCoordinate bytes)*canonical (xCoordinate bytes)+
      P256.Spec.Operations.domain.a*canonical (xCoordinate bytes)+P256.Spec.Operations.domain.b)%P256.Spec.Operations.domain.p)

theorem arithmetic_execute [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} (pre : AffineDecodePre s boundary bytes) (state : Parsed s t bytes) :
    ∃ fuel u, Advances boundary fuel t u ∧ EquationReady s u bytes := by
  obtain ⟨n0,a,run0,sa,pa⟩ := squareY_execute pre state
  have xa := pa.montgomery (by simp [preservedWindows]) state.xValue
  obtain ⟨n1,b,run1,sb,ipb,b12,b13,vb,pb,b5,mb⟩ :=
    cubeX_execute pre sa.toFrameState sa.rip sa.xPointer xa
  have xb := pb.montgomery (by simp [preservedWindows]) xa
  have wb := sa.value.of_bytes_eq mb
  obtain ⟨n2,c,run2,sc,ipc,c14,vc,zc,wc,pc,rc⟩ := linearX_execute pre sb ipb b13 xb vb wb
  obtain ⟨n3,u,run3,su,ipu,u14,u5,vu,wu,pu⟩ := sum_execute pre sc ipc
    ((rc .r12 (by simp)).trans b12) c14 zc vc wc
  have preserved := ((pa.trans pb).trans pc).trans pu
  rw [arithmetic_eq] at vu
  refine ⟨n0+n1+n2+n3,u,((run0.trans run1).trans run2).trans run3,
    ⟨su,ipu,(preserved.1 .rbx (by simp)).trans state.output,
      u5.trans ((rc .rbp (by simp)).trans (b5.trans sa.squarePointer)),u14,
      (preserved.1 .r15 (by simp)).trans state.xValid,?_,
      preserved.montgomery (by simp [preservedWindows]) state.xValue,
      preserved.montgomery (by simp [preservedWindows]) state.yValue,wu,vu⟩⟩
  have byte := preserved.2 (748,1) (by simp [preservedWindows]) 0 (by decide)
  simp only [BitVec.add_zero] at byte
  exact byte.trans state.yValid

end P256.Proofs.Sec1.Affine.Uncompressed.Curve
