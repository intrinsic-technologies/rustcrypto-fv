import P256.Proofs.Sec1.Affine.Uncompressed.Curve.Arithmetic
import P256.Proofs.Sec1.Affine.Uncompressed.Curve.Output
import P256.Proofs.Sec1.Affine.Uncompressed.Curve.CompareArguments
import P256.Proofs.Sec1.Affine.Uncompressed.Curve.Equality.Call

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Curve

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Compared [Bindings] (s t : RamState) (bytes : ByteArray) : Prop extends Frame s t where
  rip : t.RIP = 0x110be5
  output : t.regValue .rbx = s.regValue .rdi
  xValid : t.regValue .r15 = if xCoordinate bytes < P256.Spec.Operations.domain.p then 1 else 0
  yValid : t.external[stackPtr s-748]? = some (if yCoordinate bytes < P256.Spec.Operations.domain.p then 1 else 0)
  xValue : MontgomeryAt t (stackPtr s-248) (canonical (xCoordinate bytes))
  yValue : MontgomeryAt t (stackPtr s-216) (canonical (yCoordinate bytes))
  result : (t.regValue .rax).setWidth 8 =
    if canonical (yCoordinate bytes)*canonical (yCoordinate bytes)%P256.Spec.Operations.domain.p =
      (canonical (xCoordinate bytes)*canonical (xCoordinate bytes)*canonical (xCoordinate bytes)+
        P256.Spec.Operations.domain.a*canonical (xCoordinate bytes)+P256.Spec.Operations.domain.b)%P256.Spec.Operations.domain.p
    then 1 else 0

theorem compare_execute [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} (pre : AffineDecodePre s boundary bytes) (state : EquationReady s t bytes) :
    ∃ fuel u, Advances boundary fuel t u ∧ Compared s u bytes := by
  obtain ⟨n0,a,run0,sa,ea⟩ := outputX_execute pre state.toFrameState state.rip
  have fa := outputX_frame state.toFrameState ea
  have srcX : stackPtr t+480 = stackPtr s-280 :=
    ScalarFrame.scalar_stack_address (frameOffset := 760) state.rsp (by decide) (by decide)
  have dstX : stackPtr t+512 = stackPtr s-248 :=
    ScalarFrame.scalar_stack_address (frameOffset := 760) state.rsp (by decide) (by decide)
  have xa : MontgomeryAt a (stackPtr s-248) (canonical (xCoordinate bytes)) := by
    rw [← dstX]
    apply outputX_value (by rw [srcX]; exact state.xValue) ea
    have mem := ScalarFrame.stack_readable (frameOffset := 760) pre.toCalleePre sa
      (offset := 512) (len := 32) (by decide) (by decide)
    simpa only [sa.rsp,state.rsp,BitVec.ofNat_eq_ofNat] using mem
  have ya := state.yValue.of_bytes_eq (fun _ hi => output_byte fa
    (by unfold OffsetsApart; decide +kernel) (by decide) hi)
  obtain ⟨n1,b,run1,sb,eb⟩ := outputY_execute pre sa ea.rip
  have fb := outputY_frame sa eb
  have srcY : stackPtr a+448 = stackPtr s-312 :=
    ScalarFrame.scalar_stack_address (frameOffset := 760) sa.rsp (by decide) (by decide)
  have dstY : stackPtr a+544 = stackPtr s-216 :=
    ScalarFrame.scalar_stack_address (frameOffset := 760) sa.rsp (by decide) (by decide)
  have yb : MontgomeryAt b (stackPtr s-216) (canonical (yCoordinate bytes)) := by
    rw [← dstY]
    apply outputY_value (by rw [srcY]; exact ya) eb
    have mem := ScalarFrame.stack_readable (frameOffset := 760) pre.toCalleePre sb
      (offset := 544) (len := 32) (by decide) (by decide)
    simpa only [sb.rsp,sa.rsp,BitVec.ofNat_eq_ofNat] using mem
  have xb := xa.of_bytes_eq (fun _ hi => output_byte fb
    (by unfold OffsetsApart; decide +kernel) (by decide) hi)
  have square := state.square.of_bytes_eq (fun _ hi => (output_byte fb
    (by unfold OffsetsApart; decide +kernel) (by decide) hi).trans
      (output_byte fa (by unfold OffsetsApart; decide +kernel) (by decide) hi))
  have equation := state.equation.of_bytes_eq (fun _ hi => (output_byte fb
    (by unfold OffsetsApart; decide +kernel) (by decide) hi).trans
      (output_byte fa (by unfold OffsetsApart; decide +kernel) (by decide) hi))
  obtain ⟨n2,c,run2,rc,_,ec⟩ := compareArguments_correct boundary pre.outerBoundary b
    (readyToStep sb.machine sb.bindingsSupported)
    (programText_slice (programLoaded_codeIn sb.loaded) 0x10bda compareArgumentsBytes
      (by decide +kernel) (by decide +kernel)) eb.rip
  have fc : AgreesExcept [.reg 7,.reg 6,.rip] b c := ec.agrees
  have mc := fc.external (by simp [Component.Covers])
  have sc := sb.after_registers rc fc (by simp [Component.Covers]) (by simp)
  have wc : c.regValue .rdi = b.regValue .rbp ∧ c.regValue .rsi = b.regValue .r14 := ec.writes
  have c6 : c.regValue .rsi = stackPtr s-480 := wc.2.trans
    ((fb.read (n := 64) (r := 14) (by simp [outputComponents])).trans
      ((fa.read (n := 64) (r := 14) (by simp [outputComponents])).trans state.equationPointer))
  have c7 : c.regValue .rdi = stackPtr s-184 := wc.1.trans
    ((fb.read (n := 64) (r := 5) (by simp [outputComponents])).trans
      ((fa.read (n := 64) (r := 5) (by simp [outputComponents])).trans state.squarePointer))
  obtain ⟨n3,u,run3,su,ipu,result,ru,mu,_⟩ := Equality.compare_call pre sc ec.rip c6 c7
    (equation.of_bytes_eq (fun _ _ => congrArg (fun m : Ram => m[_]?) mc))
    (square.of_bytes_eq (fun _ _ => congrArg (fun m : Ram => m[_]?) mc))
  refine ⟨n0+n1+n2+n3,u,((run0.trans run1).trans run2).trans run3,
    ⟨su,ipu,?_,?_,?_,?_,?_,result⟩⟩
  · exact (ru .rbx (by simp)).trans ((fc.read (n := 64) (r := 3) (by simp)).trans
      ((fb.read (n := 64) (r := 3) (by simp [outputComponents])).trans
        ((fa.read (n := 64) (r := 3) (by simp [outputComponents])).trans state.output)))
  · exact (ru .r15 (by simp)).trans ((fc.read (n := 64) (r := 15) (by simp)).trans
      ((fb.read (n := 64) (r := 15) (by simp [outputComponents])).trans
        ((fa.read (n := 64) (r := 15) (by simp [outputComponents])).trans state.xValid)))
  · have byteU := mu 748 1 (by decide) (by decide) (by decide) 0 (by decide)
    have byteB := output_byte fb (offset := 748) (len := 1)
      (by unfold OffsetsApart; decide +kernel) (by decide) (i := 0) (by decide)
    have byteA := output_byte fa (offset := 748) (len := 1)
      (by unfold OffsetsApart; decide +kernel) (by decide) (i := 0) (by decide)
    simp only [BitVec.add_zero] at byteU byteB byteA
    exact byteU.trans ((congrArg (fun m : Ram => m[_]?) mc).trans
      (byteB.trans (byteA.trans state.yValid)))
  · exact xb.of_bytes_eq (fun i hi => (mu 248 32 (by decide) (by decide) (by decide) i hi).trans
      (congrArg (fun m : Ram => m[_]?) mc))
  · exact yb.of_bytes_eq (fun i hi => (mu 216 32 (by decide) (by decide) (by decide) i hi).trans
      (congrArg (fun m : Ram => m[_]?) mc))

end P256.Proofs.Sec1.Affine.Uncompressed.Curve
