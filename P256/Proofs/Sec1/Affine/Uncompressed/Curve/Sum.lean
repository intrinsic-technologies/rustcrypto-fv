import P256.Proofs.Sec1.Affine.Uncompressed.Curve.Constants
import P256.Proofs.Sec1.Affine.Uncompressed.Curve.AddLinearArguments
import P256.Proofs.Sec1.Affine.Uncompressed.Curve.AddConstantArguments
import P256.Proofs.Sec1.Affine.Uncompressed.Curve.Sites
import P256.Proofs.Field.Add

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Curve

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem sum_execute [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {x y w : Nat} (pre : AffineDecodePre s boundary bytes)
    (state : Frame s t) (rip : t.RIP = 0x110af0)
    (cube : t.regValue .r12 = stackPtr s-480)
    (linear : t.regValue .r14 = stackPtr s-384)
    (hx : MontgomeryAt t (stackPtr s-480) x)
    (hy : MontgomeryAt t (stackPtr s-384) y)
    (hw : MontgomeryAt t (stackPtr s-184) w) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x110b5a ∧
      u.regValue .r14 = stackPtr s-480 ∧ u.regValue .rbp = t.regValue .rbp ∧
      MontgomeryAt u (stackPtr s-480)
        (((x+y)%P256.Spec.Operations.domain.p+P256.Spec.Operations.domain.b)%P256.Spec.Operations.domain.p) ∧
      MontgomeryAt u (stackPtr s-184) w ∧ PreservesInputs s t u := by
  obtain ⟨n0, a, run0, ra, _, ea⟩ := addLinearArguments_correct boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x10af0 addLinearArgumentsBytes
      (by decide +kernel) (by decide +kernel)) rip
  have fa : AgreesExcept [.reg 13,.reg 7,.reg 6,.reg 2,.rip] t a := ea.agrees
  have ma := fa.external (by simp [Component.Covers])
  have sa := state.after_registers ra fa (by simp [Component.Covers]) (by simp)
  have pa : PreservesInputs s t a := PreservesInputs.of_registers fa
    (by simp [Component.Covers]) (by simp) (by simp)
  have xa := hx.of_bytes_eq (fun _ _ => congrArg (fun m : Ram => m[_]?) ma)
  have ya := hy.of_bytes_eq (fun _ _ => congrArg (fun m : Ram => m[_]?) ma)
  have wa : a.regValue .r13 = stackPtr t+344 ∧ a.regValue .rdi = stackPtr t+344 ∧
      a.regValue .rsi = t.regValue .r12 ∧ a.regValue .rdx = t.regValue .r14 := ea.writes
  have addr344 : stackPtr t+344 = stackPtr s-416 :=
    ScalarFrame.scalar_stack_address (frameOffset := 760) state.rsp (by decide) (by decide)
  obtain ⟨n1, b, run1, sb, ipb, vb, rb, mb, _⟩ :=
    FieldCall.binary_call pre.toCalleePre sa addLinearSite
      (op := fun x y => (x+y)%P256.Spec.Operations.domain.p)
      (fun _ hp hx hy => field_add_correct hp hx hy) ea.rip
      (wa.2.2.1.trans cube) (wa.2.2.2.trans linear) (wa.2.1.trans addr344) xa ya
  have pb : PreservesInputs s a b := PreservesInputs.of_call (outputOffset := 416) (by simp) rb mb
  have wb : MontgomeryAt b (stackPtr s-184) w := hw.of_bytes_eq (fun i hi =>
    (mb 184 32 (by decide) (by decide) (by decide) i hi).trans
      (congrArg (fun m : Ram => m[_]?) ma))
  obtain ⟨n2, c, run2, sc, ipc, vc, fc⟩ := store_b_execute pre sb ipb
  have pc := PreservesInputs.of_scratch fc
  have xc := vb.of_bytes_eq (fun _ hi => scratch_byte fc (offset := 416) (len := 32)
    (by unfold OffsetsApart; decide +kernel) (by decide) hi)
  have wc := wb.of_bytes_eq (fun _ hi => scratch_byte fc (offset := 184) (len := 32)
    (by unfold OffsetsApart; decide +kernel) (by decide) hi)
  obtain ⟨n3, d, run3, rd, _, ed⟩ := addConstantArguments_correct boundary pre.outerBoundary c
    (readyToStep sc.machine sc.bindingsSupported)
    (programText_slice (programLoaded_codeIn sc.loaded) 0x10b42 addConstantArgumentsBytes
      (by decide +kernel) (by decide +kernel)) ipc
  have fd : AgreesExcept [.reg 14,.reg 2,.reg 7,.reg 6,.rip] c d := ed.agrees
  have md := fd.external (by simp [Component.Covers])
  have sd := sc.after_registers rd fd (by simp [Component.Covers]) (by simp)
  have pd : PreservesInputs s c d := PreservesInputs.of_registers fd
    (by simp [Component.Covers]) (by simp) (by simp)
  have xd := xc.of_bytes_eq (fun _ _ => congrArg (fun m : Ram => m[_]?) md)
  have yd := vc.of_bytes_eq (fun _ _ => congrArg (fun m : Ram => m[_]?) md)
  have wd : d.regValue .r14 = stackPtr c+280 ∧ d.regValue .rdx = stackPtr c+16 ∧
      d.regValue .rdi = stackPtr c+280 ∧ d.regValue .rsi = c.regValue .r13 := ed.writes
  have addr280 : stackPtr c+280 = stackPtr s-480 :=
    ScalarFrame.scalar_stack_address (frameOffset := 760) sc.rsp (by decide) (by decide)
  have addr16 : stackPtr c+16 = stackPtr s-744 :=
    ScalarFrame.scalar_stack_address (frameOffset := 760) sc.rsp (by decide) (by decide)
  have c13 : c.regValue .r13 = stackPtr s-416 :=
    (fc.read (n := 64) (r := 13) (by simp [scratchComponents])).trans
      ((rb .r13 (by simp)).trans (wa.1.trans addr344))
  obtain ⟨n4, u, run4, su, ipu, vu, ru, mu, _⟩ :=
    FieldCall.binary_call pre.toCalleePre sd addConstantSite
      (op := fun x y => (x+y)%P256.Spec.Operations.domain.p)
      (fun _ hp hx hy => field_add_correct hp hx hy) ed.rip
      (wd.2.2.2.trans c13) (wd.2.1.trans addr16) (wd.2.2.1.trans addr280) xd yd
  refine ⟨n0+n1+n2+n3+n4,u,(((run0.trans run1).trans run2).trans run3).trans run4,
    su,ipu,(ru .r14 (by simp)).trans (wd.1.trans addr280),?_,vu,?_,?_⟩
  · exact (ru .rbp (by simp)).trans ((fd.read (n := 64) (r := 5) (by simp)).trans
      ((fc.read (n := 64) (r := 5) (by simp [scratchComponents])).trans
        ((rb .rbp (by simp)).trans (fa.read (n := 64) (r := 5) (by simp)))))
  · apply wc.of_bytes_eq
    intro i hi
    exact (mu 184 32 (by decide) (by decide) (by decide) i hi).trans
      (congrArg (fun m : Ram => m[_]?) md)
  · exact (((pa.trans pb).trans pc).trans pd).trans
      (PreservesInputs.of_call (outputOffset := 480) (by simp) ru mu)

end P256.Proofs.Sec1.Affine.Uncompressed.Curve
