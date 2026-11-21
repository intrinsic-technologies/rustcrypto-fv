import P256.Proofs.Sec1.Affine.Uncompressed.Curve.Preserve
import P256.Proofs.Sec1.Affine.Uncompressed.Curve.SquareXArguments
import P256.Proofs.Sec1.Affine.Uncompressed.Curve.CubeXArguments
import P256.Proofs.Sec1.Affine.Uncompressed.Curve.Sites
import P256.Proofs.Field.Montgomery

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Curve

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem cubeX_execute [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {x : Nat} (pre : AffineDecodePre s boundary bytes)
    (state : Frame s t) (rip : t.RIP = 0x110a46)
    (base : t.regValue .r13 = stackPtr s - 280) (hx : MontgomeryAt t (stackPtr s - 280) x) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x110aa8 ∧
      u.regValue .r12 = stackPtr s - 480 ∧ u.regValue .r13 = stackPtr s - 280 ∧
      MontgomeryAt u (stackPtr s - 480)
        (x*x%P256.Spec.Operations.domain.p*x%P256.Spec.Operations.domain.p) ∧
      PreservesInputs s t u ∧ u.regValue .rbp = t.regValue .rbp ∧
      (∀ i < 32, u.external[stackPtr s-184+BitVec.ofNat 64 i]? =
        t.external[stackPtr s-184+BitVec.ofNat 64 i]?) := by
  obtain ⟨n0, a, run0, sa, ea⟩ := copyX_execute pre state rip
  have pa := PreservesInputs.of_copyX state ea
  have original : MontgomeryAt t (stackPtr t + 480) x := by
    have addr : stackPtr t+480 = stackPtr s-280 :=
      ScalarFrame.scalar_stack_address (frameOffset := 760) (offset := 480) state.rsp (by decide) (by decide)
    rw [addr]
    exact hx
  have allocated : MemReadable a (stackPtr t+16) 32 := by
    have hr := ScalarFrame.stack_readable (frameOffset := 760) pre.toCalleePre sa
      (offset := 16) (len := 32) (by decide) (by decide)
    simpa only [sa.rsp, state.rsp, BitVec.ofNat_eq_ofNat] using hr
  have copied := copyX_value original ea allocated
  have copyAddress : stackPtr t+16 = stackPtr s-744 :=
    ScalarFrame.scalar_stack_address (frameOffset := 760) (offset := 16) state.rsp (by decide) (by decide)
  rw [copyAddress] at copied
  obtain ⟨n1, b, run1, rb, _, eb⟩ := squareXArguments_correct boundary pre.outerBoundary a
    (readyToStep sa.machine sa.bindingsSupported)
    (programText_slice (programLoaded_codeIn sa.loaded) 0x10a7a squareXArgumentsBytes
      (by decide +kernel) (by decide +kernel)) ea.rip
  have gb : AgreesExcept [.reg 14, .reg 6, .reg 7, .reg 2, .rip] a b := eb.agrees
  have mb := gb.external (by simp [Component.Covers])
  have sb := sa.after_registers rb gb (by simp [Component.Covers]) (by simp)
  have pb : PreservesInputs s a b := PreservesInputs.of_registers gb
    (by simp [Component.Covers]) (by simp) (by simp)
  have left : MontgomeryAt b (stackPtr s-744) x :=
    copied.of_bytes_eq (fun i _ => congrArg (fun m : Ram => m[_]?) mb)
  have right := pb.montgomery (by simp [preservedWindows]) (pa.montgomery (by simp [preservedWindows]) hx)
  have wb : b.regValue .r14 = stackPtr a+376 ∧ b.regValue .rsi = stackPtr a+16 ∧
      b.regValue .rdi = stackPtr a+376 ∧ b.regValue .rdx = a.regValue .r13 := eb.writes
  have addr16 : stackPtr a+16 = stackPtr s-744 :=
    ScalarFrame.scalar_stack_address (frameOffset := 760) sa.rsp (by decide) (by decide)
  have addr376 : stackPtr a+376 = stackPtr s-384 :=
    ScalarFrame.scalar_stack_address (frameOffset := 760) sa.rsp (by decide) (by decide)
  have a13 : a.regValue .r13 = stackPtr s-280 :=
    (ea.agrees.read (n := 64) (r := 13) (by simp [copyXEffect, Effect.components])).trans base
  obtain ⟨n2, c, run2, sc, ipc, xc, ac, bc, _⟩ :=
    FieldCall.binary_call pre.toCalleePre sb squareXSite
      (op := fun x y => x*y%P256.Spec.Operations.domain.p)
      (fun _ hp hx hy => field_mul_correct hp hx hy) eb.rip
      (wb.2.1.trans addr16) (wb.2.2.2.trans a13) (wb.2.2.1.trans addr376) left right
  have pc : PreservesInputs s b c := PreservesInputs.of_call (outputOffset := 384) (by simp) ac bc
  have c14 : c.regValue .r14 = stackPtr s-384 := (ac .r14 (by simp)).trans (wb.1.trans addr376)
  have c13 : c.regValue .r13 = stackPtr s-280 :=
    (ac .r13 (by simp)).trans ((gb.read (n := 64) (r := 13) (by simp)).trans a13)
  obtain ⟨n3, d, run3, rd, _, ed⟩ := cubeXArguments_correct boundary pre.outerBoundary c
    (readyToStep sc.machine sc.bindingsSupported)
    (programText_slice (programLoaded_codeIn sc.loaded) 0x10a92 cubeXArgumentsBytes
      (by decide +kernel) (by decide +kernel)) ipc
  have gd : AgreesExcept [.reg 12, .reg 7, .reg 6, .reg 2, .rip] c d := ed.agrees
  have md := gd.external (by simp [Component.Covers])
  have sd := sc.after_registers rd gd (by simp [Component.Covers]) (by simp)
  have pd : PreservesInputs s c d := PreservesInputs.of_registers gd
    (by simp [Component.Covers]) (by simp) (by simp)
  have xd : MontgomeryAt d (stackPtr s-384) (x*x%P256.Spec.Operations.domain.p) :=
    xc.of_bytes_eq (fun i _ => congrArg (fun m : Ram => m[_]?) md)
  have yd := pd.montgomery (by simp [preservedWindows]) (pc.montgomery (by simp [preservedWindows]) right)
  have wd : d.regValue .r12 = stackPtr c+280 ∧ d.regValue .rdi = stackPtr c+280 ∧
      d.regValue .rsi = c.regValue .r14 ∧ d.regValue .rdx = c.regValue .r13 := ed.writes
  have addr280 : stackPtr c+280 = stackPtr s-480 :=
    ScalarFrame.scalar_stack_address (frameOffset := 760) sc.rsp (by decide) (by decide)
  obtain ⟨n4, u, run4, su, ipu, xu, au, bu, _⟩ :=
    FieldCall.binary_call pre.toCalleePre sd cubeXSite
      (op := fun x y => x*y%P256.Spec.Operations.domain.p)
      (fun _ hp hx hy => field_mul_correct hp hx hy) ed.rip
      (wd.2.2.1.trans c14) (wd.2.2.2.trans c13) (wd.2.1.trans addr280) xd yd
  have pu : PreservesInputs s d u := PreservesInputs.of_call (outputOffset := 480) (by simp) au bu
  refine ⟨n0+n1+n2+n3+n4, u, (((run0.trans run1).trans run2).trans run3).trans run4,
    su, ipu, (au .r12 (by simp)).trans (wd.1.trans addr280),
    (au .r13 (by simp)).trans ((gd.read (n := 64) (r := 13) (by simp)).trans c13), xu,
    (((pa.trans pb).trans pc).trans pd).trans pu, ?_, ?_⟩
  · exact (au .rbp (by simp)).trans ((gd.read (n := 64) (r := 5) (by simp)).trans
      ((ac .rbp (by simp)).trans ((gb.read (n := 64) (r := 5) (by simp)).trans
        (ea.agrees.read (n := 64) (r := 5) (by simp [copyXEffect, Effect.components])))))
  · intro i hi
    have byteU : u.external[stackPtr s-184+BitVec.ofNat 64 i]? =
        d.external[stackPtr s-184+BitVec.ofNat 64 i]? :=
      bu 184 32 (by decide) (by decide) (by decide) i hi
    have byteC : c.external[stackPtr s-184+BitVec.ofNat 64 i]? =
        b.external[stackPtr s-184+BitVec.ofNat 64 i]? :=
      bc 184 32 (by decide) (by decide) (by decide) i hi
    rw [byteU, md, byteC, mb]
    have addr : stackPtr t+576 = stackPtr s-184 :=
      ScalarFrame.scalar_stack_address (frameOffset := 760) (offset := 576) state.rsp (by decide) (by decide)
    have byteA : a.external[stackPtr t+576+BitVec.ofNat 64 i]? =
        t.external[stackPtr t+576+BitVec.ofNat 64 i]? :=
      copyX_bytes ea (offset := 576) (len := 32) (by decide) (by decide) hi
    rw [addr] at byteA
    exact byteA

end P256.Proofs.Sec1.Affine.Uncompressed.Curve
