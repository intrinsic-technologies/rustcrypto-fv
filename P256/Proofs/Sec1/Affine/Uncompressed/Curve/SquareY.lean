import P256.Proofs.Sec1.Affine.Uncompressed.Curve.Preserve
import P256.Proofs.Sec1.Affine.Uncompressed.Curve.SquareYArguments
import P256.Proofs.Sec1.Affine.Uncompressed.Curve.Sites
import P256.Proofs.Field.Montgomery

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Curve

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure SquaredY [Bindings] (s t : RamState) (bytes : ByteArray) : Prop extends Frame s t where
  rip : t.RIP = 0x110a46
  xPointer : t.regValue .r13 = stackPtr s - 280
  squarePointer : t.regValue .rbp = stackPtr s - 184
  value : MontgomeryAt t (stackPtr s - 184)
    (canonical (yCoordinate bytes) * canonical (yCoordinate bytes) % P256.Spec.Operations.domain.p)

theorem squareY_execute [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} (pre : AffineDecodePre s boundary bytes) (state : Parsed s t bytes) :
    ∃ fuel u, Advances boundary fuel t u ∧ SquaredY s u bytes ∧ PreservesInputs s t u := by
  obtain ⟨n0, a, run0, sa, ea⟩ := copyY_execute pre state.toFrameState state.rip
  have pa := PreservesInputs.of_copyY state.toFrameState ea
  have y : MontgomeryAt t (stackPtr t + 448) (canonical (yCoordinate bytes)) := by
    have address : stackPtr t + 448 = stackPtr s - 312 :=
      ScalarFrame.scalar_stack_address (frameOffset := 760) (offset := 448) state.rsp (by decide) (by decide)
    rw [address]
    exact state.yValue
  have allocated : MemReadable a (stackPtr t + 16) 32 := by
    have hr := ScalarFrame.stack_readable (frameOffset := 760) pre.toCalleePre sa
      (offset := 16) (len := 32) (by decide) (by decide)
    simpa only [sa.rsp, state.rsp, BitVec.ofNat_eq_ofNat] using hr
  have copied := copyY_value y ea allocated
  have copyAddress : stackPtr t + 16 = stackPtr s - 744 :=
    ScalarFrame.scalar_stack_address (frameOffset := 760) (offset := 16) state.rsp (by decide) (by decide)
  rw [copyAddress] at copied
  obtain ⟨n1, b, run1, readyb, _, eb⟩ := squareYArguments_correct boundary pre.outerBoundary a
    (readyToStep sa.machine sa.bindingsSupported)
    (programText_slice (programLoaded_codeIn sa.loaded) 0x10a2e squareYArgumentsBytes
      (by decide +kernel) (by decide +kernel)) ea.rip
  have gb : AgreesExcept [.reg 5, .reg 6, .reg 7, .reg 2, .rip] a b := eb.agrees
  have mb := gb.external (by simp [Component.Covers])
  have sb := sa.after_registers readyb gb (by simp [Component.Covers]) (by simp)
  have pb : PreservesInputs s a b := PreservesInputs.of_registers gb
    (by simp [Component.Covers]) (by simp) (by simp)
  have left : MontgomeryAt b (stackPtr s - 744) (canonical (yCoordinate bytes)) :=
    copied.of_bytes_eq (fun i _ => congrArg (fun m : Ram => m[_]?) mb)
  have right := pb.montgomery (by simp [preservedWindows])
    (pa.montgomery (by simp [preservedWindows]) state.yValue)
  have wb : b.regValue .rbp = stackPtr a + 576 ∧ b.regValue .rsi = stackPtr a + 16 ∧
      b.regValue .rdi = stackPtr a + 576 ∧ b.regValue .rdx = a.regValue .r14 := eb.writes
  have addr16 : stackPtr a + 16 = stackPtr s - 744 :=
    ScalarFrame.scalar_stack_address (frameOffset := 760) sa.rsp (by decide) (by decide)
  have addr576 : stackPtr a + 576 = stackPtr s - 184 :=
    ScalarFrame.scalar_stack_address (frameOffset := 760) sa.rsp (by decide) (by decide)
  have a14 : a.regValue .r14 = stackPtr s - 312 :=
    (ea.agrees.read (n := 64) (r := 14) (by simp [copyYEffect, Effect.components])).trans state.yPointer
  obtain ⟨n2, u, run2, su, ipu, value, regs, mem, _⟩ :=
    FieldCall.binary_call pre.toCalleePre sb squareYSite
      (op := fun x y => x*y%P256.Spec.Operations.domain.p)
      (fun _ hp hx hy => field_mul_correct hp hx hy) eb.rip
      (wb.2.1.trans addr16) (wb.2.2.2.trans a14) (wb.2.2.1.trans addr576) left right
  have pu : PreservesInputs s b u := PreservesInputs.of_call (outputOffset := 184)
    (by simp) regs mem
  refine ⟨n0+n1+n2, u, (run0.trans run1).trans run2,
    ⟨su, ipu, ?_, (regs .rbp (by simp)).trans (wb.1.trans addr576), value⟩,
    (pa.trans pb).trans pu⟩
  exact (regs .r13 (by simp)).trans ((gb.read (n := 64) (r := 13) (by simp)).trans
    ((ea.agrees.read (n := 64) (r := 13) (by simp [copyYEffect, Effect.components])).trans
      state.xPointer))

end P256.Proofs.Sec1.Affine.Uncompressed.Curve
