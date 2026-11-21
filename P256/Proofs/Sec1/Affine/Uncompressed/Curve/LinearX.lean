import P256.Proofs.Sec1.Affine.Uncompressed.Curve.Constants
import P256.Proofs.Sec1.Affine.Uncompressed.Curve.LinearXArguments
import P256.Proofs.Sec1.Affine.Uncompressed.Curve.Sites
import P256.Proofs.Field.Montgomery

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Curve

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem linearX_execute [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {x z w : Nat} (pre : AffineDecodePre s boundary bytes)
    (state : Frame s t) (rip : t.RIP = 0x110aa8)
    (base : t.regValue .r13 = stackPtr s-280)
    (hx : MontgomeryAt t (stackPtr s-280) x)
    (hz : MontgomeryAt t (stackPtr s-480) z)
    (hw : MontgomeryAt t (stackPtr s-184) w) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x110af0 ∧
      u.regValue .r14 = stackPtr s-384 ∧
      MontgomeryAt u (stackPtr s-384) (P256.Spec.Operations.domain.a*x%P256.Spec.Operations.domain.p) ∧
      MontgomeryAt u (stackPtr s-480) z ∧ MontgomeryAt u (stackPtr s-184) w ∧
      PreservesInputs s t u ∧
      (∀ r ∈ [Syntax.Reg.rbp, .r12, .r13], u.regValue r = t.regValue r) := by
  obtain ⟨n0, a, run0, sa, ipa, xa, fa⟩ := store_a_execute pre state rip
  have pa := PreservesInputs.of_scratch fa
  have za : MontgomeryAt a (stackPtr s-480) z := hz.of_bytes_eq
    (fun _ hi => scratch_byte fa (offset := 480) (len := 32) (by unfold OffsetsApart; decide +kernel) (by decide) hi)
  have wa : MontgomeryAt a (stackPtr s-184) w := hw.of_bytes_eq
    (fun _ hi => scratch_byte fa (offset := 184) (len := 32) (by unfold OffsetsApart; decide +kernel) (by decide) hi)
  obtain ⟨n1, b, run1, rb, _, eb⟩ := linearXArguments_correct boundary pre.outerBoundary a
    (readyToStep sa.machine sa.bindingsSupported)
    (programText_slice (programLoaded_codeIn sa.loaded) 0x10ad8 linearXArgumentsBytes
      (by decide +kernel) (by decide +kernel)) ipa
  have fb : AgreesExcept [.reg 14, .reg 6, .reg 7, .reg 2, .rip] a b := eb.agrees
  have mb := fb.external (by simp [Component.Covers])
  have sb := sa.after_registers rb fb (by simp [Component.Covers]) (by simp)
  have pb : PreservesInputs s a b := PreservesInputs.of_registers fb
    (by simp [Component.Covers]) (by simp) (by simp)
  have xb := xa.of_bytes_eq (fun i _ => congrArg (fun m : Ram => m[_]?) mb)
  have yb := pb.montgomery (by simp [preservedWindows]) (pa.montgomery (by simp [preservedWindows]) hx)
  have wb : b.regValue .r14 = stackPtr a+376 ∧ b.regValue .rsi = stackPtr a+16 ∧
      b.regValue .rdi = stackPtr a+376 ∧ b.regValue .rdx = a.regValue .r13 := eb.writes
  have addr16 : stackPtr a+16 = stackPtr s-744 :=
    ScalarFrame.scalar_stack_address (frameOffset := 760) sa.rsp (by decide) (by decide)
  have addr376 : stackPtr a+376 = stackPtr s-384 :=
    ScalarFrame.scalar_stack_address (frameOffset := 760) sa.rsp (by decide) (by decide)
  have a13 : a.regValue .r13 = stackPtr s-280 :=
    (fa.read (n := 64) (r := 13) (by simp [scratchComponents])).trans base
  obtain ⟨n2, u, run2, su, ipu, value, regs, mem, _⟩ :=
    FieldCall.binary_call pre.toCalleePre sb linearXSite
      (op := fun x y => x*y%P256.Spec.Operations.domain.p)
      (fun _ hp hx hy => field_mul_correct hp hx hy) eb.rip
      (wb.2.1.trans addr16) (wb.2.2.2.trans a13) (wb.2.2.1.trans addr376) xb yb
  have pu : PreservesInputs s b u := PreservesInputs.of_call (outputOffset := 384) (by simp) regs mem
  refine ⟨n0+n1+n2, u, (run0.trans run1).trans run2, su, ipu,
    (regs .r14 (by simp)).trans (wb.1.trans addr376), value, ?_, ?_, (pa.trans pb).trans pu, ?_⟩
  · apply za.of_bytes_eq
    intro i hi
    exact (mem 480 32 (by decide) (by decide) (by decide) i hi).trans
      (congrArg (fun m : Ram => m[_]?) mb)
  · apply wa.of_bytes_eq
    intro i hi
    exact (mem 184 32 (by decide) (by decide) (by decide) i hi).trans
      (congrArg (fun m : Ram => m[_]?) mb)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (regs .rbp (by simp)).trans ((fb.read (n := 64) (r := 5) (by simp)).trans
        (fa.read (n := 64) (r := 5) (by simp [scratchComponents])))
    · exact (regs .r12 (by simp)).trans ((fb.read (n := 64) (r := 12) (by simp)).trans
        (fa.read (n := 64) (r := 12) (by simp [scratchComponents])))
    · exact (regs .r13 (by simp)).trans ((fb.read (n := 64) (r := 13) (by simp)).trans
        (fa.read (n := 64) (r := 13) (by simp [scratchComponents])))

end P256.Proofs.Sec1.Affine.Uncompressed.Curve
