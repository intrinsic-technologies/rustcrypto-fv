import P256.Proofs.Projective.Add.Products.Copy
import P256.Proofs.Projective.Add.Products.Registers
import P256.Proofs.Projective.Add.Call.Sites
import P256.Proofs.Projective.Add.Values
import P256.Proofs.Field.Montgomery
import P256.Proofs.Projective.Add.Products.ZLeft
import P256.Proofs.Projective.Add.Products.ZRight
set_option autoImplicit false
namespace P256.Proofs.Projective.Add
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Products
theorem z_product [Bindings] {s t8 : RamState} {boundary : ReturnBoundary}
    {left right : Projective} (pre : CalleePre s boundary 0x1051f0 96 96 920)
    (st8 : FrameState s t8 96 920 632) (ip8 : t8.RIP = 0x1052c0)
    (lp8 : ProjectiveAt t8 (s.regValue .rdi) left)
    (rp8 : ProjectiveAt t8 (s.regValue .rsi) right)
    (bx8 : t8.regValue .rbx = s.regValue .rdi) (r148 : t8.regValue .r14 = s.regValue .rsi)
    (xx8 : MontgomeryAt t8 (stackPtr s - 560) (values left right).xx)
    (yy8 : MontgomeryAt t8 (stackPtr s - 464) (values left right).yy) :
    ∃ fuel t, Advances boundary fuel t8 t ∧ FrameState s t 96 920 632 ∧
      t.RIP = 0x10531f ∧ ProductsAt s t left right := by
  obtain ⟨n9, t9, run9, st9, ip9, value9, ag9⟩ :=
    copy_coordinate pre st8 (ZLeft.copy boundary pre.outerBoundary)
      (entryOffset := 0x52c0) (offset := 40) (coordinate := 64)
      (by decide) (by decide +kernel) (by decide) .rdi (by simp) (by decide)
      ip8 (by change t8.regValue .rbx + BitVec.ofNat 64 64 = _; rw [bx8]) rfl
      (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using lp8.2.2)
  have dst9 : ZLeft.destination t8 = stackPtr s - 592 :=
    scalar_stack_address (frameOffset := 632) st8.rsp (by decide) (offset := 40) (by decide)
  have mem9 := Copy.stack_frame pre ag9 dst9 (by decide) (by decide)
  have lp9 := Copy.point_of_stack pre .rdi (Or.inl rfl) mem9 lp8
  have rp9 := Copy.point_of_stack pre .rsi (Or.inr rfl) mem9 rp8
  have bx9 : t9.regValue .rbx = s.regValue .rdi :=
    (ag9.read (n := 64) (r := 3) (by simp [Copy32.components])).trans bx8
  have r149 : t9.regValue .r14 = s.regValue .rsi :=
    (ag9.read (n := 64) (r := 14) (by simp [Copy32.components])).trans r148
  have xx9 := Copy.stack_preserves ag9 dst9
    (inputOffset := 560) (by unfold OffsetsApart; decide +kernel) xx8
  have yy9 := Copy.stack_preserves ag9 dst9
    (inputOffset := 464) (by unfold OffsetsApart; decide +kernel) yy8
  obtain ⟨n10, t10, run10, st10, ip10, value10, ag10⟩ :=
    copy_coordinate pre st9 (ZRight.copy boundary pre.outerBoundary)
      (entryOffset := 0x52e4) (offset := 8) (coordinate := 64)
      (by decide) (by decide +kernel) (by decide) .rsi (by simp) (by decide)
      ip9 (by change t9.regValue .r14 + BitVec.ofNat 64 64 = _; rw [r149]) rfl
      (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using rp9.2.2)
  have dst10 : ZRight.destination t9 = stackPtr s - 624 :=
    scalar_stack_address (frameOffset := 632) st9.rsp (by decide) (offset := 8) (by decide)
  have mem10 := Copy.stack_frame pre ag10 dst10 (by decide) (by decide)
  have lp10 := Copy.point_of_stack pre .rdi (Or.inl rfl) mem10 lp9
  have rp10 := Copy.point_of_stack pre .rsi (Or.inr rfl) mem10 rp9
  have bx10 : t10.regValue .rbx = s.regValue .rdi :=
    (ag10.read (n := 64) (r := 3) (by simp [Copy32.components])).trans bx9
  have r1410 : t10.regValue .r14 = s.regValue .rsi :=
    (ag10.read (n := 64) (r := 14) (by simp [Copy32.components])).trans r149
  have xx10 := Copy.stack_preserves ag10 dst10
    (inputOffset := 560) (by unfold OffsetsApart; decide +kernel) xx9
  have yy10 := Copy.stack_preserves ag10 dst10
    (inputOffset := 464) (by unfold OffsetsApart; decide +kernel) yy9
  have left10 := Copy.stack_preserves ag10 dst10
    (inputOffset := 592) (by unfold OffsetsApart; decide +kernel) value9
  obtain ⟨n11, t11, run11, ready11, _, e11⟩ := zz_registers boundary pre.outerBoundary t10
    (readyToStep st10.machine st10.bindingsSupported)
    (programText_slice (programLoaded_codeIn st10.loaded) 0x5308 zzRegisterBytes
      (by decide) (by decide +kernel)) ip10
  have st11 := st10.after_registers ready11 e11.agrees
    (by simp [zzRegisterEffect, Effect.components, Component.Covers])
    (by simp [zzRegisterEffect, Effect.components])
  have ext11 : t11.external = t10.external := e11.agrees.external
    (by simp [zzRegisterEffect, Effect.components, Component.Covers])
  have bx11 : t11.regValue .rbx = s.regValue .rdi :=
    (e11.agrees.read (n := 64) (r := 3) (by simp [zzRegisterEffect, Effect.components])).trans bx10
  have r1411 : t11.regValue .r14 = s.regValue .rsi :=
    (e11.agrees.read (n := 64) (r := 14) (by simp [zzRegisterEffect, Effect.components])).trans r1410
  have lp11 : ProjectiveAt t11 (s.regValue .rdi) left := by simpa only [ProjectiveAt, MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, ext11] using lp10
  have rp11 : ProjectiveAt t11 (s.regValue .rsi) right := by simpa only [ProjectiveAt, MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, ext11] using rp10
  have left11 : MontgomeryAt t11 (stackPtr s - 592) left.z := by
    simpa only [values, MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, BitVec.ofNat_eq_ofNat, Nat.reduceSub, ext11] using left10
  have right11 : MontgomeryAt t11 (stackPtr s - 624) right.z := by
    simpa only [values, MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, BitVec.ofNat_eq_ofNat, Nat.reduceSub, ext11] using value10
  have regs11 := e11.writes
  simp only [zzRegisterEffect, Write.AllHold] at regs11
  have vin11 : t11.regValue .rsi = stackPtr s - 592 :=
    regs11.2.1.trans (scalar_stack_address (frameOffset := 632) st10.rsp (by decide) (offset := 40) (by decide))
  have vr11 : t11.regValue .rdx = stackPtr s - 624 :=
    regs11.2.2.1.trans (scalar_stack_address (frameOffset := 632) st10.rsp (by decide) (offset := 8) (by decide))
  have vout11 : t11.regValue .rdi = stackPtr s - 528 :=
    regs11.2.2.2.trans (scalar_stack_address (frameOffset := 632) st10.rsp (by decide) (offset := 104) (by decide))
  obtain ⟨n12, t12, run12, st12, ip12, zz12, regs12, bytes12, work12⟩ :=
    Call.binary_call pre st11 Call.Sites.call_102fca (x := left.z) (y := right.z)
      (op := fun x y => x * y % P256.Spec.Operations.domain.p) (fun _ hp hx hy => field_mul_correct hp hx hy)
      e11.rip vin11 vr11 vout11 left11 right11
  have lp12 := Copy.point_of_stack pre .rdi (Or.inl rfl) (Copy.work_stack_frame pre work12) lp11
  have rp12 := Copy.point_of_stack pre .rsi (Or.inr rfl) (Copy.work_stack_frame pre work12) rp11
  have bx12 := (regs12 .rbx (by simp)).trans bx11
  have r1412 := (regs12 .r14 (by simp)).trans r1411
  have xx11 : MontgomeryAt t11 (stackPtr s - 560) (values left right).xx := by
    simpa only [values, MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, BitVec.ofNat_eq_ofNat, Nat.reduceSub, ext11] using xx10
  have xx12 : MontgomeryAt t12 (stackPtr s - 560) (values left right).xx :=
    xx11.of_bytes_eq (fun i hi => (bytes12 560 32 (by decide) (by decide) (by decide) i hi))
  have yy11 : MontgomeryAt t11 (stackPtr s - 464) (values left right).yy := by
    simpa only [values, MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, BitVec.ofNat_eq_ofNat, Nat.reduceSub, ext11] using yy10
  have yy12 : MontgomeryAt t12 (stackPtr s - 464) (values left right).yy :=
    yy11.of_bytes_eq (fun i hi => (bytes12 464 32 (by decide) (by decide) (by decide) i hi))
  have rbp12 : t12.regValue .rbp = stackPtr s - 528 :=
    (regs12 .rbp (by simp)).trans (regs11.1.trans
      (scalar_stack_address (frameOffset := 632) st10.rsp (by decide) (offset := 104) (by decide)))
  exact ⟨_, t12, ((run9.trans run10).trans run11).trans run12,
    st12, ip12, lp12, rp12, bx12, r1412, rbp12, xx12, yy12, zz12⟩
end P256.Proofs.Projective.Add
