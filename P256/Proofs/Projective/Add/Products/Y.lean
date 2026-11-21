import P256.Proofs.Projective.Add.Products.Copy
import P256.Proofs.Projective.Add.Products.Registers
import P256.Proofs.Projective.Add.Call.Sites
import P256.Proofs.Projective.Add.Values
import P256.Proofs.Field.Montgomery
import P256.Proofs.Projective.Add.Products.YLeft
import P256.Proofs.Projective.Add.Products.YRight
set_option autoImplicit false
namespace P256.Proofs.Projective.Add
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Products
theorem y_product [Bindings] {s t4 : RamState} {boundary : ReturnBoundary}
    {left right : Projective} (pre : CalleePre s boundary 0x1051f0 96 96 920)
    (st4 : FrameState s t4 96 920 632) (ip4 : t4.RIP = 0x105261)
    (lp4 : ProjectiveAt t4 (s.regValue .rdi) left)
    (rp4 : ProjectiveAt t4 (s.regValue .rsi) right)
    (bx4 : t4.regValue .rbx = s.regValue .rdi) (r144 : t4.regValue .r14 = s.regValue .rsi)
    (xx4 : MontgomeryAt t4 (stackPtr s - 560) (values left right).xx) :
    ∃ fuel t, Advances boundary fuel t4 t ∧ FrameState s t 96 920 632 ∧
      t.RIP = 0x1052c0 ∧ ProjectiveAt t (s.regValue .rdi) left ∧
      ProjectiveAt t (s.regValue .rsi) right ∧ t.regValue .rbx = s.regValue .rdi ∧
      t.regValue .r14 = s.regValue .rsi ∧
      MontgomeryAt t (stackPtr s - 560) (values left right).xx ∧
      MontgomeryAt t (stackPtr s - 464) (values left right).yy := by
  obtain ⟨n5, t5, run5, st5, ip5, value5, ag5⟩ :=
    copy_coordinate pre st4 (YLeft.copy boundary pre.outerBoundary)
      (entryOffset := 0x5261) (offset := 40) (coordinate := 32)
      (by decide) (by decide +kernel) (by decide) .rdi (by simp) (by decide)
      ip4 (by change t4.regValue .rbx + BitVec.ofNat 64 32 = _; rw [bx4]) rfl
      (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using lp4.2.1)
  have dst5 : YLeft.destination t4 = stackPtr s - 592 :=
    scalar_stack_address (frameOffset := 632) st4.rsp (by decide) (offset := 40) (by decide)
  have mem5 := Copy.stack_frame pre ag5 dst5 (by decide) (by decide)
  have lp5 := Copy.point_of_stack pre .rdi (Or.inl rfl) mem5 lp4
  have rp5 := Copy.point_of_stack pre .rsi (Or.inr rfl) mem5 rp4
  have bx5 : t5.regValue .rbx = s.regValue .rdi :=
    (ag5.read (n := 64) (r := 3) (by simp [Copy32.components])).trans bx4
  have r145 : t5.regValue .r14 = s.regValue .rsi :=
    (ag5.read (n := 64) (r := 14) (by simp [Copy32.components])).trans r144
  have xx5 := Copy.stack_preserves ag5 dst5
    (inputOffset := 560) (by unfold OffsetsApart; decide +kernel) xx4
  obtain ⟨n6, t6, run6, st6, ip6, value6, ag6⟩ :=
    copy_coordinate pre st5 (YRight.copy boundary pre.outerBoundary)
      (entryOffset := 0x5285) (offset := 8) (coordinate := 32)
      (by decide) (by decide +kernel) (by decide) .rsi (by simp) (by decide)
      ip5 (by change t5.regValue .r14 + BitVec.ofNat 64 32 = _; rw [r145]) rfl
      (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using rp5.2.1)
  have dst6 : YRight.destination t5 = stackPtr s - 624 :=
    scalar_stack_address (frameOffset := 632) st5.rsp (by decide) (offset := 8) (by decide)
  have mem6 := Copy.stack_frame pre ag6 dst6 (by decide) (by decide)
  have lp6 := Copy.point_of_stack pre .rdi (Or.inl rfl) mem6 lp5
  have rp6 := Copy.point_of_stack pre .rsi (Or.inr rfl) mem6 rp5
  have bx6 : t6.regValue .rbx = s.regValue .rdi :=
    (ag6.read (n := 64) (r := 3) (by simp [Copy32.components])).trans bx5
  have r146 : t6.regValue .r14 = s.regValue .rsi :=
    (ag6.read (n := 64) (r := 14) (by simp [Copy32.components])).trans r145
  have xx6 := Copy.stack_preserves ag6 dst6
    (inputOffset := 560) (by unfold OffsetsApart; decide +kernel) xx5
  have left6 := Copy.stack_preserves ag6 dst6
    (inputOffset := 592) (by unfold OffsetsApart; decide +kernel) value5
  obtain ⟨n7, t7, run7, ready7, _, e7⟩ := yy_registers boundary pre.outerBoundary t6
    (readyToStep st6.machine st6.bindingsSupported)
    (programText_slice (programLoaded_codeIn st6.loaded) 0x52a9 yyRegisterBytes
      (by decide) (by decide +kernel)) ip6
  have st7 := st6.after_registers ready7 e7.agrees
    (by simp [yyRegisterEffect, Effect.components, Component.Covers])
    (by simp [yyRegisterEffect, Effect.components])
  have ext7 : t7.external = t6.external := e7.agrees.external
    (by simp [yyRegisterEffect, Effect.components, Component.Covers])
  have bx7 : t7.regValue .rbx = s.regValue .rdi :=
    (e7.agrees.read (n := 64) (r := 3) (by simp [yyRegisterEffect, Effect.components])).trans bx6
  have r147 : t7.regValue .r14 = s.regValue .rsi :=
    (e7.agrees.read (n := 64) (r := 14) (by simp [yyRegisterEffect, Effect.components])).trans r146
  have lp7 : ProjectiveAt t7 (s.regValue .rdi) left := by simpa only [ProjectiveAt, MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, ext7] using lp6
  have rp7 : ProjectiveAt t7 (s.regValue .rsi) right := by simpa only [ProjectiveAt, MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, ext7] using rp6
  have left7 : MontgomeryAt t7 (stackPtr s - 592) left.y := by
    simpa only [values, MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, BitVec.ofNat_eq_ofNat, Nat.reduceSub, ext7] using left6
  have right7 : MontgomeryAt t7 (stackPtr s - 624) right.y := by
    simpa only [values, MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, BitVec.ofNat_eq_ofNat, Nat.reduceSub, ext7] using value6
  have regs7 := e7.writes
  simp only [yyRegisterEffect, Write.AllHold] at regs7
  have vin7 : t7.regValue .rsi = stackPtr s - 592 :=
    regs7.2.1.trans (scalar_stack_address (frameOffset := 632) st6.rsp (by decide) (offset := 40) (by decide))
  have vr7 : t7.regValue .rdx = stackPtr s - 624 :=
    regs7.2.2.trans (scalar_stack_address (frameOffset := 632) st6.rsp (by decide) (offset := 8) (by decide))
  have vout7 : t7.regValue .rdi = stackPtr s - 464 :=
    regs7.1.trans (scalar_stack_address (frameOffset := 632) st6.rsp (by decide) (offset := 168) (by decide))
  obtain ⟨n8, t8, run8, st8, ip8, yy8, regs8, bytes8, work8⟩ :=
    Call.binary_call pre st7 Call.Sites.call_102f6b (x := left.y) (y := right.y)
      (op := fun x y => x * y % P256.Spec.Operations.domain.p) (fun _ hp hx hy => field_mul_correct hp hx hy)
      e7.rip vin7 vr7 vout7 left7 right7
  have lp8 := Copy.point_of_stack pre .rdi (Or.inl rfl) (Copy.work_stack_frame pre work8) lp7
  have rp8 := Copy.point_of_stack pre .rsi (Or.inr rfl) (Copy.work_stack_frame pre work8) rp7
  have bx8 := (regs8 .rbx (by simp)).trans bx7
  have r148 := (regs8 .r14 (by simp)).trans r147
  have xx7 : MontgomeryAt t7 (stackPtr s - 560) (values left right).xx := by
    simpa only [values, MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, BitVec.ofNat_eq_ofNat, Nat.reduceSub, ext7] using xx6
  have xx8 : MontgomeryAt t8 (stackPtr s - 560) (values left right).xx :=
    xx7.of_bytes_eq (fun i hi => (bytes8 560 32 (by decide) (by decide) (by decide) i hi))
  exact ⟨_, t8, ((run5.trans run6).trans run7).trans run8,
    st8, ip8, lp8, rp8, bx8, r148, xx8, yy8⟩
end P256.Proofs.Projective.Add
