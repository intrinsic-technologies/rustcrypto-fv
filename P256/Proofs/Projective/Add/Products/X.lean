import P256.Proofs.Projective.Add.Products.Copy
import P256.Proofs.Projective.Add.Products.Registers
import P256.Proofs.Projective.Add.Call.Sites
import P256.Proofs.Projective.Add.Values
import P256.Proofs.Field.Montgomery
import P256.Proofs.Projective.Add.Products.XLeft
import P256.Proofs.Projective.Add.Products.XRight
set_option autoImplicit false
namespace P256.Proofs.Projective.Add
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Products
theorem x_product [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {left right : Projective} (pre : CalleePre s boundary 0x1051f0 96 96 920)
    (hleft : ProjectiveAt s (s.regValue .rdi) left)
    (hright : ProjectiveAt s (s.regValue .rsi) right) :
    ∃ fuel t, Advances boundary fuel s t ∧ FrameState s t 96 920 632 ∧
      t.RIP = 0x105261 ∧ ProjectiveAt t (s.regValue .rdi) left ∧
      ProjectiveAt t (s.regValue .rsi) right ∧ t.regValue .rbx = s.regValue .rdi ∧
      t.regValue .r14 = s.regValue .rsi ∧
      MontgomeryAt t (stackPtr s - 560) (values left right).xx := by
  obtain ⟨t0, entry⟩ := entry_correct pre
  obtain ⟨n0, run0⟩ := entry.execution
  have st0 := entry.toFrameState
  obtain ⟨lp0, rp0⟩ := entry.preserves_points pre hleft hright
  have bx0 := entry.left
  have r140 := entry.right
  have di0 : t0.regValue .rdi = s.regValue .rdi :=
    entry.agrees.read (n := 64) (r := 7) (by simp [saveFrame])
  have si0 : t0.regValue .rsi = s.regValue .rsi :=
    entry.agrees.read (n := 64) (r := 6) (by simp [saveFrame])
  have ip0 := entry.rip
  obtain ⟨n1, t1, run1, st1, ip1, value1, ag1⟩ :=
    copy_coordinate pre st0 (XLeft.copy boundary pre.outerBoundary)
      (entryOffset := 0x5207) (offset := 40) (coordinate := 0)
      (by decide) (by decide +kernel) (by decide) .rdi (by simp) (by decide)
      ip0 (by change t0.regValue .rdi + BitVec.ofNat 64 0 = _; rw [di0]) rfl
      (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using lp0.1)
  have dst1 : XLeft.destination t0 = stackPtr s - 592 :=
    scalar_stack_address (frameOffset := 632) st0.rsp (by decide) (offset := 40) (by decide)
  have mem1 := Copy.stack_frame pre ag1 dst1 (by decide) (by decide)
  have lp1 := Copy.point_of_stack pre .rdi (Or.inl rfl) mem1 lp0
  have rp1 := Copy.point_of_stack pre .rsi (Or.inr rfl) mem1 rp0
  have bx1 : t1.regValue .rbx = s.regValue .rdi :=
    (ag1.read (n := 64) (r := 3) (by simp [Copy32.components])).trans bx0
  have r141 : t1.regValue .r14 = s.regValue .rsi :=
    (ag1.read (n := 64) (r := 14) (by simp [Copy32.components])).trans r140
  have si1 : t1.regValue .rsi = s.regValue .rsi := (ag1.read (n := 64) (r := 6) (by simp [Copy32.components])).trans si0
  obtain ⟨n2, t2, run2, st2, ip2, value2, ag2⟩ :=
    copy_coordinate pre st1 (XRight.copy boundary pre.outerBoundary)
      (entryOffset := 0x522a) (offset := 8) (coordinate := 0)
      (by decide) (by decide +kernel) (by decide) .rsi (by simp) (by decide)
      ip1 (by change t1.regValue .rsi + BitVec.ofNat 64 0 = _; rw [si1]) rfl
      (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using rp1.1)
  have dst2 : XRight.destination t1 = stackPtr s - 624 :=
    scalar_stack_address (frameOffset := 632) st1.rsp (by decide) (offset := 8) (by decide)
  have mem2 := Copy.stack_frame pre ag2 dst2 (by decide) (by decide)
  have lp2 := Copy.point_of_stack pre .rdi (Or.inl rfl) mem2 lp1
  have rp2 := Copy.point_of_stack pre .rsi (Or.inr rfl) mem2 rp1
  have bx2 : t2.regValue .rbx = s.regValue .rdi :=
    (ag2.read (n := 64) (r := 3) (by simp [Copy32.components])).trans bx1
  have r142 : t2.regValue .r14 = s.regValue .rsi :=
    (ag2.read (n := 64) (r := 14) (by simp [Copy32.components])).trans r141
  have left2 := Copy.stack_preserves ag2 dst2
    (inputOffset := 592) (by unfold OffsetsApart; decide +kernel) value1
  obtain ⟨n3, t3, run3, ready3, _, e3⟩ := xx_registers boundary pre.outerBoundary t2
    (readyToStep st2.machine st2.bindingsSupported)
    (programText_slice (programLoaded_codeIn st2.loaded) 0x524d xxRegisterBytes
      (by decide) (by decide +kernel)) ip2
  have st3 := st2.after_registers ready3 e3.agrees
    (by simp [xxRegisterEffect, Effect.components, Component.Covers])
    (by simp [xxRegisterEffect, Effect.components])
  have ext3 : t3.external = t2.external := e3.agrees.external
    (by simp [xxRegisterEffect, Effect.components, Component.Covers])
  have bx3 : t3.regValue .rbx = s.regValue .rdi :=
    (e3.agrees.read (n := 64) (r := 3) (by simp [xxRegisterEffect, Effect.components])).trans bx2
  have r143 : t3.regValue .r14 = s.regValue .rsi :=
    (e3.agrees.read (n := 64) (r := 14) (by simp [xxRegisterEffect, Effect.components])).trans r142
  have lp3 : ProjectiveAt t3 (s.regValue .rdi) left := by simpa only [ProjectiveAt, MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, ext3] using lp2
  have rp3 : ProjectiveAt t3 (s.regValue .rsi) right := by simpa only [ProjectiveAt, MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, ext3] using rp2
  have left3 : MontgomeryAt t3 (stackPtr s - 592) left.x := by
    simpa only [values, MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, BitVec.ofNat_eq_ofNat, Nat.reduceSub, ext3] using left2
  have right3 : MontgomeryAt t3 (stackPtr s - 624) right.x := by
    simpa only [values, MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, BitVec.ofNat_eq_ofNat, Nat.reduceSub, ext3] using value2
  have regs3 := e3.writes
  simp only [xxRegisterEffect, Write.AllHold] at regs3
  have vin3 : t3.regValue .rsi = stackPtr s - 592 :=
    regs3.2.1.trans (scalar_stack_address (frameOffset := 632) st2.rsp (by decide) (offset := 40) (by decide))
  have vr3 : t3.regValue .rdx = stackPtr s - 624 :=
    regs3.2.2.trans (scalar_stack_address (frameOffset := 632) st2.rsp (by decide) (offset := 8) (by decide))
  have vout3 : t3.regValue .rdi = stackPtr s - 560 :=
    regs3.1.trans (scalar_stack_address (frameOffset := 632) st2.rsp (by decide) (offset := 72) (by decide))
  obtain ⟨n4, t4, run4, st4, ip4, xx4, regs4, bytes4, work4⟩ :=
    Call.binary_call pre st3 Call.Sites.call_102f0c (x := left.x) (y := right.x)
      (op := fun x y => x * y % P256.Spec.Operations.domain.p) (fun _ hp hx hy => field_mul_correct hp hx hy)
      e3.rip vin3 vr3 vout3 left3 right3
  have lp4 := Copy.point_of_stack pre .rdi (Or.inl rfl) (Copy.work_stack_frame pre work4) lp3
  have rp4 := Copy.point_of_stack pre .rsi (Or.inr rfl) (Copy.work_stack_frame pre work4) rp3
  have bx4 := (regs4 .rbx (by simp)).trans bx3
  have r144 := (regs4 .r14 (by simp)).trans r143
  exact ⟨_, t4, (((run0.trans run1).trans run2).trans run3).trans run4,
    st4, ip4, lp4, rp4, bx4, r144, xx4⟩
end P256.Proofs.Projective.Add
