import P256.Proofs.Signing.Core.Iteration.Point.Normalize.Select
import P256.Proofs.Signing.Core.Iteration.Point.Normalize.Copy.X
import P256.Proofs.Signing.Core.Iteration.Point.Normalize.Copy.Memory
import P256.Proofs.Signing.Core.Iteration.Point.Normalize.Blocks.B1012d7
import P256.Proofs.Field.Montgomery

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point.Normalize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open Standards.SECG.ECC P256.Spec.Operations
open NextNonce (scalarFrame coreFrame base_add)
open Projective.Multiply.Machine.Basepoint (register_block)
open Blocks

structure XProduct [Bindings] (s t : RamState) (point : Projective) : Prop where
  frame : Frame s t
  x : Field.MontgomeryAt t (frameBase s+1328) (point.x*Curve.inverse domain.p point.z % domain.p)
  y : Field.MontgomeryAt t (frameBase s+208) point.y
  inverse : Field.MontgomeryAt t (frameBase s+2128) (Curve.inverse domain.p point.z)
  flag : (t.regValue .r12).setWidth 8 = if point.z = 0 then 0 else 1
  rbp : t.regValue .rbp = frameBase s+2128
  r13 : t.regValue .r13 = frameBase s+432
  r15 : t.regValue .r15 = frameBase s+1328
  rbx : t.regValue .rbx = frameBase s+240
  r14 : t.regValue .r14 = frameBase s+8

set_option maxHeartbeats 600000 in
theorem x_product [Bindings] {s t : RamState} {boundary : ReturnBoundary} {point : Projective}
    (pre : SignPre s boundary) (state : Selected s t point) (rip : t.RIP = 0x10cfd8) :
    ∃ fuel u, Advances boundary fuel t u ∧ u.RIP = 0x10d01f ∧
      XProduct s u point ∧ Preserved s t u := by
  have src : Copy.X.source t = frameBase s+176 := congrArg (·+176) state.frame.rsp
  have dst : Copy.X.destination t = frameBase s+8 := congrArg (·+8) state.frame.rsp
  obtain ⟨n1,v,run1,f1,rip1,value1,ag1⟩ := Copy.execute pre state.frame
    (codeOffset := 0xcfd8) (sourceOffset := 176) (destinationOffset := 8)
    (Copy.X.copy boundary pre.outerBoundary) (by decide) (by decide +kernel) rip
    (by decide) (by decide) (.inr (by decide)) src dst (src.symm ▸ state.projective.1)
  rw [dst] at value1 ag1
  have y0 : Field.MontgomeryAt t (frameBase s+208) point.y := by
    rw [← (show frameBase s+176+32 = frameBase s+208 by rw [BitVec.add_assoc]; rfl)]
    exact state.projective.2.1
  have y1 := Copy.montgomery (offset := 8) ag1 (by decide) (by decide) (.inr (by decide)) y0
  have z1 := Copy.montgomery (offset := 8) ag1 (by decide) (by decide) (.inr (by decide)) state.inverse
  have keep1 := Copy.preserved (offset := 8) ag1 (by decide) (by intro i hi; rcases hi with h|h|h|h <;> omega)
  obtain ⟨n2,w,run2,sf2,ef2,mem2⟩ := register_block (offset := 0xd00c)
    (scalarFrame f1) (b1012d7_correct boundary pre.outerBoundary)
    (by decide +kernel) (by decide +kernel) rip1
    (by simp [b1012d7Effect,Effect.components,Component.Covers])
    (by simp [b1012d7Effect,Effect.components]) (by simp [b1012d7Effect,Effect.components])
    (by simp [b1012d7Effect,Effect.components]) (by simp [b1012d7Effect,Effect.components])
  have regs := ef2.writes
  simp only [b1012d7Effect,Write.AllHold] at regs
  have r15v : v.regValue .r15 = frameBase s+1328 :=
    (ag1.read (n := 64) (r := 15) (by simp [ScalarFrame.Copy32.components])).trans state.r15
  have si : w.regValue .rsi = frameBase s+8 := regs.2.2.1.trans (congrArg (·+8) f1.rsp)
  have dx : w.regValue .rdx = frameBase s+2128 := regs.2.2.2.trans ((ag1.read (n := 64) (r := 5) (by simp [ScalarFrame.Copy32.components])).trans state.rbp)
  have di : w.regValue .rdi = frameBase s+1328 := regs.1.trans r15v
  obtain ⟨n3,u,run3,sf3,rip3,value3,saved,bytes,_⟩ := FieldCall.binary_call
    (op := fun x y => x*y % domain.p) pre.toCalleePre sf2 xMultiplySite
    (fun _ hp hx hy => Field.field_mul_correct hp hx hy) ef2.rip
    (si.trans (base_add s (by decide))) (dx.trans (base_add s (by decide)))
    (di.trans (base_add s (by decide)))
    (by
      change Field.MontgomeryAt w (stackPtr s-2272) point.x
      rw [← (show frameBase s+8 = stackPtr s-2272 from base_add s (by decide))]
      exact value1.of_bytes_eq (by intros; simp only [mem2,BitVec.ofNat_eq_ofNat]))
    (by
      change Field.MontgomeryAt w (stackPtr s-152) (Curve.inverse domain.p point.z)
      rw [← (show frameBase s+2128 = stackPtr s-152 from base_add s (by decide))]
      exact z1.of_bytes_eq (by intros; simp only [mem2,BitVec.ofNat_eq_ofNat]))
  have kept := bytes_from_stack (s := s) (output := 1328) (lenOut := 32) (by decide) bytes
  have x3 : Field.MontgomeryAt u (frameBase s+1328)
      (point.x*Curve.inverse domain.p point.z % domain.p) := by
    rw [show frameBase s+1328 = stackPtr s-952 from base_add s (by decide)]
    exact value3
  refine ⟨n1+n2+n3,u,(run1.trans run2).trans run3,rip3,⟨coreFrame sf3,x3,?_,?_,?_,?_,?_,?_,?_,?_⟩,?_⟩
  · exact y1.of_bytes_eq (by intro i hi; exact (kept 208 32 (by decide) (.inl (by decide)) i hi).trans (by rw [mem2]))
  · exact z1.of_bytes_eq (by intro i hi; exact (kept 2128 32 (by decide) (.inr (by decide)) i hi).trans (by rw [mem2]))
  · have flag2 : w.regValue .r12 = t.regValue .r12 :=
      (ef2.agrees.read (n := 64) (r := 12) (by simp [b1012d7Effect,Effect.components])).trans
        (ag1.read (n := 64) (r := 12) (by simp [ScalarFrame.Copy32.components]))
    exact (congrArg (BitVec.setWidth 8) ((saved .r12 (by simp)).trans flag2)).trans state.flag
  · exact (saved .rbp (by simp)).trans ((ef2.agrees.read (n := 64) (r := 5)
      (by simp [b1012d7Effect,Effect.components])).trans
      ((ag1.read (n := 64) (r := 5) (by simp [ScalarFrame.Copy32.components])).trans state.rbp))
  · exact (saved .r13 (by simp)).trans ((ef2.agrees.read (n := 64) (r := 13)
      (by simp [b1012d7Effect,Effect.components])).trans
      ((ag1.read (n := 64) (r := 13) (by simp [ScalarFrame.Copy32.components])).trans state.r13))
  · exact (saved .r15 (by simp)).trans ((ef2.agrees.read (n := 64) (r := 15)
      (by simp [b1012d7Effect,Effect.components])).trans
      ((ag1.read (n := 64) (r := 15) (by simp [ScalarFrame.Copy32.components])).trans state.r15))
  · exact (saved .rbx (by simp)).trans ((ef2.agrees.read (n := 64) (r := 3)
      (by simp [b1012d7Effect,Effect.components])).trans
      ((ag1.read (n := 64) (r := 3) (by simp [ScalarFrame.Copy32.components])).trans state.rbx))
  · exact (saved .r14 (by simp)).trans (regs.2.1.trans (congrArg (·+8) f1.rsp))
  · intro i hi
    have h := kept i 1 (by rcases hi with h|h|h|h <;> omega)
      (by rcases hi with h|h|h|h <;> omega) 0 (by decide)
    simp only [BitVec.add_zero,mem2] at h
    exact h.trans (keep1 i hi)

end P256.Proofs.Signing.Core.Iteration.Point.Normalize
