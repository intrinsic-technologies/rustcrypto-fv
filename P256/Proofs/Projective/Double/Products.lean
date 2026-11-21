import P256.Proofs.Projective.Double.Products.Run
import P256.Proofs.Projective.Double.Products.Sites
import P256.Proofs.Field.Montgomery
import P256.Proofs.Field.Add
import P256.Proofs.Field.Subtract
set_option autoImplicit false

namespace P256.Proofs.Projective.Double

variable {inputRegister : X86.Syntax.Reg}

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Program.FieldCall
open P256.Proofs.Field X86 X86.Machine X86.UserProcess X86Proofs

open Products in
theorem products_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {point : Projective} (pre : CalleePre s boundary 0x105d80 0 96 1016 inputRegister)
    (state : FrameState s t 96 1016 728) (rip : t.RIP = 0x105fd1)
    (input : CrossTermsAt s t point) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 96 1016 728 ∧
      u.RIP = 0x1060fe ∧ ProductsAt s u point := by
  obtain ⟨na, a, ra, fa, ea, ma, ka⟩ := subtraction_run pre state rip
  have a12 : a.regValue .r12 = stackPtr s - 400 := by
    have h : a.regValue .r12 = stackPtr t + 328 := ea.writes.2.2.1
    exact h.trans (scalar_stack_address (frameOffset := 728) state.rsp (by decide) (offset := 328) (by decide))
  have a6 : a.regValue .rsi = stackPtr s - 688 := by
    have h : a.regValue .rsi = stackPtr t + 40 := ea.writes.2.2.2.1
    exact h.trans (scalar_stack_address (frameOffset := 728) state.rsp (by decide) (offset := 40) (by decide))
  have a2 : a.regValue .rdx = stackPtr s - 720 := by
    have h : a.regValue .rdx = stackPtr t + 8 := ea.writes.2.2.2.2.1
    exact h.trans (scalar_stack_address (frameOffset := 728) state.rsp (by decide) (offset := 8) (by decide))
  have a7 : a.regValue .rdi = stackPtr s - 400 := by
    have h : a.regValue .rdi = stackPtr t + 328 := ea.writes.2.2.2.2.2.1
    exact h.trans (scalar_stack_address (frameOffset := 728) state.rsp (by decide) (offset := 328) (by decide))
  obtain ⟨nb, b, rb, fb, pb, minus, ab, mb, wb⟩ := binary_call (x := (values point).yy) (y := (values point).bzz3)
    (op := Standards.SECG.ECC.Curve.fieldSub P256.Spec.Operations.domain.p) pre fa subtractionSite
    (fun _ hp hx hy => by simpa only [Standards.SECG.ECC.Curve.fieldSub, Nat.mod_eq_of_lt hx.1, Nat.mod_eq_of_lt hy.1] using field_subtract_correct hp hx hy) ea.rip a6 a2 a7
    (subtraction_copy_40 pre state ea input.yy) (subtraction_copy_8 pre state ea input.bzz3)
  have b15 : b.regValue .r15 = stackPtr s - 432 :=
    (ab .r15 (by simp)).trans ((ea.agrees.read (n := 64) (r := 15)
      (by simp [subtractionEffect, Effect.components])).trans input.r15)
  have b12 : b.regValue .r12 = stackPtr s - 400 := (ab .r12 (by simp)).trans a12
  have byy := call_keep mb (offset := 592) (by decide) (by decide) (by decide)
    (ka _ _ (by decide) (by decide) input.yy)
  obtain ⟨nc, c, rc, fc, ec, mc, kc⟩ := addition_run pre fb pb
  have c13 : c.regValue .r13 = stackPtr s - 144 := by
    have h : c.regValue .r13 = stackPtr b + 584 := ec.writes.2.2.1
    exact h.trans (scalar_stack_address (frameOffset := 728) fb.rsp (by decide) (offset := 584) (by decide))
  have c6 : c.regValue .rsi = stackPtr s - 720 := by
    have h : c.regValue .rsi = stackPtr b + 8 := ec.writes.2.2.2.1
    exact h.trans (scalar_stack_address (frameOffset := 728) fb.rsp (by decide) (offset := 8) (by decide))
  have c7 : c.regValue .rdi = stackPtr s - 144 := by
    have h : c.regValue .rdi = stackPtr b + 584 := ec.writes.2.2.2.2.1
    exact h.trans (scalar_stack_address (frameOffset := 728) fb.rsp (by decide) (offset := 584) (by decide))
  have c2 : c.regValue .rdx = stackPtr s - 432 :=
    ec.writes.2.2.2.2.2.1.trans b15
  have cbzz := kc _ _ (by decide) (by decide)
    (call_keep mb (offset := 432) (by decide) (by decide) (by decide)
      (ka _ _ (by decide) (by decide) input.bzz3))
  obtain ⟨nd, d, rd, fd, pd, plus, ad, md, wd⟩ := binary_call (x := (values point).yy) (y := (values point).bzz3)
    (op := fun x y => (x+y) % P256.Spec.Operations.domain.p) pre fc additionSite
    (fun _ hp hx hy => field_add_correct hp hx hy) ec.rip c6 c2 c7
    (addition_copy_8 pre fb ec byy) cbzz
  have dminus := call_keep md (offset := 400) (by decide) (by decide) (by decide)
    (kc _ _ (by decide) (by decide) minus)
  have d13 : d.regValue .r13 = stackPtr s - 144 := (ad .r13 (by simp)).trans c13
  have d12 : d.regValue .r12 = stackPtr s - 400 := (ad .r12 (by simp)).trans
    ((ec.agrees.read (n := 64) (r := 12) (by simp [additionEffect, Effect.components])).trans b12)
  obtain ⟨ne, e, re, fe, ee, me, ke⟩ := y_product_run pre fd pd
  have e15 : e.regValue .r15 = stackPtr s - 112 := by
    have h : e.regValue .r15 = stackPtr d + 616 := ee.writes.2.2.1
    exact h.trans (scalar_stack_address (frameOffset := 728) fd.rsp (by decide) (offset := 616) (by decide))
  have e2 : e.regValue .rdx = stackPtr s - 720 := by
    have h : e.regValue .rdx = stackPtr d + 8 := ee.writes.2.2.2.1
    exact h.trans (scalar_stack_address (frameOffset := 728) fd.rsp (by decide) (offset := 8) (by decide))
  have e7 : e.regValue .rdi = stackPtr s - 112 := by
    have h : e.regValue .rdi = stackPtr d + 616 := ee.writes.2.2.2.2.1
    exact h.trans (scalar_stack_address (frameOffset := 728) fd.rsp (by decide) (offset := 616) (by decide))
  have e6 : e.regValue .rsi = stackPtr s - 144 := ee.writes.2.2.2.2.2.1.trans d13
  obtain ⟨nf, f, rf, ff, pf, yprod, af, mf, wf⟩ := binary_call (x := (values point).yyPlus) (y := (values point).yyMinus)
    (op := fun x y => x*y % P256.Spec.Operations.domain.p) pre fe y_productSite
    (fun _ hp hx hy => field_mul_correct hp hx hy) ee.rip e6 e2 e7
    (ke _ _ (by decide) (by decide) plus) (y_product_copy_8 pre fd ee dminus)
  have f12 : f.regValue .r12 = stackPtr s - 400 := (af .r12 (by simp)).trans
    ((ee.agrees.read (n := 64) (r := 12) (by simp [y_productEffect, Effect.components])).trans d12)
  have f14 : f.regValue .r14 = stackPtr s - 176 := (af .r14 (by simp)).trans
    ((ee.agrees.read (n := 64) (r := 14) (by simp [y_productEffect, Effect.components])).trans
      ((ad .r14 (by simp)).trans
        ((ec.agrees.read (n := 64) (r := 14) (by simp [additionEffect, Effect.components])).trans
          ((ab .r14 (by simp)).trans
            ((ea.agrees.read (n := 64) (r := 14) (by simp [subtractionEffect, Effect.components])).trans input.r14)))))
  have fminus := call_keep mf (offset := 400) (by decide) (by decide) (by decide)
    (ke _ _ (by decide) (by decide) dminus)
  have fxy := call_keep mf (offset := 176) (by decide) (by decide) (by decide)
    (ke _ _ (by decide) (by decide)
      (call_keep md (offset := 176) (by decide) (by decide) (by decide)
        (kc _ _ (by decide) (by decide)
          (call_keep mb (offset := 176) (by decide) (by decide) (by decide)
            (ka _ _ (by decide) (by decide) input.xy2)))))
  obtain ⟨ng, g, rg, fg, eg, mg, kg⟩ := x_product_run pre ff pf
  have g7 : g.regValue .rdi = stackPtr s - 208 := by
    have h : g.regValue .rdi = stackPtr f + 520 := eg.writes.1
    exact h.trans (scalar_stack_address (frameOffset := 728) ff.rsp (by decide) (offset := 520) (by decide))
  have g6 : g.regValue .rsi = stackPtr s - 400 := eg.writes.2.1.trans f12
  have g2 : g.regValue .rdx = stackPtr s - 176 := eg.writes.2.2.trans f14
  obtain ⟨nh, h, rh, fh, ph, xprod, ah, mh, wh⟩ := binary_call (x := (values point).yyMinus) (y := (values point).xy2)
    (op := fun x y => x*y % P256.Spec.Operations.domain.p) pre fg x_productSite
    (fun _ hp hx hy => field_mul_correct hp hx hy) eg.rip g6 g2 g7
    (kg _ _ (by decide) (by decide) fminus) (kg _ _ (by decide) (by decide) fxy)
  have execution := ((((((ra.trans rb).trans rc).trans rd).trans re).trans rf).trans rg).trans rh
  have mem := memoryWriteFrame_trans (memoryWriteFrame_trans (memoryWriteFrame_trans
    (memoryWriteFrame_trans (memoryWriteFrame_trans (memoryWriteFrame_trans
      (memoryWriteFrame_trans ma wb) mc) wd) me) wf) mg) wh
  refine ⟨_, h, execution, fh, ph, ?_⟩
  refine ⟨point_of_stack pre (work_stack_frame pre mem) input.pointAt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, xprod, ?_⟩
  · exact (ah .rbx (by simp)).trans
      ((eg.agrees.read (n := 64) (r := 3) (by simp [x_productEffect, Effect.components])).trans
        ((af .rbx (by simp)).trans
          ((ee.agrees.read (n := 64) (r := 3) (by simp [y_productEffect, Effect.components])).trans
            ((ad .rbx (by simp)).trans
              ((ec.agrees.read (n := 64) (r := 3) (by simp [additionEffect, Effect.components])).trans
                ((ab .rbx (by simp)).trans
                  ((ea.agrees.read (n := 64) (r := 3) (by simp [subtractionEffect, Effect.components])).trans input.rbx)))))))
  · exact (ah .rbp (by simp)).trans
      ((eg.agrees.read (n := 64) (r := 5) (by simp [x_productEffect, Effect.components])).trans
        ((af .rbp (by simp)).trans
          ((ee.agrees.read (n := 64) (r := 5) (by simp [y_productEffect, Effect.components])).trans
            ((ad .rbp (by simp)).trans
              ((ec.agrees.read (n := 64) (r := 5) (by simp [additionEffect, Effect.components])).trans
                ((ab .rbp (by simp)).trans
                  ((ea.agrees.read (n := 64) (r := 5) (by simp [subtractionEffect, Effect.components])).trans input.rbp)))))))
  · exact (ah .r15 (by simp)).trans
      ((eg.agrees.read (n := 64) (r := 15) (by simp [x_productEffect, Effect.components])).trans
        ((af .r15 (by simp)).trans e15))
  · exact call_keep mh (offset := 624) (by decide) (by decide) (by decide)
      (kg _ _ (by decide) (by decide)
        (call_keep mf (offset := 624) (by decide) (by decide) (by decide)
          (ke _ _ (by decide) (by decide)
            (call_keep md (offset := 624) (by decide) (by decide) (by decide)
              (kc _ _ (by decide) (by decide)
                (call_keep mb (offset := 624) (by decide) (by decide) (by decide)
                  (ka _ _ (by decide) (by decide) input.xx)))))))
  · exact call_keep mh (offset := 592) (by decide) (by decide) (by decide)
      (kg _ _ (by decide) (by decide)
        (call_keep mf (offset := 592) (by decide) (by decide) (by decide)
          (ke _ _ (by decide) (by decide)
            (call_keep md (offset := 592) (by decide) (by decide) (by decide)
              (kc _ _ (by decide) (by decide)
                (call_keep mb (offset := 592) (by decide) (by decide) (by decide)
                  (ka _ _ (by decide) (by decide) input.yy)))))))
  · exact call_keep mh (offset := 560) (by decide) (by decide) (by decide)
      (kg _ _ (by decide) (by decide)
        (call_keep mf (offset := 560) (by decide) (by decide) (by decide)
          (ke _ _ (by decide) (by decide)
            (call_keep md (offset := 560) (by decide) (by decide) (by decide)
              (kc _ _ (by decide) (by decide)
                (call_keep mb (offset := 560) (by decide) (by decide) (by decide)
                  (ka _ _ (by decide) (by decide) input.zz)))))))
  · exact call_keep mh (offset := 528) (by decide) (by decide) (by decide)
      (kg _ _ (by decide) (by decide)
        (call_keep mf (offset := 528) (by decide) (by decide) (by decide)
          (ke _ _ (by decide) (by decide)
            (call_keep md (offset := 528) (by decide) (by decide) (by decide)
              (kc _ _ (by decide) (by decide)
                (call_keep mb (offset := 528) (by decide) (by decide) (by decide)
                  (ka _ _ (by decide) (by decide) input.xz2)))))))
  · exact call_keep mh (offset := 112) (by decide) (by decide) (by decide)
      (kg _ _ (by decide) (by decide) yprod)

end P256.Proofs.Projective.Double
