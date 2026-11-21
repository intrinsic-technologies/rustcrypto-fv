import P256.Proofs.Ecdh.Normalize.Coordinates.Support
import P256.Proofs.Ecdh.Normalize.Coordinates.XCopy
import P256.Proofs.Ecdh.Normalize.Coordinates.Registers
import P256.Proofs.Ecdh.Normalize.Coordinates.Sites
import P256.Proofs.Field.Montgomery

set_option autoImplicit false

namespace P256.Proofs.Ecdh.Normalize.Coordinates

open P256.Spec.Program P256.Spec.Program.Routines Program Program.ScalarFrame Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Standards.SECG.ECC
open P256.Spec.Operations (domain)

structure XProduct [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (point : Projective) : Prop extends FrameState s t 32 3464 2056 where
  execution : ∃ fuel, Advances boundary fuel s t
  rip : t.RIP = 0x1003f2
  output : t.regValue .rbx = s.regValue .rdi
  x : MontgomeryAt t (stackPtr s - 1808) (point.x * Curve.inverse domain.p point.z % domain.p)
  y : MontgomeryAt t (stackPtr s - 1872) point.y
  inverse : MontgomeryAt t (stackPtr s - 176) (Curve.inverse domain.p point.z)
  choice : (t.regValue .rbp).setWidth 8 = if point.z = 0 then 0 else 1
  r14 : t.regValue .r14 = stackPtr s - 176
  r15 : t.regValue .r15 = stackPtr s - 1808

theorem x_product [Bindings] {s t : RamState} {boundary : ReturnBoundary} {point : Projective}
    (pre : CalleePre s boundary 0x100000 32 32 3464) (state : Selected s t boundary point) :
    ∃ u, XProduct s u boundary point := by
  obtain ⟨n1,t1,run1,st1,ip1,value1,ag1⟩ := copy_coordinate pre state.toFrameState
    (XCopy.copy boundary pre.outerBoundary) (entryOffset := 0x397) (sourceOffset := 152)
    (by decide) (by decide +kernel) (by decide) rfl rfl state.rip state.projective.1
  have y0 : MontgomeryAt t (stackPtr s - 1872) point.y := by
    have h := state.projective.2.1
    simpa only [show stackPtr s - 1904 + 32 = stackPtr s - 1872 by
      simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl] using h
  have y1 := copy_preserves ag1 (by unfold OffsetsApart; decide +kernel) y0
  have z1 := copy_preserves ag1 (by unfold OffsetsApart; decide +kernel) state.inverse
  obtain ⟨n2,t2,run2,st2,e2,ext2⟩ := x_setup st1 pre.outerBoundary ip1
  have regs2 := e2.writes
  change t2.regValue .r15 = stackPtr t1 + 248 ∧
    t2.regValue .rsi = stackPtr t1 + 1016 ∧
    t2.regValue .rdi = stackPtr t1 + 248 ∧
    t2.regValue .rdx = t1.regValue .r14 at regs2
  have r141 : t1.regValue .r14 = stackPtr s - 176 :=
    (ag1.read (n := 64) (r := 14) (by simp [Copy32.components])).trans state.r14
  have addr1016 : stackPtr t1 + 1016 = stackPtr s - 1040 :=
    scalar_stack_address st1.rsp (by decide) (by decide)
  have addr248 : stackPtr t1 + 248 = stackPtr s - 1808 :=
    scalar_stack_address st1.rsp (by decide) (by decide)
  obtain ⟨n3,u,run3,st3,ip3,value3,regs3,bytes3,_⟩ :=
    FieldCall.binary_call pre st2 xSite
      (op := fun x y => x*y % domain.p) (fun _ hp hx hy => field_mul_correct hp hx hy)
      e2.rip
      (regs2.2.1.trans addr1016) (regs2.2.2.2.trans r141) (regs2.2.2.1.trans addr248)
      (value1.of_bytes_eq (by intro i hi; rw [ext2]; rfl))
      (z1.of_bytes_eq (by intro i hi; rw [ext2]; rfl))
  have y3 : MontgomeryAt u (stackPtr s - 1872) point.y := by
    apply y1.of_bytes_eq
    intro i hi
    simpa only [ext2, BitVec.ofNat_eq_ofNat] using bytes3 1872 32 (by decide) (by decide) (by decide) i hi
  have z3 : MontgomeryAt u (stackPtr s - 176) (Curve.inverse domain.p point.z) := by
    apply z1.of_bytes_eq
    intro i hi
    simpa only [ext2, BitVec.ofNat_eq_ofNat] using bytes3 176 32 (by decide) (by decide) (by decide) i hi
  have bp2 : t2.regValue .rbp = t.regValue .rbp :=
    (e2.agrees.read (n := 64) (r := 5) (by simp [xEffect,Effect.components])).trans
      (ag1.read (n := 64) (r := 5) (by simp [Copy32.components]))
  have bx2 : t2.regValue .rbx = t.regValue .rbx :=
    (e2.agrees.read (n := 64) (r := 3) (by simp [xEffect,Effect.components])).trans
      (ag1.read (n := 64) (r := 3) (by simp [Copy32.components]))
  have r142 : t2.regValue .r14 = stackPtr s - 176 :=
    (e2.agrees.read (n := 64) (r := 14) (by simp [xEffect,Effect.components])).trans r141
  obtain ⟨n0,run0⟩ := state.execution
  refine ⟨u,st3,⟨n0+n1+n2+n3,((run0.trans run1).trans run2).trans run3⟩,ip3,
    (regs3 .rbx (by simp)).trans (bx2.trans state.output),value3,y3,z3,?_,
    (regs3 .r14 (by simp)).trans r142,
    (regs3 .r15 (by simp)).trans (regs2.1.trans addr248)⟩
  rw [regs3 .rbp (by simp),bp2]
  exact state.choice

end P256.Proofs.Ecdh.Normalize.Coordinates
