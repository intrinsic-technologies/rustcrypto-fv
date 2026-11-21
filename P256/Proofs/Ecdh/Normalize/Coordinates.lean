import P256.Proofs.Ecdh.Normalize.Coordinates.X
import P256.Proofs.Ecdh.Normalize.Coordinates.YCopy

set_option autoImplicit false

namespace P256.Proofs.Ecdh.Normalize

open P256.Spec.Program P256.Spec.Program.Routines Program Program.ScalarFrame Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Standards.SECG.ECC
open P256.Spec.Operations (domain)
open Coordinates

theorem coordinates [Bindings] {s t : RamState} {boundary : ReturnBoundary} {point : Projective}
    (pre : CalleePre s boundary 0x100000 32 32 3464) (state : Selected s t boundary point) :
    ∃ u, Coordinates s u boundary point := by
  obtain ⟨v,st⟩ := x_product pre state
  obtain ⟨n1,t1,run1,st1,ip1,value1,ag1⟩ := copy_coordinate pre st.toFrameState
    (YCopy.copy boundary pre.outerBoundary) (entryOffset := 0x3f2) (sourceOffset := 184)
    (by decide) (by decide +kernel) (by decide) rfl rfl st.rip st.y
  have x1 := copy_preserves ag1 (by unfold OffsetsApart; decide +kernel) st.x
  have z1 := copy_preserves ag1 (by unfold OffsetsApart; decide +kernel) st.inverse
  obtain ⟨n2,t2,run2,st2,e2,ext2⟩ := y_setup st1 pre.outerBoundary ip1
  have regs2 := e2.writes
  change t2.regValue .rdi = stackPtr t1 + 48 ∧
    t2.regValue .rsi = stackPtr t1 + 1016 ∧
    t2.regValue .rdx = t1.regValue .r14 at regs2
  have r141 : t1.regValue .r14 = stackPtr s - 176 :=
    (ag1.read (n := 64) (r := 14) (by simp [Copy32.components])).trans st.r14
  have addr1016 : stackPtr t1 + 1016 = stackPtr s - 1040 :=
    scalar_stack_address st1.rsp (by decide) (by decide)
  have addr48 : stackPtr t1 + 48 = stackPtr s - 2008 :=
    scalar_stack_address st1.rsp (by decide) (by decide)
  obtain ⟨n3,u,run3,st3,ip3,value3,regs3,bytes3,_⟩ :=
    FieldCall.binary_call pre st2 ySite
      (op := fun x y => x*y % domain.p) (fun _ hp hx hy => field_mul_correct hp hx hy)
      e2.rip
      (regs2.2.1.trans addr1016) (regs2.2.2.trans r141) (regs2.1.trans addr48)
      (value1.of_bytes_eq (by intro i hi; rw [ext2]; rfl))
      (z1.of_bytes_eq (by intro i hi; rw [ext2]; rfl))
  have x3 : MontgomeryAt u (stackPtr s - 1808)
      (point.x * Curve.inverse domain.p point.z % domain.p) := by
    apply x1.of_bytes_eq
    intro i hi
    simpa only [ext2, BitVec.ofNat_eq_ofNat] using bytes3 1808 32 (by decide) (by decide) (by decide) i hi
  have bp2 : t2.regValue .rbp = v.regValue .rbp :=
    (e2.agrees.read (n := 64) (r := 5) (by simp [yEffect,Effect.components])).trans
      (ag1.read (n := 64) (r := 5) (by simp [Copy32.components]))
  have bx2 : t2.regValue .rbx = v.regValue .rbx :=
    (e2.agrees.read (n := 64) (r := 3) (by simp [yEffect,Effect.components])).trans
      (ag1.read (n := 64) (r := 3) (by simp [Copy32.components]))
  have r152 : t2.regValue .r15 = stackPtr s - 1808 :=
    (e2.agrees.read (n := 64) (r := 15) (by simp [yEffect,Effect.components])).trans
      ((ag1.read (n := 64) (r := 15) (by simp [Copy32.components])).trans st.r15)
  obtain ⟨n0,run0⟩ := st.execution
  refine ⟨u,st3,⟨n0+n1+n2+n3,((run0.trans run1).trans run2).trans run3⟩,ip3,
    (regs3 .rbx (by simp)).trans (bx2.trans st.output),x3,value3,?_,
    (regs3 .r15 (by simp)).trans r152⟩
  rw [regs3 .rbp (by simp),bp2]
  exact st.choice

end P256.Proofs.Ecdh.Normalize
