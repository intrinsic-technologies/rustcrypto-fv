import P256.Proofs.Ecdh.Table.Entry2
import P256.Proofs.Ecdh.Table.Entry3
import P256.Proofs.Ecdh.Table.Entry4
import P256.Proofs.Ecdh.Table.Entry5
import P256.Proofs.Ecdh.Table.Entry6
import P256.Proofs.Ecdh.Table.Entry7
import P256.Proofs.Ecdh.Table.Entry8

set_option autoImplicit false

namespace P256.Proofs.Ecdh

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame Table

theorem table_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {point : Standards.SECG.ECC.Curve.Point}
    (pre : Pre s boundary) (initial : Initial s t point) :
    ∃ fuel u, Advances boundary fuel t u ∧ Prepared s u point := by
  have baseAddress : frameBase s + 1784 = stackPtr s - 272 := by
    simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have tableAddress : frameBase s + 1016 = stackPtr s - 1040 := by
    simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have scalarAddress : frameBase s + 8 = stackPtr s - 2048 := by
    simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have facts : Facts s t [(.rbx, s.regValue .rdi), (.r15, stackPtr s - 272)]
      [(272, Projective.tableEntry (ProjectiveWrapper.Decode.projective point) 0),
        (1040, Projective.tableEntry (ProjectiveWrapper.Decode.projective point) 0)] := by
    refine ⟨⟨initial.output, ?_, trivial⟩, ⟨?_, ?_, trivial⟩, ?_⟩
    · exact initial.r15.trans baseAddress
    · exact baseAddress ▸ initial.base
    · exact tableAddress ▸ initial.first
    · exact scalarAddress ▸ initial.scalar
  obtain ⟨n2, t2, run2, st2, rip2, facts2⟩ := entry2 pre.toCalleePre initial.toFrameState initial.rip facts
  obtain ⟨n3, t3, run3, st3, rip3, facts3⟩ := entry3 pre.toCalleePre st2 rip2 facts2
  obtain ⟨n4, t4, run4, st4, rip4, facts4⟩ := entry4 pre.toCalleePre st3 rip3 facts3
  obtain ⟨n5, t5, run5, st5, rip5, facts5⟩ := entry5 pre.toCalleePre st4 rip4 facts4
  obtain ⟨n6, t6, run6, st6, rip6, facts6⟩ := entry6 pre.toCalleePre st5 rip5 facts5
  obtain ⟨n7, t7, run7, st7, rip7, facts7⟩ := entry7 pre.toCalleePre st6 rip6 facts6
  obtain ⟨n8, t8, run8, st8, rip8, facts8⟩ := entry8 pre.toCalleePre st7 rip7 facts7
  rcases facts8.points with ⟨_, p0, _, p1, _, p2, p3, p4, p5, p6, p7, _⟩
  refine ⟨n2+n3+n4+n5+n6+n7+n8, t8,
    (((((run2.trans run3).trans run4).trans run5).trans run6).trans run7).trans run8,
    st8, rip8, facts8.regs.1, ?_, ?_⟩
  · rw [scalarAddress]
    exact facts8.scalar
  · intro index
    rw [table_address]
    rcases index with ⟨i, hi⟩
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact p0
    · exact p1
    · exact p2
    · exact p3
    · exact p4
    · exact p5
    · exact p6
    · exact p7

end P256.Proofs.Ecdh
