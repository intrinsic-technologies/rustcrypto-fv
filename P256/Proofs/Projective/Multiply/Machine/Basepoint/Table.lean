import P256.Proofs.Projective.Multiply.Machine.Basepoint.Prologue
import P256.Proofs.Projective.Multiply.Machine.Basepoint.Prepared
import P256.Proofs.Projective.Multiply.Machine.Basepoint.Table.FirstEntries
import P256.Proofs.Projective.Multiply.Machine.Basepoint.Table.ThirdEntry
import P256.Proofs.Projective.Multiply.Machine.Basepoint.Table.FourthEntry
import P256.Proofs.Projective.Multiply.Machine.Basepoint.Table.FifthEntry
import P256.Proofs.Projective.Multiply.Machine.Basepoint.Table.SixthEntry
import P256.Proofs.Projective.Multiply.Machine.Basepoint.Table.SeventhEntry
import P256.Proofs.Projective.Multiply.Machine.Basepoint.Table.EighthEntry

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Basepoint

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame Table

theorem table_prepared [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10e6f0 32 65 3352) :
    ∃ t, Prepared s t boundary := by
  obtain ⟨t0, run0, st0, rip0, _, saved0⟩ := frame_entry pre
  have facts0 : Facts s t0 [(.rsi, s.regValue .rsi), (.rdi, s.regValue .rdi)] [] := by
    refine ⟨⟨?_, ?_, trivial⟩, trivial⟩
    · exact saved0.read (n := 64) (r := 6) (by simp [saveFrame])
    · exact saved0.read (n := 64) (r := 7) (by simp [saveFrame])
  obtain ⟨n1, t1, run1, st1, rip1, facts1⟩ := first_entries pre st0 rip0 facts0
  obtain ⟨n2, t2, run2, st2, rip2, facts2⟩ := third_entry pre st1 rip1 facts1
  obtain ⟨n3, t3, run3, st3, rip3, facts3⟩ := fourth_entry pre st2 rip2 facts2
  obtain ⟨n4, t4, run4, st4, rip4, facts4⟩ := fifth_entry pre st3 rip3 facts3
  obtain ⟨n5, t5, run5, st5, rip5, facts5⟩ := sixth_entry pre st4 rip4 facts4
  obtain ⟨n6, t6, run6, st6, rip6, facts6⟩ := seventh_entry pre st5 rip5 facts5
  obtain ⟨n7, t7, run7, st7, rip7, facts7⟩ := eighth_entry pre st6 rip6 facts6
  rcases facts7.regs with ⟨output, _, _, _, _, scalar, _⟩
  rcases facts7.points with ⟨_, _, p7, p6, p5, p4, p3, p2, p1, p0, _⟩
  refine ⟨t7, st7, ⟨7+n1+n2+n3+n4+n5+n6+n7,
    ((((((run0.trans run1).trans run2).trans run3).trans run4).trans run5).trans run6).trans run7⟩,
    rip7, output, scalar, ?_⟩
  intro index
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

end P256.Proofs.Projective.Multiply.Machine.Basepoint
