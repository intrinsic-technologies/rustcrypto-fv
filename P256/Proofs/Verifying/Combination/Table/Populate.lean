import P256.Proofs.Verifying.Combination.Table.Sites
import P256.Proofs.Verifying.Combination.Table.Step
import P256.Proofs.Verifying.Combination.Table.Initialize

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Table

open P256.Proofs.Program

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def prefixCells (value : Projective) : Nat → Cells
  | 0 => initialCells value
  | n + 1 => writeCell (writeCell (prefixCells value n) 9 (oddTableEntry value (n+1)))
      (Fin.ofNat 11 (n+1)) (oddTableEntry value (n+1))

def finalCells (value : Projective) : Cells :=
  writeCell (prefixCells value 7) 9 (oddTableEntry value 8)

theorem populate_table [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {cursor point : BitVec 64} {value : Projective}
    (pre : TablePre s boundary cursor point) (input : ProjectiveAt s point value) :
    ∃ fuel t, Advances boundary fuel s t ∧ Memory s t cursor point (finalCells value) ∧
      Registers s t ∧ t.RIP = 0x10b148 := by
  obtain ⟨n0, t0, run0, mem0, regs0, rip0⟩ := initialize_table pre input
  obtain ⟨n1, t1, run1, mem1, regs1, rip1⟩ :=
    add_copy_current (left := oddTableEntry value 0) (right := value.double)
      pre mem0 regs0 addSite1 1 (by decide) copySite1 rfl rip0 rfl rfl
  change Memory s t1 cursor point (prefixCells value 1) at mem1
  obtain ⟨n2, t2, run2, mem2, regs2, rip2⟩ :=
    add_copy_current (left := oddTableEntry value 1) (right := value.double)
      pre mem1 regs1 addSite2 2 (by decide) copySite2 rfl rip1 rfl rfl
  change Memory s t2 cursor point (prefixCells value 2) at mem2
  obtain ⟨n3, t3, run3, mem3, regs3, rip3⟩ :=
    add_copy_current (left := oddTableEntry value 2) (right := value.double)
      pre mem2 regs2 addSite3 3 (by decide) copySite3 rfl rip2 rfl rfl
  change Memory s t3 cursor point (prefixCells value 3) at mem3
  obtain ⟨n4, t4, run4, mem4, regs4, rip4⟩ :=
    add_copy_current (left := oddTableEntry value 3) (right := value.double)
      pre mem3 regs3 addSite4 4 (by decide) copySite4 rfl rip3 rfl rfl
  change Memory s t4 cursor point (prefixCells value 4) at mem4
  obtain ⟨n5, t5, run5, mem5, regs5, rip5⟩ :=
    add_copy_current (left := oddTableEntry value 4) (right := value.double)
      pre mem4 regs4 addSite5 5 (by decide) copySite5 rfl rip4 rfl rfl
  change Memory s t5 cursor point (prefixCells value 5) at mem5
  obtain ⟨n6, t6, run6, mem6, regs6, rip6⟩ :=
    add_copy_current (left := oddTableEntry value 5) (right := value.double)
      pre mem5 regs5 addSite6 6 (by decide) copySite6 rfl rip5 rfl rfl
  change Memory s t6 cursor point (prefixCells value 6) at mem6
  obtain ⟨n7, t7, run7, mem7, regs7, rip7⟩ :=
    add_copy_current (left := oddTableEntry value 6) (right := value.double)
      pre mem6 regs6 addSite7 7 (by decide) copySite7 rfl rip6 rfl rfl
  change Memory s t7 cursor point (prefixCells value 7) at mem7
  obtain ⟨n8, t8, run8, mem8, regs8, rip8⟩ :=
    add_current (left := oddTableEntry value 7) (right := value.double)
      pre mem7 regs7 addSite8 rip7 rfl rfl
  exact ⟨n0+n1+n2+n3+n4+n5+n6+n7+n8, t8,
    (((((((run0.trans run1).trans run2).trans run3).trans run4).trans run5).trans run6).trans run7).trans run8,
    mem8, regs8, rip8⟩

theorem finalCells_table (value : Projective) (i : Fin 8) :
    finalCells value ⟨i.val, by have := i.isLt; omega⟩ = some (oddTable value i) := by
  rcases i with ⟨i, hi⟩
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem table_address (s : RamState) (i : Fin 8) :
    stackPtr s - 1088 + BitVec.ofNat 64 (96*i.val) =
      stackPtr s - BitVec.ofNat 64 (offset ⟨i.val, by have := i.isLt; omega⟩) := by
  have hb : 96*i.val ≤ 1088 := by have := i.isLt; omega
  rw [offset, ← BitVec.ofNat_sub_ofNat_of_le 1088 (96*i.val) (by omega) hb]
  simp only [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.neg_neg, BitVec.add_assoc]
  rfl

theorem Memory.tableAt [Bindings] {s t : RamState} {cursor point : BitVec 64} {value : Projective}
    (state : Memory s t cursor point (finalCells value)) :
    TableAt t (stackPtr s - 1088) (oddTable value) := by
  intro i
  rw [table_address]
  exact state.cells _ _ (finalCells_table value i)

end P256.Proofs.Verifying.Combination.Table
