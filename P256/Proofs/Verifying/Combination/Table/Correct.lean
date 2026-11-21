import P256.Proofs.Verifying.Combination.Table.Populate
import P256.Proofs.Verifying.Combination.Table.Output
import P256.Proofs.Verifying.Combination.Table.Epilogue

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Table

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs

theorem oddTable_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {cursor point : BitVec 64} {value : Projective}
    (pre : TablePre s boundary cursor point) (input : ProjectiveAt s point value) :
    ∃ t, TableResult s t boundary cursor point ∧
      TableAt t (s.regValue .rdi) (oddTable value) := by
  obtain ⟨n, t, run, mem, regs, rip⟩ := populate_table pre input
  obtain ⟨m, u, run', frame, rip', table, cursorValue, rbx⟩ := copy_table_output pre mem regs mem.tableAt rip
  obtain ⟨v, result, memory⟩ := epilogue pre frame rip' rbx cursorValue ⟨n+m, run.trans run'⟩
  exact ⟨v, result, table.of_copy (fun _ _ => by rw [memory])⟩

theorem correct : Correct := by
  intro _ _ _ _ _ _ pre input
  exact oddTable_correct pre input

end P256.Proofs.Verifying.Combination.Table
