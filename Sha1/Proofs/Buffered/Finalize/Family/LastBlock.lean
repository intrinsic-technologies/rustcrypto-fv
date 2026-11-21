import Sha1.Proofs.Buffered.Finalize.Family.LastBlock.Copy
import Sha1.Proofs.Buffered.Finalize.Family.CompressBlock

namespace Sha1.Proofs.Buffered.Finalize.Family

open Sha1.Spec Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Standards.NIST

theorem last_block [bindings : Bindings] {b : ReturnBoundary} {m : ByteArray} {s : RamState}
    (hStride : UnitStringStride bindings) (hOutside : ¬ InProgram b.rip)
    (storage : Storage .updateFinalizeCopy s) (ready : ReadyToStep s)
    (code : CodeIn Extracted.programImage s)
    (h : Last m s) : ∃ t, Run b s t ∧ t.RIP = 0x101f80 ∧ StateBytes t (finalHash m) := by
  obtain ⟨u, run, rip, state, bytes⟩ :=
    LastBlock.copy_last_block hOutside storage ready code h
  have df : DirectionFlagClear u.RFLAGS :=
    (run.agrees.directionFlagClear (by simp [Kind.changes, Kind.workRegisters, Kind.localChanges])
      ⟨h.df⟩).df
  obtain ⟨t, done⟩ := compress_block hStride hOutside
    (storage.of_agrees run.agrees run.rsp) run.ready run.code df (.inr rfl) rip
    (Digest.size_lastBlock m) bytes state
  exact ⟨t, run.trans done.toRun, done.rip, done.state⟩

end Sha1.Proofs.Buffered.Finalize.Family
