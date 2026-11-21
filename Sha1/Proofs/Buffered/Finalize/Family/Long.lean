import Sha1.Proofs.Buffered.Finalize.Family.CompressBlock
import Sha1.Proofs.Buffered.Finalize.Family.Long.Stack

namespace Sha1.Proofs.Buffered.Finalize.Family

open Sha1.Spec Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Standards.NIST

theorem long_path [bindings : Bindings] {b : ReturnBoundary} {m : ByteArray} {s : RamState}
    (hStride : UnitStringStride bindings) (hOutside : ¬ InProgram b.rip)
    (storage : Storage .updateFinalizeCopy s) (ready : ReadyToStep s)
    (code : CodeIn Extracted.programImage s)
    (h : Padded m s) (hlong : 56 ≤ m.size % 64) : ∃ t, Run b s t ∧ Last m t := by
  obtain ⟨u, hu, hpc, hdf, hpos, hstate, hblock⟩ :=
    Long.copy_block hOutside storage ready code h hlong
  obtain ⟨v, hv⟩ := compress_block hStride hOutside (storage.of_agrees hu.agrees hu.rsp)
    hu.ready hu.code hdf (.inl rfl) hpc (Digest.size_firstBlock m) hblock hstate
  have huv := hu.trans hv.toRun
  have hvdf : DirectionFlagClear v.RFLAGS :=
    (hv.agrees.directionFlagClear (by simp [Kind.changes, Kind.workRegisters, Kind.localChanges])
      ⟨hdf⟩).df
  have hvpos : Position m v := ⟨hv.r14.trans hpos.position, hv.r15.trans hpos.blocks⟩
  have hvstate : StateBytes v (penultimateHash m) := by
    simpa only [penultimateHash, show ¬ m.size % 64 < 56 by omega, ite_false] using hv.state
  obtain ⟨t, ht, hlast⟩ := Long.clear_block hOutside (storage.of_agrees huv.agrees huv.rsp)
    hv.ready hv.code hv.rip hvdf hvpos hvstate hlong
  exact ⟨t, huv.trans ht, hlast⟩

end Sha1.Proofs.Buffered.Finalize.Family
