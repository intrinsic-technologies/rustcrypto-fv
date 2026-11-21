import Sha1.Proofs.Buffered.Finalize.Family.Prepare
import Sha1.Proofs.Buffered.Finalize.Family.Pad
import Sha1.Proofs.Buffered.Finalize.Family.Long
import Sha1.Proofs.Buffered.Finalize.Family.LastBlock
import Sha1.Proofs.Buffered.Finalize.Family.Output

namespace Sha1.Proofs.Buffered.Finalize

open Sha1.Spec Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem finalize_family [bindings : Bindings]
    {boundary : ReturnBoundary} {message : ByteArray} {s : RamState}
    (h : Pre .updateFinalizeCopy boundary message s)
    (hOutputBounded : (Kind.resultRegion .updateFinalizeCopy s).Bounded)
    (hOutputAllocated : (Kind.resultRegion .updateFinalizeCopy s).Allocated s.external)
    (hOutputDisjoint : (Kind.resultRegion .updateFinalizeCopy s).Disjoint
      (Kind.stackRegion .updateFinalizeCopy s))
    (hOutputAvoids : (Kind.resultRegion .updateFinalizeCopy s).Avoids
      (fun address ↦ InProgram address ∨ InPageTables address)) :
    ∃ t, Post .updateFinalizeCopy boundary message s t := by
  obtain ⟨u, hu, hprep⟩ := Family.prepare h
  obtain ⟨v, hv, hpad⟩ := Family.pad h.stride h.boundaryOutside
    (h.toStorage.of_agrees hu.agrees hu.rsp) hu.ready hu.code hprep
  have hsv := hu.trans hv
  have step : ∃ w, Family.Run boundary s w ∧ Family.Last message w := by
    by_cases short : message.size % 64 < 56
    · refine ⟨v, hsv, hpad.toPosition, by simpa only [short, ite_true] using hpad.rip,
        hpad.df, ?_, ?_⟩
      · simpa only [Family.penultimateHash, short, ite_true] using hpad.state
      · intro i hi
        simpa only [short, ite_true] using hpad.padded i (by omega)
    · obtain ⟨w, hw, hlast⟩ := Family.long_path h.stride h.boundaryOutside
        (h.toStorage.of_agrees hsv.agrees hsv.rsp) hsv.ready hsv.code hpad (by omega)
      exact ⟨w, hsv.trans hw, hlast⟩
  obtain ⟨w, hw, hwlast⟩ := step
  obtain ⟨x, hx, hip, hstate⟩ := Family.last_block h.stride h.boundaryOutside
    (h.toStorage.of_agrees hw.agrees hw.rsp) hw.ready hw.code hwlast
  have hsx := hw.trans hx
  have result : Kind.resultRegion .updateFinalizeCopy x = Kind.resultRegion .updateFinalizeCopy s :=
    congrArg (fun a : BitVec 64 ↦ (⟨a.toNat, 20⟩ : MemoryRegion)) hsx.saved
  have stack : Kind.stackRegion .updateFinalizeCopy x = Kind.stackRegion .updateFinalizeCopy s := by
    simp only [Kind.stackRegion, hsx.rsp]
  have alloc : (Kind.resultRegion .updateFinalizeCopy x).Allocated x.external := by
    rw [result]
    intro a ha
    exact Option.isSome_iff_exists.mp (hsx.agrees.grow _ (Option.isSome_iff_exists.mpr (hOutputAllocated a ha)))
  obtain ⟨t, ht, hit, hd⟩ := Family.write_output h.boundaryOutside
    (h.toStorage.of_agrees hsx.agrees hsx.rsp) hsx.ready hsx.code hip hstate
    (result ▸ hOutputBounded) alloc (by rwa [result, stack]) (result ▸ hOutputAvoids)
  have hst := hsx.trans ht
  exact ⟨t, hst.advances, ht.ready, ht.code, hit, by rwa [Family.resultBytes, ← result], hst.agrees⟩

end Sha1.Proofs.Buffered.Finalize
