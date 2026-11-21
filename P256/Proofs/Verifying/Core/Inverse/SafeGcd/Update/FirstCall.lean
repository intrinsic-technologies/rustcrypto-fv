import P256.Proofs.Field.Inverse.SafeGcd.Core.Prepare.Frame
import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Update.Memory

namespace P256.Proofs.Verifying.Core.Inverse.SafeGcd.Update

open P256.Proofs.Field.Inverse.SafeGcd
open P256.Proofs.Field.Inverse.SafeGcd.Core.Shared
open P256.Proofs.Field.Inverse.SafeGcd.Core.Shared.Batch
open P256.Proofs.Field.Inverse.SafeGcd.Core

open P256.Proofs.Field.Inverse.SafeGcd.Core.Support (MemoryStable atom_of_frame atoms_of_frame)

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

set_option maxRecDepth 4096 in
set_option maxHeartbeats 600000 in
theorem first_call [Bindings] {code : CodeMap}
    (hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    {initial : RamState} {fr : Activation} {controls : RamState} {p : Inputs} {s : LoopState} {boundary : ReturnBoundary}
    (hready : EntryReady code initial) (hrip : initial.RIP = 0x1115d0)
    (hframe : RamWriteFrame fr.original initial.external [fr.region, outputRegion fr])
    (hout : ReturnOutside boundary code)
    (hcore : Atom.All code (Machine.lifted.locationOf .l1170b0 initial).arguments
      initial.external (firstCall fr controls p s)) :
    ∃ fuel final, Advances boundary fuel initial final ∧ EntryReady code final ∧
      final.RIP = 0x11230c ∧
      RamWriteFrame fr.original final.external [fr.region, outputRegion fr] ∧
      Atom.All code (Machine.lifted.locationOf .l11435c final).arguments final.external
        (firstReturned fr controls p s) := by
  simp only [firstCall, Atom.all_append] at hcore
  obtain ⟨⟨⟨hmem, hb⟩, hpres⟩, hargs⟩ := hcore
  have hstable := memory_stable hmem
  have hm := hmem
  simp only [memoryAtoms, commonAtoms, outputAtoms, inputAtoms, savedInputAtoms,
    stateAtoms, signedAtoms, Atom.all_append, Atom.All, Atom.Holds] at hm
  obtain ⟨⟨⟨⟨⟨_, _, _, _, _, _, _, hretread, _, hw, hroom, halign, _, _, _, _⟩,
    _, _⟩, _⟩, ⟨⟨⟨hfw, hfs, _⟩, hgw, hgs, _⟩, _⟩, _⟩, _⟩ := hm
  simp only [preservedAtoms, Atom.All, Atom.Holds, Lifted.locationOf,
    Fin.getElem_fin, Vector.getElem_ofFn] at hpres
  obtain ⟨hrsp, hdf, hrbx, hrbp, hr12, hr13, hr14, hr15, hmx, hfc, _⟩ := hpres
  simp only [Atom.All, Atom.Holds, Lifted.locationOf,
    Fin.getElem_fin, Vector.getElem_ofFn] at hargs
  obtain ⟨hrdi, hrsi, hrdx, hrcx, hr8, hr9, hret, hslot, _⟩ := hargs
  have hsp : stackPtr initial = fr.rsp - 0x190 := Value.eq_bits hrsp
  have hdi : initial.regValue .rdi = fr.rsp - 0xd8 := Value.eq_bits hrdi
  have hsi : initial.regValue .rsi = fr.rsp - 0x180 := Value.eq_bits hrsi
  have hdx : initial.regValue .rdx = fr.rsp - 0x158 := Value.eq_bits hrdx
  have hcx : initial.regValue .rcx = (batchResult s).u := Value.eq_bits hrcx
  have h8 : initial.regValue .r8 = (batchResult s).v := Value.eq_bits hr8
  have h9 : initial.regValue .r9 = (BitVec.ofNat 32 (batchCount s)).setWidth 64 := Value.eq_bits hr9
  have hret' : (returnBoundary initial).rip = 0x11230c := by
    change memLoad initial.external (stackPtr initial) 64 = _
    rwa [hsp]
  have hwindow : Writable code initial.external (stackPtr initial - 0xc0) 0xc0 := by
    rw [hsp]; exact hw.sub (by bv_omega) (by bv_omega)
  have hentry := Core.Support.activation_entryAtoms LinearShift.Machine.Shift.frameInfo
    LinearShift.Machine.lifted .l1170b0 rfl (by rw [hret']; decide)
    (by rwa [hsp]) hwindow (by change 0xc0 ≤ (stackPtr initial).toNat; rw [hsp]; bv_omega)
    (by rw [hsp]; bv_omega) (Reg.read_df_iff.1 hdf)
  have hc : (BitVec.ofNat 32 (batchCount s)).toNat = batchCount s := by
    rw [BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    simp only [batchCount]
    omega
  have hinput : Atom.All code (LinearShift.Machine.lifted.locationOf .l1170b0 initial).arguments
      initial.external (LinearShift.entryAtoms (Core.Support.activation initial 0xc0) controls (fInput s)) := by
    simp only [LinearShift.entryAtoms, Atom.all_append]
    refine ⟨⟨⟨⟨hentry, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · simp only [LinearShift.outputAtoms, Core.Support.activation, Atom.All, Atom.Holds, Lifted.locationOf, Fin.getElem_fin, Vector.getElem_ofFn]
      rw [hdi, hsp]
      exact ⟨hmx, hfc, hw.sub (by bv_omega) (by bv_omega), Or.inr (by bv_omega), trivial⟩
    · simp only [LinearShift.inputAtoms, Core.Support.activation, fInput, linearInput, Atom.All, Atom.Holds]
      rw [hsi, hdx, hsp, hcx, h8]
      exact ⟨hfw, hgw, hfs, hgs,
        (hw.sub (by bv_omega) (by bv_omega)).readable,
        (hw.sub (by bv_omega) (by bv_omega)).readable,
        Or.inr (by bv_omega), Or.inr (by bv_omega), rfl, rfl, trivial⟩
    · simp only [LinearShift.bounds, fInput, Atom.All, Atom.Holds, hc]
      have hp := hb.1
      change 1 ≤ s.remaining at hp
      exact ⟨by simp only [batchCount]; omega, by simp only [batchCount]; omega, trivial⟩
    · simp only [Atom.All, Atom.Holds, Core.Support.activation, fInput, h9]
      exact ⟨by bv_omega, trivial⟩
  have hretCode : ∃ b, (0x11230c, b) ∈ code :=
    ⟨_, hcode _ (Machine.code_l11435c _ (mem_codeRange _ _ 0 (by decide)))⟩
  obtain ⟨fuel, final, he, ready, hp, hwout, hsout, hrout, mx, fc⟩ := LinearShift.advances hcode hready hrip
    (fr := Core.Support.activation initial 0xc0) (RamWriteFrame.refl _ _) hout
    (Or.inl (by change (returnBoundary initial).rip ≠ boundary.rip
                rw [hret']; exact ReturnOutside.ne hout hretCode)) hinput
  have hwithin : RegionsWithin [(Core.Support.activation initial 0xc0).region,
      LinearShift.outputRegion (Core.Support.activation initial 0xc0)] (updateRegions fr) := by
    intro r hh
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl
    · refine ⟨({ start := (fr.rsp - 0x2c0).toNat, size := 0x138 } : MemoryRegion), by simp [updateRegions], ?_, ?_⟩
      all_goals simp only [Activation.region, Core.Support.activation, hsp]
      all_goals bv_omega
    · refine ⟨({ start := (fr.rsp - 0xd8).toNat, size := 0x50 } : MemoryRegion), by simp [updateRegions], ?_, ?_⟩
      all_goals simp only [LinearShift.outputRegion, Core.Support.activation, hdi]
      all_goals bv_omega
  have hmidframe := (RamWriteFrame.refl initial.external (updateRegions fr)).trans hp.frame hwithin
  have hmem' := atoms_of_frame (args' := (Machine.lifted.locationOf .l11435c final).arguments)
    hmidframe (memoryAtoms fr p s) hstable hmem
  have houter : RegionsWithin (updateRegions fr) [fr.region, outputRegion fr] := by
    intro r hh
    simp only [updateRegions, List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl
    all_goals refine ⟨fr.region, by simp, ?_, ?_⟩
    all_goals simp only [Activation.region]
    all_goals bv_omega
  have hspFinal := hp.rsp
  change (Reg.ofIndex 4).read final = ⟨64, stackPtr initial + 8⟩ at hspFinal
  rw [show stackPtr initial + 8 = fr.rsp - 0x188 by rw [hsp]; bv_omega] at hspFinal
  change WordsAt final.external (initial.regValue .rdi) 64 _ at hwout
  change memLoad final.external (initial.regValue .rdi + 32) 8 = _ at hsout
  change Readable final.external (initial.regValue .rdi) 33 at hrout
  rw [hdi] at hwout hsout hrout
  rw [show fr.rsp - 0xd8 + 32 = fr.rsp - 0xb8 by bv_omega] at hsout
  have hb' : Atom.All code (Machine.lifted.locationOf .l11435c final).arguments
      final.external (bounds s) := by
    change 1 ≤ s.remaining ∧ s.remaining ≤ 591 ∧ True
    exact ⟨hb.1, hb.2.1, trivial⟩
  refine ⟨fuel, final, he, ready, hp.rip.trans hret', hframe.trans hmidframe houter, ?_⟩
  simp only [firstReturned, Atom.all_append]
  refine ⟨⟨⟨hmem', hb'⟩, ?_⟩, hwout, hsout, hrout, trivial⟩
  simp only [preservedAtoms, Atom.All, Atom.Holds, Lifted.locationOf,
    Fin.getElem_fin, Vector.getElem_ofFn]
  exact ⟨hspFinal, Reg.read_df_iff.2 hp.df,
    (hp.preserved 3 (by decide)).trans hrbx, (hp.preserved 5 (by decide)).trans hrbp,
    (hp.preserved 12 (by decide)).trans hr12, (hp.preserved 13 (by decide)).trans hr13,
    (hp.preserved 14 (by decide)).trans hr14, (hp.preserved 15 (by decide)).trans hr15,
    congrArg (Value.mk 32) mx, congrArg (Value.mk 16) fc, trivial⟩

end P256.Proofs.Verifying.Core.Inverse.SafeGcd.Update
