import P256.Proofs.Field.Inverse.SafeGcd.Core.Prepare.Frame
import P256.Proofs.Field.Inverse.SafeGcd.Core.Update.Pointer
import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Update.Memory
import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Update.ModularDefs

namespace P256.Proofs.Verifying.Core.Inverse.SafeGcd.Update

open P256.Proofs.Field.Inverse.SafeGcd
open P256.Proofs.Field.Inverse.SafeGcd.Core.Shared
open P256.Proofs.Field.Inverse.SafeGcd.Core.Shared.Batch
open P256.Proofs.Field.Inverse.SafeGcd.Core

open P256.Proofs.Field.Inverse.SafeGcd.Core.Support (MemoryStable atom_of_frame atoms_of_frame)

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

set_option maxRecDepth 4096 in
set_option maxHeartbeats 600000 in
theorem fourth_call [Bindings] {code : CodeMap}
    (hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    {initial : RamState} {fr : Activation} {controls : RamState} {p : Inputs} {s : LoopState} {boundary : ReturnBoundary}
    (hready : EntryReady code initial) (hrip : initial.RIP = 0x1116c0)
    (hframe : RamWriteFrame fr.original initial.external [fr.region, outputRegion fr])
    (hout : ReturnOutside boundary code)
    (hcore : Atom.All code (Machine.lifted.locationOf .l1171a0 initial).arguments
      initial.external (fourthCall fr controls p s)) :
    ∃ fuel final, Advances boundary fuel initial final ∧ EntryReady code final ∧
      final.RIP = 0x112463 ∧
      RamWriteFrame fr.original final.external [fr.region, outputRegion fr] ∧
      Atom.All code (Machine.lifted.locationOf .l1144b3 final).arguments final.external
        (fourthReturned fr controls p s) := by
  simp only [fourthCall, Atom.all_append] at hcore
  obtain ⟨⟨⟨⟨hmem, hb⟩, hpres⟩, hfirst⟩, hargs⟩ := hcore
  have hstable := memory_stable hmem
  have hm := hmem
  simp only [memoryAtoms, commonAtoms, outputAtoms, inputAtoms, savedInputAtoms,
    stateAtoms, signedAtoms, CopyFG.fgState, Atom.all_append, Atom.All, Atom.Holds] at hm
  obtain ⟨⟨⟨⟨⟨_, _, _, _, _, _, _, hretread, _, hw, hroom, halign, _, _, _, _⟩,
    _, _, hmodw, _, _, hmodread, _, _, hmodsep, _, hinv, _⟩, _⟩,
    ⟨⟨_, hfw, hfs, _⟩, hgw, hgs, _⟩⟩, _⟩ := hm
  simp only [modularPreserved, Atom.All, Atom.Holds, Lifted.locationOf,
    Fin.getElem_fin, Vector.getElem_ofFn] at hpres
  obtain ⟨hrsp, hdf, hrbx, hrbp, hr12, hr13, hr14, hr15, hmx, hfc, _⟩ := hpres
  simp only [Atom.All, Atom.Holds, Lifted.locationOf,
    Fin.getElem_fin, Vector.getElem_ofFn] at hargs
  obtain ⟨hrdi, hrsi, hrdx, hrcx, hr8, hr9, hret, hslot, hmodslot, hinvslot, _⟩ := hargs
  have hsp : stackPtr initial = fr.rsp - 0x1a0 := Value.eq_bits hrsp
  have hdi : initial.regValue .rdi = fr.rsp - 0xb0 := Value.eq_bits hrdi
  have hsi : initial.regValue .rsi = fr.rsp - 0x128 := Value.eq_bits hrsi
  have hdx : initial.regValue .rdx = fr.rsp - 0x100 := Value.eq_bits hrdx
  have hcx : initial.regValue .rcx = (batchResult s).q := Value.eq_bits hrcx
  have h8 : initial.regValue .r8 = (batchResult s).r := Value.eq_bits hr8
  have h9 : initial.regValue .r9 = (BitVec.ofNat 32 (batchCount s)).setWidth 64 := Value.eq_bits hr9
  have hret' : (returnBoundary initial).rip = 0x112463 := by
    change memLoad initial.external (stackPtr initial) 64 = _
    rwa [hsp]
  have hwindow : Writable code initial.external (stackPtr initial - 0x120) 0x120 := by
    rw [hsp]; exact hw.sub (by bv_omega) (by bv_omega)
  have hentry := Core.Support.activation_entryAtoms ModularShift.Machine.Modular.frameInfo
    ModularShift.Machine.lifted .l1171a0 rfl (by rw [hret']; decide)
    (by rw [hsp]; exact hslot.sub (by bv_omega) (by bv_omega)) hwindow (by change 0x120 ≤ (stackPtr initial).toNat; rw [hsp]; bv_omega)
    (by rw [hsp]; bv_omega) (Reg.read_df_iff.1 hdf)
  have hc : (BitVec.ofNat 32 (batchCount s)).toNat = batchCount s := by
    rw [BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    simp only [batchCount]
    omega
  have hinput : Atom.All code (ModularShift.Machine.lifted.locationOf .l1171a0 initial).arguments
      initial.external (ModularShift.entryAtoms (Core.Support.activation initial 0x120) controls (eCallInput fr p s)) := by
    simp only [ModularShift.entryAtoms, Atom.all_append]
    refine ⟨⟨⟨⟨⟨hentry, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · simp only [ModularShift.outputAtoms, Core.Support.activation, Atom.All, Atom.Holds, Lifted.locationOf, Fin.getElem_fin, Vector.getElem_ofFn]
      rw [hdi, hsp]
      exact ⟨hmx, hfc, hw.sub (by bv_omega) (by bv_omega), Or.inr (by bv_omega), trivial⟩
    · simp only [ModularShift.inputAtoms, Core.Support.activation, eCallInput, eInput, linearInput, Atom.All, Atom.Holds]
      rw [hsi, hdx, hsp, hcx, h8]
      exact ⟨hfw, hgw, hfs, hgs,
        (hw.sub (by bv_omega) (by bv_omega)).readable,
        (hw.sub (by bv_omega) (by bv_omega)).readable,
        Or.inr (by bv_omega), Or.inr (by bv_omega), rfl, rfl, trivial⟩
    · simp only [ModularShift.bounds, eCallInput, eInput, Atom.All, Atom.Holds, hc]
      have hp := hb.1
      change 1 ≤ s.remaining at hp
      exact ⟨by simp only [batchCount]; omega, by simp only [batchCount]; omega, trivial⟩
    · simp only [Atom.All, Atom.Holds, Core.Support.activation, eCallInput, eInput, h9]
      exact ⟨by bv_omega, trivial⟩
    · simp only [ModularShift.modulusAtoms, eCallInput, eInput, Core.Support.activation, Atom.All, Atom.Holds]
      rw [hsp]
      refine ⟨hmodw, hmodread, ?_, ?_, ?_, ?_, trivial⟩
      · rcases hmodsep with h | h
        · left; bv_omega
        · right; bv_omega
      · simpa only [show fr.rsp - 0x1a0 + 8 = fr.rsp - 0x198 by bv_omega] using hmodslot
      · simpa only [show fr.rsp - 0x1a0 + 16 = fr.rsp - 0x190 by bv_omega, hinv] using hinvslot
      · exact hslot.sub (by bv_omega) (by bv_omega)
  have hretCode : ∃ b, (0x112463, b) ∈ code :=
    ⟨_, hcode _ (Machine.code_l1144b3 _ (mem_codeRange _ _ 0 (by decide)))⟩
  obtain ⟨fuel, final, he, ready, hp, hwout, hsout, hrout, mx, fc⟩ := ModularShift.advances hcode hready hrip
    (fr := Core.Support.activation initial 0x120) (RamWriteFrame.refl _ _) hout
    (Or.inl (by change (returnBoundary initial).rip ≠ boundary.rip
                rw [hret']; exact ReturnOutside.ne hout hretCode)) hinput
  have hwithin : RegionsWithin [(Core.Support.activation initial 0x120).region,
      ModularShift.outputRegion (Core.Support.activation initial 0x120)] (updateRegions fr) := by
    intro r hh
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl
    · refine ⟨({ start := (fr.rsp - 0x2c0).toNat, size := 0x138 } : MemoryRegion), by simp [updateRegions], ?_, ?_⟩
      all_goals simp only [Activation.region, Core.Support.activation, hsp]
      all_goals bv_omega
    · refine ⟨({ start := (fr.rsp - 0xd8).toNat, size := 0x50 } : MemoryRegion), by simp [updateRegions], ?_, ?_⟩
      all_goals simp only [ModularShift.outputRegion, Core.Support.activation, hdi]
      all_goals bv_omega
  have hmidframe := (RamWriteFrame.refl initial.external (updateRegions fr)).trans hp.frame hwithin
  have hmem' := atoms_of_frame (args' := (Machine.lifted.locationOf .l1144b3 final).arguments)
    hmidframe (memoryAtoms fr p (CopyFG.fgState s)) hstable hmem
  have houter : RegionsWithin (updateRegions fr) [fr.region, outputRegion fr] := by
    intro r hh
    simp only [updateRegions, List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl
    all_goals refine ⟨fr.region, by simp, ?_, ?_⟩
    all_goals simp only [Activation.region]
    all_goals bv_omega
  have hspFinal := hp.rsp
  change (Reg.ofIndex 4).read final = ⟨64, stackPtr initial + 8⟩ at hspFinal
  rw [show stackPtr initial + 8 = fr.rsp - 0x198 by rw [hsp]; bv_omega] at hspFinal
  change WordsAt final.external (initial.regValue .rdi) 64 _ at hwout
  change memLoad final.external (initial.regValue .rdi + 32) 8 = _ at hsout
  change Readable final.external (initial.regValue .rdi) 33 at hrout
  simp only [eCallInput, ModularShift.resultWords_withPtr] at hwout
  simp only [eCallInput, ModularShift.resultSign_withPtr] at hsout
  rw [hdi] at hwout hsout hrout
  rw [show fr.rsp - 0xb0 + 32 = fr.rsp - 0x90 by bv_omega] at hsout
  have hfirstStable : ∀ a ∈ thirdResult fr p s, MemoryStable
      [(Core.Support.activation initial 0x120).region,
        ModularShift.outputRegion (Core.Support.activation initial 0x120)] a := by
    have hl := hretread.low
    simp only [thirdResult, List.not_mem_nil,
      MemoryStable, Vector.size, Nat.reduceDiv, Nat.reduceMul, Nat.reduceLT, true_and,
      and_true, Outside, List.mem_cons, or_false, forall_eq_or_imp, forall_eq,
      Activation.region, ModularShift.outputRegion, Core.Support.activation, hsp, hdi]
    repeat' apply And.intro
    all_goals bv_omega
  have hfirst' := atoms_of_frame (args' := (Machine.lifted.locationOf .l1144b3 final).arguments)
    hp.frame (thirdResult fr p s) hfirstStable hfirst
  have hb' : Atom.All code (Machine.lifted.locationOf .l1144b3 final).arguments
      final.external (bounds s) := by
    change 1 ≤ s.remaining ∧ s.remaining ≤ 591 ∧ True
    exact ⟨hb.1, hb.2.1, trivial⟩
  refine ⟨fuel, final, he, ready, hp.rip.trans hret', hframe.trans hmidframe houter, ?_⟩
  simp only [fourthReturned, Atom.all_append]
  refine ⟨⟨⟨⟨hmem', hb'⟩, ?_⟩, hfirst'⟩, hwout, hsout, hrout, trivial⟩
  simp only [modularPreserved, Atom.All, Atom.Holds, Lifted.locationOf,
    Fin.getElem_fin, Vector.getElem_ofFn]
  exact ⟨hspFinal, Reg.read_df_iff.2 hp.df,
    (hp.preserved 3 (by decide)).trans hrbx, (hp.preserved 5 (by decide)).trans hrbp,
    (hp.preserved 12 (by decide)).trans hr12, (hp.preserved 13 (by decide)).trans hr13,
    (hp.preserved 14 (by decide)).trans hr14, (hp.preserved 15 (by decide)).trans hr15,
    congrArg (Value.mk 32) mx, congrArg (Value.mk 16) fc, trivial⟩

end P256.Proofs.Verifying.Core.Inverse.SafeGcd.Update
