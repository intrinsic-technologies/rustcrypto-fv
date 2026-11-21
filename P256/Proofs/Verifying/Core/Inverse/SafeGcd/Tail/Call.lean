import P256.Proofs.Field.Inverse.SafeGcd.Core.Tail.Defs
import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Tail.Defs

namespace P256.Proofs.Verifying.Core.Inverse.SafeGcd.Tail

open P256.Proofs.Field.Inverse.SafeGcd.Core.Shared (zeroWords correctionInput)

open P256.Proofs.Field.Inverse.SafeGcd

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

def callRegions (fr : Activation) : List MemoryRegion :=
  [⟨(fr.rsp - 0x1c8).toNat, 0x38⟩, ⟨fr.rdi.toNat, 32⟩]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 600000 in
theorem resident_stable {code : CodeMap} {args : Values Value Reg.count} {mem : Ram}
    {fr : Activation} {s : LoopState}
    (h : Atom.All code args mem (residentAtoms fr s)) :
    ∀ a ∈ residentAtoms fr s, Core.Support.MemoryStable (callRegions fr) a := by
  simp only [residentAtoms, savedAtoms, outputAtoms, signedAtoms, Atom.all_append,
    Atom.All, Atom.Holds] at h
  obtain ⟨⟨⟨_, _, _, _, _, _, _, hread, _, hw, hroom, _, _⟩,
    hout, hsep, _⟩, _⟩ := h
  have hrl := hread.low
  have hol := hout.readable.low
  simp only [residentAtoms, savedAtoms, outputAtoms, signedAtoms, List.forall_mem_append,
    List.not_mem_nil, Core.Support.MemoryStable, and_true, Vector.size,
    Nat.reduceDiv, Nat.reduceMul, Nat.reduceLT, true_and, Outside, callRegions,
    List.mem_cons, or_false, forall_eq_or_imp, forall_eq]
  repeat' apply And.intro
  all_goals first | omega | bv_omega

set_option maxRecDepth 4096 in
set_option maxHeartbeats 600000 in
theorem correction_call [Bindings] {code : CodeMap}
    (hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    {initial : RamState} {fr : Activation} {controls : RamState} {p : Inputs} {s : LoopState} {boundary : ReturnBoundary}
    (hready : EntryReady code initial) (hrip : initial.RIP = 0x1126c0)
    (hframe : RamWriteFrame fr.original initial.external [fr.region, outputRegion fr])
    (hout : ReturnOutside boundary code)
    (hcore : Atom.All code (Machine.lifted.locationOf .l1181a0 initial).arguments
      initial.external (callAtoms fr controls p s)) :
    ∃ fuel final, Advances boundary fuel initial final ∧ EntryReady code final ∧
      final.RIP = 0x112689 ∧
      RamWriteFrame fr.original final.external [fr.region, outputRegion fr] ∧
      Atom.All code (Machine.lifted.locationOf .l1146d9 final).arguments final.external
        (returnedAtoms fr controls p s) := by
  simp only [callAtoms, Atom.all_append] at hcore
  obtain ⟨hresident, hargs⟩ := hcore
  have hstable := resident_stable hresident
  have hm := hresident
  simp only [residentAtoms, savedAtoms, outputAtoms, signedAtoms,
    Atom.all_append, Atom.All, Atom.Holds] at hm
  obtain ⟨⟨⟨_, _, _, _, _, _, _, hread, _, hw, hroom, halign, _⟩,
    houtw, houtsep, _⟩, _⟩ := hm
  simp only [Atom.All, Atom.Holds, Lifted.locationOf,
    Fin.getElem_fin, Vector.getElem_ofFn] at hargs
  obtain ⟨hdw, hds, hmw, hmr, hmsep, hrsp, hdf, hrbl, hr14,
    hrdi, hrsi, hrcx, hrdl, hret, hslot, hmx, hfc, _⟩ := hargs
  have hsp : stackPtr initial = fr.rsp - 0x190 := Value.eq_bits hrsp
  have hdi : initial.regValue .rdi = fr.rdi := Value.eq_bits hrdi
  have hsi : initial.regValue .rsi = fr.rsp - 0x128 := Value.eq_bits hrsi
  have hcx : initial.regValue .rcx = fr.rdx := Value.eq_bits hrcx
  have hdl : (initial.regValue .rdx).setWidth 8 = s.f.sign := hrdl
  have hret' : (returnBoundary initial).rip = 0x112689 := by
    change memLoad initial.external (stackPtr initial) 64 = _
    rwa [hsp]
  have hwindow : Writable code initial.external (stackPtr initial - 0x38) 0x38 := by
    rw [hsp]
    exact hw.sub (by bv_omega) (by bv_omega)
  have hentry := Core.Support.activation_entryAtoms Correction.Execution.Machine.Correction.frameInfo
    Correction.Execution.Machine.lifted .l1181a0 rfl (by rw [hret']; decide)
    (by rw [hsp]; exact hslot) hwindow
    (by change 0x38 ≤ (stackPtr initial).toNat; rw [hsp]; bv_omega)
    (by rw [hsp]; bv_omega) (Reg.read_df_iff.1 hdf)
  let cp : Correction.Inputs := { correctionInput p s with negate := initial.regValue .rdx }
  have hinput : Atom.All code (Correction.Execution.Machine.lifted.locationOf .l1181a0 initial).arguments
      initial.external (Correction.Execution.Machine.Correction.frameAt .l1181a0
        (Core.Support.activation initial 0x38) ++ Correction.Execution.commonAtoms (Core.Support.activation initial 0x38) controls cp) := by
    rw [Atom.all_append]
    refine ⟨hentry, ?_⟩
    simp only [Correction.Execution.commonAtoms, Core.Support.activation, cp, correctionInput, Atom.All, Atom.Holds, Lifted.locationOf, Fin.getElem_fin, Vector.getElem_ofFn]
    rw [hdi, hsi, hcx, hsp]
    refine ⟨hmx, hfc, houtw.sub (by omega) (by omega), ?_, hdw, hmw, ?_,
      (hw.sub (by bv_omega) (by bv_omega)).readable, hmr, ?_, ?_, trivial, trivial⟩
    · rcases houtsep with h | h
      · left; bv_omega
      · right; bv_omega
    · simpa only [show fr.rsp - 0x128 + 32 = fr.rsp - 0x108 by bv_omega] using hds
    · right; bv_omega
    · rcases hmsep with h | h
      · left; bv_omega
      · right; bv_omega
  have hretCode : ∃ b, (0x112689, b) ∈ code :=
    ⟨_, hcode _ (Machine.code_l1146d9 _ (mem_codeRange _ _ 0 (by decide)))⟩
  obtain ⟨fuel, final, he, ready, hp, hwout, hrout, mx, fc⟩ := Correction.Execution.correction_advances hcode
    hready hrip (fr := Core.Support.activation initial 0x38) (RamWriteFrame.refl _ _) hout
    (Or.inl (by change (returnBoundary initial).rip ≠ boundary.rip
                rw [hret']; exact ReturnOutside.ne hout hretCode)) hinput
  have hwithin : RegionsWithin [(Core.Support.activation initial 0x38).region,
      Correction.Execution.outputRegion (Core.Support.activation initial 0x38)] (callRegions fr) := by
    intro r hh
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl
    · refine ⟨({start := (fr.rsp - 0x1c8).toNat, size := 0x38} : MemoryRegion), by simp [callRegions], ?_, ?_⟩
      all_goals simp only [Activation.region, Core.Support.activation, hsp]
      all_goals bv_omega
    · refine ⟨({start := fr.rdi.toNat, size := 32} : MemoryRegion), by simp [callRegions], ?_, ?_⟩
      all_goals simp only [Correction.Execution.outputRegion, Core.Support.activation, hdi]
      all_goals omega
  have hmidframe := (RamWriteFrame.refl initial.external (callRegions fr)).trans hp.frame hwithin
  have hresident' := Core.Support.atoms_of_frame
    (args' := (Machine.lifted.locationOf .l1146d9 final).arguments)
    hmidframe (residentAtoms fr s) hstable hresident
  have houter : RegionsWithin (callRegions fr) [fr.region, outputRegion fr] := by
    intro r hh
    simp only [callRegions, List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl
    · refine ⟨fr.region, by simp, ?_, ?_⟩
      all_goals simp only [Activation.region]
      all_goals bv_omega
    · exact ⟨outputRegion fr, by simp, Nat.le_refl _, by change fr.rdi.toNat+32 ≤ fr.rdi.toNat+33; omega⟩
  have hspFinal := hp.rsp
  change (Reg.ofIndex 4).read final = ⟨64, stackPtr initial + 8⟩ at hspFinal
  rw [show stackPtr initial + 8 = fr.rsp - 0x188 by rw [hsp]; bv_omega] at hspFinal
  have heq : Correction.correctedWords cp = Correction.correctedWords (correctionInput p s) := by
    apply Core.Tail.correction_negate
    change (initial.regValue .rdx).setWidth 8 = (s.f.sign.setWidth 64).setWidth 8
    rw [hdl]
    bv_omega
  change WordsAt final.external (initial.regValue .rdi) 64 (Correction.correctedWords cp) at hwout
  change Readable final.external (initial.regValue .rdi) 32 at hrout
  rw [hdi, heq] at hwout
  rw [hdi] at hrout
  refine ⟨fuel, final, he, ready, hp.rip.trans hret', hframe.trans hmidframe houter, ?_⟩
  simp only [returnedAtoms, Atom.all_append]
  refine ⟨hresident', ?_⟩
  simp only [Atom.All, Atom.Holds, Lifted.locationOf, Fin.getElem_fin, Vector.getElem_ofFn]
  refine ⟨hspFinal, Reg.read_df_iff.2 hp.df, ?_,
    (hp.preserved 14 (by decide)).trans hr14, hwout, hrout, congrArg (Value.mk 32) mx, congrArg (Value.mk 16) fc, trivial⟩
  have hb : final.regValue .rbx = initial.regValue .rbx := Value.eq_bits (hp.preserved 3 (by decide))
  change (final.regValue .rbx).setWidth 8 = _
  exact (congrArg (fun x : BitVec 64 => x.setWidth 8) hb).trans hrbl

end P256.Proofs.Verifying.Core.Inverse.SafeGcd.Tail
