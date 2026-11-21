import K256.Proofs.Verify.Core.Lincomb.Prepare.Bases.State

namespace K256.Proofs.Verify.Core.Lincomb.Prepare

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine

def BelowSaved (sp : BitVec 64) (regions : List MemoryRegion) : Prop :=
  ∀ r ∈ regions, sp.toNat - 0x558 ≤ r.start ∧ r.start + r.size ≤ sp.toNat - 48

variable {a b c : Registers} {m n o : Ram} {sp tables digits : BitVec 64} {k : Nat}
  {regions : List MemoryRegion}

theorem savedFrameAfter (entry : RoutineEntry a m sp 0x558) (old : SavedFrame a sp tables b n)
    (frame : RamWriteFrame n o regions) (bounds : BelowSaved sp regions)
    (rsp : c[4] = ⟨64,frameSp sp⟩) (table : c[3] = b[3])
    (widths : ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15] → c[i].width = 64)
    (ctl : ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → c[i] = b[i]) :
    SavedFrame a sp tables c o := by
  have room := entry.room
  have high := entry.returnSlot.low
  have keep (off : Nat) (lo : 8 ≤ off) (hi : off ≤ 48) :
      memLoad o (sp - BitVec.ofNat 64 off) 64 = memLoad n (sp - BitVec.ofNat 64 off) 64 := by
    apply frame.memLoad_eq
    have eq : (sp - BitVec.ofNat 64 off).toNat = sp.toNat - off := by
      rw [BitVec.toNat_sub_of_le, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      apply BitVec.le_def.mpr
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    refine ⟨by rw [eq]; omega, fun r hr => Or.inr ?_⟩
    have := bounds r hr
    rw [eq]
    omega
  exact ⟨rsp,table.trans old.tableBase,widths,fun i hi => (ctl i hi).trans (old.control i hi),
    (keep 48 (by decide) (by decide)).trans old.rbx, (keep 40 (by decide) (by decide)).trans old.r12,
    (keep 32 (by decide) (by decide)).trans old.r13, (keep 24 (by decide) (by decide)).trans old.r14,
    (keep 16 (by decide) (by decide)).trans old.r15, (keep 8 (by decide) (by decide)).trans old.rbp⟩

theorem signedFrameAfter (entry : RoutineEntry a m sp 0x558) (old : SignedFrame a m sp tables digits k b n)
    (digitsWrite : Writable Extracted.programImage m digits 544)
    (digitsApart : Outside [scratch sp 0x558, ⟨sp.toNat, 8⟩] digits 544)
    (frame : RamWriteFrame n o regions) (bounds : BelowSaved sp regions)
    (rsp : c[4] = ⟨64,frameSp sp⟩) (table : c[3] = b[3])
    (widths : ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15] → c[i].width = 64)
    (ctl : ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → c[i] = b[i]) :
    SignedFrame a m sp tables digits k c o := by
  have room := entry.room
  have high := digitsWrite.readable.low
  have apart := digitsApart.2 _ (List.mem_cons_self ..)
  change digits.toNat + 544 ≤ sp.toNat - 1368 ∨ sp.toNat - 1368 + 1368 ≤ digits.toNat at apart
  have within : RegionsWithin regions [scratch sp 0x558, ⟨digits.toNat,544⟩] := by
    intro r hr
    have h := bounds r hr
    exact ⟨_,List.mem_cons_self .., h.1, by dsimp only [scratch]; omega⟩
  have keep (ptr : BitVec 64) (w : Nat) (lo : digits.toNat ≤ ptr.toNat)
      (hi : ptr.toNat + w/8 ≤ digits.toNat + 544) : memLoad o ptr w = memLoad n ptr w := by
    apply frame.memLoad_eq
    refine ⟨by omega, fun r hr => ?_⟩
    have h := bounds r hr
    omega
  refine ⟨savedFrameAfter entry old.toSavedFrame frame bounds rsp table widths ctl,
    old.frame.trans frame within,(keep _ _ (by omega) (by omega)).trans old.firstLength,
    (keep _ _ ?_ ?_).trans old.secondLength,?_,?_⟩
  · simp only [BitVec.toNat_add, BitVec.reduceToNat]; omega
  · simp only [BitVec.toNat_add, BitVec.reduceToNat]; omega
  all_goals
    intro i
    first | apply Eq.trans (keep _ _ _ _) (old.firstBytes i) | apply Eq.trans (keep _ _ _ _) (old.secondBytes i)
    all_goals simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]; omega

end K256.Proofs.Verify.Core.Lincomb.Prepare
