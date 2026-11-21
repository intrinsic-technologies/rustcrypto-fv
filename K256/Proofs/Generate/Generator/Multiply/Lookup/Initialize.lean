import K256.Proofs.Sec1.Wrapper.Copy.Execution
import K256.Proofs.Generate.Generator.Multiply.Lookup.Memory
import K256.Proofs.Generate.Generator.Multiply.Lookup.Choice
import K256.Proofs.Generate.Generator.Multiply.Lookup.Digit

namespace K256.Proofs.Generate.Generator.Multiply.Lookup

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Field
  Standards.SECG.ECC

private def savedStack (fr : Activation) (m : Ram) : Ram :=
  let m := memStore m (fr.rsp - 8) fr.rbp
  let m := memStore m (fr.rsp - 16) fr.r15
  let m := memStore m (fr.rsp - 24) fr.r14
  let m := memStore m (fr.rsp - 32) fr.r13
  let m := memStore m (fr.rsp - 40) fr.r12
  memStore m (fr.rsp - 48) fr.rbx

private def copiedStack (fr : Activation) (m : Ram) : Ram :=
  memCopy (savedStack fr m) (fr.rsp - 408) 0x203258 120

private theorem lookup_call {fr : Activation} {a : Registers} {m : Ram}
    (rsp : a[4] = ⟨64, fr.rsp⟩) (df : a[22] = ⟨1, 0⟩)
    (dx : a[2] = ⟨64, fr.rdx⟩) (di : a[7] = ⟨64, fr.rdi⟩) (si : a[6] = ⟨64, fr.rsi⟩)
    (bp : a[5] = ⟨64, fr.rbp⟩) (r15 : a[15] = ⟨64, fr.r15⟩)
    (r14 : a[14] = ⟨64, fr.r14⟩) (r13 : a[13] = ⟨64, fr.r13⟩)
    (r12 : a[12] = ⟨64, fr.r12⟩) (bx : a[3] = ⟨64, fr.rbx⟩)
    (win : Writable Extracted.programImage m (fr.rsp - 496) 496)
    (copy : RepMovsOk Extracted.programImage (savedStack fr m) 0 0x203258 (fr.rsp - 408) 15 8 0x11c53b 3)
    (push : StoreOk Extracted.programImage (copiedStack fr m) (fr.rsp - 416) 8 0x11c556 5) :
    ∃ b : Registers,
      program.runBlock (dialect Extracted.programImage) ⟨.l11c510, a, m⟩ =
        .call ⟨.l127d50, b, memStore (copiedStack fr m) (fr.rsp - 408 - 8) (0x11c55b : Word)⟩
          (callFrame .l11c55b 0x11c55b) ∧
      b[4].get 64 = fr.rsp - 408 - 8 ∧ b[3] = ⟨64, fr.rdi⟩ ∧
      (b[5].get 64).setWidth 8 = fr.rdx.setWidth 8 ∧
      (b[13].get 64).setWidth 8 = magnitude (fr.rdx.setWidth 8) ∧
      (b[7].get 64).setWidth 8 = (if magnitude (fr.rdx.setWidth 8) = 1 then 1 else 0) ∧
      b[14].get 64 = fr.rsp - 408 ∧ b[15].get 64 = fr.rsi ∧
      b[22] = ⟨1, 0⟩ ∧ b[39] = a[39] ∧ b[50] = a[50] ∧ b[51] = a[51] := by
  dsimp only [savedStack] at copy
  dsimp only [copiedStack, savedStack] at push
  refine ⟨?_, ?run, ?post⟩
  case run =>
    arithmetic_segment using code_l11c510 [rsp, df, dx, di, si, bp, r15, r14, r13, r12, bx,
      BitVec.sub_sub, copy, push, false_or]
  case post =>
    refine ⟨?_, rfl, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rw [BitVec.sub_sub]
      rfl
    · change ((fr.rdx.setWidth 32).setWidth 64).setWidth 8 = fr.rdx.setWidth 8
      simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),
        BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32)]
    all_goals
      change (mergeGPR 8 _ _).setWidth 8 = _
      simp only [setWidth_mergeGPR8, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),
        BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32), magnitude]
      try rfl

private theorem identityImage (a : Word) (lo : (0x203258 : Nat) ≤ a.toNat)
    (hi : a.toNat < 0x203258 + 120) : Common.InImage a := by
  apply exists_mem_toCodeMap (s := rodataSection)
  · simp [rodataSection, Extracted.programSections]
  · change 0x200000 ≤ a.toNat
    omega
  · change a.toNat < 0x200000 + Extracted.rodataBytes.size
    rw [Common.rodataBytes_size]
    omega

private theorem identityReadable {m : Ram} (image : ∀ b ∈ Extracted.programImage, m[b.1]? = some b.2) :
    Readable m 0x203258 120 := by
  refine ⟨by decide, fun i hi => ?_⟩
  have addr : ((0x203258 : Word) + BitVec.ofNat 64 i).toNat = 0x203258 + i := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    change (2110040 + i % (2^64)) % (2^64) = 2110040 + i
    omega
  obtain ⟨b, hb⟩ := identityImage ((0x203258 : Word) + BitVec.ofNat 64 i) (by rw [addr]; omega)
    (by rw [addr]; omega)
  rw [image _ hb]
  rfl

private theorem identityOutside {fr : Activation} {m : Ram}
    (win : Writable Extracted.programImage m (fr.rsp - 496) 496) :
    Outside [window fr] 0x203258 120 := by
  refine ⟨by decide, ?_⟩
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  rw [or_comm]
  apply apart_of_avoids (forbidden := Common.InImage) (lo := 0x203258) (hi := 0x203258 + 120) ?_
    identityImage (by change 0 < 496; decide) (by decide) (by decide)
  intro a ha hImage
  obtain ⟨b, hb⟩ := hImage
  let base := fr.rsp - 496
  change base.toNat ≤ a.toNat ∧ a.toNat < base.toNat + 496 at ha
  have i : a.toNat - base.toNat < 496 := by omega
  apply win.notCode (a, b) hb (a.toNat - base.toNat) i
  apply BitVec.eq_of_toNat_eq
  change a.toNat = (base + BitVec.ofNat 64 (a.toNat - base.toNat)).toNat
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  have low := win.readable.low
  change base.toNat + 496 ≤ 2^32 at low
  rw [Nat.mod_eq_of_lt (by omega : a.toNat - base.toNat < 2^64), Nat.mod_eq_of_lt (by omega)]
  omega

set_option maxRecDepth 1024 in
theorem startScan {fr : Activation} {a : Registers} {m : Ram} {digit : Int}
    (atoms : Atom.All Extracted.programImage a m (Fn11c510.frameAt .l11c510 fr))
    (image : ∀ b ∈ Extracted.programImage, m[b.1]? = some b.2)
    (bounds : -8 ≤ digit ∧ digit ≤ 8)
    (index : fr.rdx.setWidth 8 = BitVec.ofInt 8 digit) :
    ∃ b n, Reaches .l11c510 a m (stage 0) b n ∧ Scanning fr m digit 0 b n identity := by
  simp only [Fn11c510.frameAt, Fn11c510.frameAtG1, Atom.All, Atom.Holds] at atoms
  obtain ⟨rsp, df, _, dx, bx, bp, si, di, _, _, r12, r13, r14, r15, mx, ft, fc,
    readableRet, ret, retLow, win, room, align, _⟩ := atoms
  have room' : 496 ≤ fr.rsp.toNat := by omega
  have stackNat (off : Word) (hs : off.toNat ≤ 496) :
      (fr.rsp - off).toNat = fr.rsp.toNat - off.toNat :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))
  have stackLow := readableRet.low
  have winLow := win.readable.low
  have inside {off : Word} {len : Nat} (hs : off.toNat ≤ 496) (hl : len ≤ off.toNat) :
      InRegions [window fr] (fr.rsp - off) len := by
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    change (fr.rsp - 496).toNat ≤ (fr.rsp - off).toNat ∧
      (fr.rsp - off).toNat + len ≤ (fr.rsp - 496).toNat + 496 ∧
      (fr.rsp - off).toNat + len ≤ 2^64
    rw [stackNat off hs, stackNat 496 (by decide)]
    simp only [BitVec.reduceToNat]
    omega
  have savedWrites : RamWriteFrame m (savedStack fr m) [window fr] := by
    unfold savedStack
    repeat' refine RamWriteFrame.memStore ?_ _ (inside (by decide) (by decide))
    exact RamWriteFrame.refl _ _
  have savedWin : Writable Extracted.programImage (savedStack fr m) (fr.rsp - 496) 496 :=
    win.of_frame savedWrites
  have copiedWin : Writable Extracted.programImage (copiedStack fr m) (fr.rsp - 496) 496 := by
    exact savedWin.memStore _ _
  have loadConst := (identityReadable image).of_frame savedWrites
  have outside := identityOutside win
  have hcopy : RepMovsOk Extracted.programImage (savedStack fr m) 0 0x203258 (fr.rsp - 408) 15 8 0x11c53b 3 := by
    apply copyGuard loadConst (by slot_guard using code_l11c510)
    have or := outside.2 _ (List.mem_singleton_self _)
    change 2110040 + 120 ≤ (fr.rsp - 496).toNat ∨ (fr.rsp - 496).toNat + 496 ≤ 2110040 at or
    change 2110040 + 120 ≤ (fr.rsp - 408).toNat ∨ (fr.rsp - 408).toNat + 120 ≤ 2110040
    rw [stackNat 496 (by decide)] at or
    simp only [BitVec.reduceToNat] at or
    rw [stackNat 408 (by decide)]
    simp only [BitVec.reduceToNat]
    omega
  have hpush : StoreOk Extracted.programImage (copiedStack fr m) (fr.rsp - 416) 8 0x11c556 5 := by
    slot_guard using code_l11c510
  obtain ⟨b, call, brsp, bdst, bdigit, bmag, bflag, bacc, btable, bdf, bmx, bft, bfc⟩ :=
    lookup_call rsp df dx di si bp r15 r14 r13 r12 bx win hcopy hpush
  have slotAddr : fr.rsp - 408 - 8 = fr.rsp - 416 := by bv_omega
  have tmpAddr : fr.rsp - 408 - 8 - 1 = fr.rsp - 417 := by bv_omega
  have tmp : Writable Extracted.programImage (copiedStack fr m) (fr.rsp - 417) 1 := by
    slot_state region
  have slot : Readable (copiedStack fr m) (fr.rsp - 416) 8 := by
    slot_state region
  obtain ⟨c, n, reach, crsp, flag, postFrame, preserved⟩ := resumeChoice call brsp
    (tmpAddr.symm ▸ tmp) (slotAddr.symm ▸ slot) (by decide)
  rw [tmpAddr, slotAddr] at postFrame
  let extra : MemoryRegion := ⟨(fr.rsp - 417).toNat, 9⟩
  let init : MemoryRegion := ⟨(fr.rsp - 417).toNat, 129⟩
  have pushed : RamWriteFrame (copiedStack fr m)
      (memStore (copiedStack fr m) (fr.rsp - 416) (0x11c55b : Word)) [extra] := by
    apply (RamWriteFrame.refl _ _).memStore
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    change (fr.rsp - 417).toNat ≤ (fr.rsp - 416).toNat ∧
      (fr.rsp - 416).toNat + 8 ≤ (fr.rsp - 417).toNat + 9 ∧
      (fr.rsp - 416).toNat + 8 ≤ 2^64
    rw [stackNat 417 (by decide), stackNat 416 (by decide)]
    simp only [BitVec.reduceToNat]
    omega
  have extraWrites : RamWriteFrame (copiedStack fr m) n [extra] := by
    apply pushed.trans postFrame
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨extra, List.mem_singleton_self _, Nat.le_refl _, by dsimp only [extra]; omega⟩
  have copied : RamWriteFrame (savedStack fr m) (copiedStack fr m) [init] := by
    apply Sec1.Wrapper.Copy.memCopy_frame (RamWriteFrame.refl _ _)
    refine ⟨init, List.mem_singleton_self _, ?_⟩
    change (fr.rsp - 417).toNat ≤ (fr.rsp - 408).toNat ∧
      (fr.rsp - 408).toNat + 120 ≤ (fr.rsp - 417).toNat + 129 ∧
      (fr.rsp - 408).toNat + 120 ≤ 2^64
    rw [stackNat 417 (by decide), stackNat 408 (by decide)]
    simp only [BitVec.reduceToNat]
    omega
  have initWrites : RamWriteFrame (savedStack fr m) n [init] := by
    apply copied.trans extraWrites
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨init, List.mem_singleton_self _, Nat.le_refl _, by dsimp only [extra, init]; omega⟩
  have fullFrame : RamWriteFrame m n [window fr] := by
    apply savedWrites.trans initWrites
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    obtain ⟨r, hr, hin⟩ := inside (off := 417) (len := 129) (by decide) (by decide)
    exact ⟨r, hr, hin.1, hin.2.1⟩
  have preRet : memLoad (savedStack fr m) fr.rsp 64 = fr.ret := by
    dsimp only [savedStack]
    simpa (disch := store_disch) only [store_norm] using ret
  have savedAtoms : Atom.All Extracted.programImage c (savedStack fr m) (Fn11c510.frameAt .l11c6ed fr) := by
    simp only [Fn11c510.frameAt, Fn11c510.frameAtG1, Atom.All, Atom.Holds]
    refine ⟨crsp, (preserved 22 (by decide)).trans bdf, (preserved 3 (by decide)).trans bdst,
      (preserved 39 (by decide)).trans (bmx.trans mx), (preserved 50 (by decide)).trans (bft.trans ft),
      (preserved 51 (by decide)).trans (bfc.trans fc), ?_, ?_, ?_, ?_, ?_, ?_,
      readableRet.of_frame savedWrites, preRet, retLow, savedWin, room, align, trivial⟩
    all_goals simp (disch := store_disch) only [savedStack, store_norm]
  have finalAtoms := frameAtomsAfter savedAtoms initWrites (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    change (fr.rsp - 417).toNat + 129 ≤ fr.rsp.toNat - 48
    rw [stackNat 417 (by decide)]
    simp only [BitVec.reduceToNat]
    omega) (fun _ _ => rfl)
  have point : identity.Stored (copiedStack fr m) (fr.rsp - 408) := copyStored ((identity_stored image (Or.inr rfl)).of_frame savedWrites outside)
  have pointAfter : identity.Stored n (fr.rsp - 408) := by
    apply point.of_frame extraWrites
    refine ⟨by rw [stackNat 408 (by decide)]; simp only [BitVec.reduceToNat]; omega, fun r hr => Or.inr ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    change (fr.rsp - 417).toNat + 9 ≤ (fr.rsp - 408).toNat
    rw [stackNat 417 (by decide), stackNat 408 (by decide)]
    simp only [BitVec.reduceToNat]
    omega
  have mag := (digitBytes digit bounds.1 bounds.2).1
  have magOne : magnitude (fr.rdx.setWidth 8) = 1 ↔ digit.natAbs = 1 := by
    rw [index, mag]
    constructor
    · intro h
      have hn := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, BitVec.reduceToNat] at hn
      omega
    · intro h
      rw [h]
      rfl
  refine ⟨c, n, reach, finalAtoms, ?_, by omega, ?_, ?_, ?_, ?_, pointAfter, fullFrame⟩
  · exact (congrArg (Value.get 64) (preserved 14 (by decide))).trans bacc
  · intro _
    exact (congrArg (Value.get 64) (preserved 15 (by decide))).trans btable
  · intro _
    exact (congrArg (fun v : Value => (v.get 64).setWidth 8) (preserved 5 (by decide))).trans
      (bdigit.trans index)
  · intro _
    exact (congrArg (fun v : Value => (v.get 64).setWidth 8) (preserved 13 (by decide))).trans
      (bmag.trans ((congrArg magnitude index).trans mag))
  · rw [flag, Value.get_mk, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),
      bflag]
    change (if magnitude (fr.rdx.setWidth 8) = 1 then (1 : BitVec 8) else 0).setWidth 8 =
      (if decide (digit.natAbs = 1) = true then (1 : BitVec 8) else 0)
    by_cases h : digit.natAbs = 1
    · rw [ite_eq_left (magOne.mpr h), ite_eq_left (decide_eq_true h)] <;> rfl
    · have noMag : ¬ magnitude (fr.rdx.setWidth 8) = 1 := fun hm => h (magOne.mp hm)
      have noFlag : ¬ decide (digit.natAbs = 1) = true := fun hf => h (of_decide_eq_true hf)
      rw [ite_eq_right noMag, ite_eq_right noFlag] <;> rfl

end K256.Proofs.Generate.Generator.Multiply.Lookup
