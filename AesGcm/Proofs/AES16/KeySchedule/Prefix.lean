import AesGcm.Proofs.AES16.Layout
import AesGcm.Proofs.AES16.Sbox
import AesGcm.Proofs.AES16.Output
import AesGcm.Proofs.Machine.Runtime.Call
import AesGcm.Proofs.Machine.LIR.Fn104370.Frame
import AesGcm.Proofs.Machine.LIR.Fn1057c0.Frame
import AesGcm.Proofs.AES16.KeySchedule.Zero
import AesGcm.Proofs.Machine.Runtime.Memset.Unaligned
import AesGcm.Proofs.AES16.KeySchedule.Entry
import AesGcm.Proofs.AES16.KeySchedule.InputCall

namespace AesGcm.Proofs.Machine.AES16

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

namespace KeySchedule
namespace Prefix

theorem keyBytes_of_frame {fr : Activation} {mem : Ram} {n : Nat}
    (hframe : RamWriteFrame fr.original mem [fr.region])
    (hread : Readable fr.original fr.rsi n)
    (hapart : (callStack fr).Disjoint (span fr.rsi n)) :
    ∀ i : Fin n, mem[fr.rsi + BitVec.ofNat 64 i.val]? =
      fr.original[fr.rsi + BitVec.ofNat 64 i.val]? := by
  intro i
  have haddr : (fr.rsi + BitVec.ofNat 64 i.val).toNat = fr.rsi.toNat + i.val := by
    have := hread.low
    have := i.isLt
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := i.val) (by omega), Nat.mod_eq_of_lt (by omega)]
  apply hframe.outside
  refine ⟨by rw [haddr]; have := hread.low; have := i.isLt; omega, ?_⟩
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  have hn := hapart (fr.rsi.toNat + i.val)
  simp only [callStack, span, Activation.region, MemoryRegion.Contains, haddr] at *
  have := i.isLt
  omega

theorem inputRegions_within (use256 later : Bool) (sp : BitVec 64)
    (hroom : 248 ≤ sp.toNat)
    (hlim : sp.toNat + (if use256 then 360 else 264) ≤ 2 ^ 32) :
    RegionsWithin
      [span (sp - 248) 248, span (sp + (if use256 then 288 else 200)) 16,
        span (sp + (if use256 then 12 else 8) + (if later then 16 else 0)) 16]
      [span (sp - 248) 248, span (sp + (if use256 then 12 else 8))
        (if use256 then 240 else 176), span (sp + (if use256 then 288 else 200)) 16] := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, List.Mem.head _, Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨_, List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)),
      Nat.le_refl _, Nat.le_refl _⟩
  · refine ⟨_, List.Mem.tail _ (List.Mem.head _), ?_, ?_⟩
    all_goals cases use256 <;> cases later <;>
      simp only [span, Bool.false_eq_true, ↓reduceIte] at * <;> bv_omega

theorem initial_words (v : Standards.NIST.AES.Variant) (key : Vector UInt8 v.keyBytes)
    (round : Fin (v.Nr + 1)) (hi : 4 * (round.val + 1) ≤ v.Nk)
    (mem out : Ram) (src dst : BitVec 64)
    (hk : ∀ i : Fin v.keyBytes, mem[src + BitVec.ofNat 64 i.val]? = some key[i.val])
    (hw : WordsAt out dst 16
      (Vector.ofFn (Fixslice16.encode
        (Fixslice.memoryBlock mem (src + BitVec.ofNat 64 (16 * round.val)))))) :
    WordsAt out dst 16 (Vector.ofFn (Fixslice16.encodeStandard
      (Machine.KeySchedule.roundKeyBlock v key round))) := by
  rw [memoryBlock_roundKeyBlock_initial v key round hi hk] at hw
  exact hw

end Prefix

end KeySchedule

set_option maxHeartbeats 1200000 in
theorem initializer_prefix_reaches (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (key : Vector UInt8 (variant use256).keyBytes)
    (fr : Activation) (args : Values Value Reg.count)
    (hats : Atom.All code args fr.original
      ((if use256 then LIR.Fn1057c0.frameInfo else LIR.Fn104370.frameInfo).entryAtoms fr))
    (hTypes : GPRsTyped args)
    (hpre : Readable fr.original fr.rsi (variant use256).keyBytes ∧
        (∀ i : Fin (variant use256).keyBytes,
          fr.original[fr.rsi + BitVec.ofNat 64 i.val]? = some key[i.val]) ∧
        (callStack fr).Disjoint (span fr.rsi (variant use256).keyBytes)) :
    let sp := fr.rsp - (if use256 then 360 else 264)
    let base := sp + (if use256 then 12 else 8)
    let raw := sp + (if use256 then 288 else 200)
      ∃ (startArgs : Values Value Reg.count) (startMem : Ram),
        (LIR.program.sem (dialect code)).Reaches
          ⟨⟨(if use256 then .l1057c0 else .l104370), args, fr.original⟩, []⟩
          ⟨⟨(if use256 then .l105856 else .l1043d2), startArgs, startMem⟩, []⟩ ∧
        startArgs[4].get 64 = sp ∧ GPRsTyped startArgs ∧ startArgs[22] = ⟨1, 0⟩ ∧
        startArgs[14].get 64 = base ∧ startArgs[15].get 64 = (if use256 then 8 else 0) ∧
        Writable code startMem (sp - 248) (if use256 then 608 else 512) ∧
        248 ≤ sp.toNat ∧ sp.toNat % 16 = 0 ∧
        Readable startMem 0x201210 8 ∧ memLoad startMem 0x201210 64 = 0x103880 ∧
        Readable startMem 0x201230 8 ∧ memLoad startMem 0x201230 64 = 0x101230 ∧
        (0x201330 ≤ sp.toNat ∨ sp.toNat + (if use256 then 360 else 264) ≤ 0x201210) ∧
        KeySchedule.RawSchedulePrefix (variant use256) key ((variant use256).Nk / 4)
          base startMem ∧
        startArgs[39] = ⟨32, fr.mxcsr⟩ ∧ startArgs[50] = ⟨16, fr.ftw⟩ ∧
        startArgs[51] = ⟨16, fr.fcw⟩ ∧
        RamWriteFrame fr.original startMem [fr.region] ∧
        RamWriteFrame (KeySchedule.entryMemory use256 args fr.original) startMem
          [span (sp - 248) 248, span base (if use256 then 240 else 176), span raw 16] := by
  dsimp only
  let sp := fr.rsp - (if use256 then 360 else 264)
  let base := sp + (if use256 then 12 else 8)
  let raw := sp + (if use256 then 288 else 200)
  have hEntry := KeySchedule.initializer_entry_atoms use256 code fr args hats
  rcases hEntry with ⟨ha4, ha22, ha1, ha2, ha3, ha5, ha6, ha7, ha8, ha9,
    ha12, ha13, ha14, ha15, ha39, ha50, ha51, hRetRead, hRet, hRetLow,
    hStack, hRoom, hAlign, hReadCopy, hCopy, hReadPanic, hPanic,
    hReadZero, hZero, hReadBounds, hBounds, hSep, _⟩
  have hsp : args[4].get 64 = fr.rsp := by rw [ha4]; rfl
  have hInitialRoom : (if use256 then 608 else 512) ≤ fr.rsp.toNat := by omega
  obtain ⟨zeroed, hZeroReach, hz4, hz12, hz14, hz15, hz3, hz5, hz13,
      hz22, hz39, hz50, hz51, hzTypes, hzFrame, hzZero⟩ :=
    KeySchedule.entry_zero_reaches use256 code hcode (memset_zero_call_of_writable code hcode)
      args fr.original hTypes ha22 (by rw [ha39]; rfl) (by rw [ha50]; rfl)
      (by rw [ha51]; rfl) (by simpa only [hsp] using hStack)
      (by simpa only [hsp] using hInitialRoom) (by simpa only [hsp] using hAlign)
      hReadZero hZero (by simpa only [hsp] using hSep)
  have hSpNat : sp.toNat = fr.rsp.toNat - (if use256 then 360 else 264) := by
    dsimp only [sp]
    cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> bv_omega
  have hSpRoom : 248 ≤ sp.toNat := by
    rw [hSpNat]
    cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> omega
  have hSpLow : sp.toNat + (if use256 then 360 else 264) ≤ 2 ^ 32 := by
    have := hStack.readable.low
    cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> bv_omega
  have hBase : args[4].get 64 - (if use256 then 348 else 256) = base := by
    rw [hsp]
    cases use256 <;> simp only [base, sp, Bool.false_eq_true, ↓reduceIte] <;> bv_omega
  have hStackAddr : sp - 248 = fr.rsp - (if use256 then 608 else 512) := by
    cases use256 <;> simp only [sp, Bool.false_eq_true, ↓reduceIte] <;> bv_omega
  let footprint := [span (sp - 248) 248, span base (if use256 then 240 else 176), span raw 16]
  have hWithin : RegionsWithin footprint
      [span (sp - 248) (if use256 then 608 else 512)] := by
    intro r hr
    simp only [footprint, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    all_goals refine ⟨_, List.Mem.head _, ?_, ?_⟩
    all_goals cases use256 <;> simp only [span, base, raw, Bool.false_eq_true, ↓reduceIte] at * <;> bv_omega
  have hWithinFr : RegionsWithin
      [span (sp - 248) (if use256 then 608 else 512)] [fr.region] := by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    refine ⟨_, List.Mem.head _, ?_, ?_⟩
    all_goals rw [hStackAddr]
    all_goals cases use256 <;> simp only [span, Activation.region, Bool.false_eq_true, ↓reduceIte] at * <;> bv_omega
  have hZeroFrame : RamWriteFrame (KeySchedule.entryMemory use256 args fr.original)
      zeroed.store footprint := by
    apply (RamWriteFrame.refl _ _).trans hzFrame
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · refine ⟨_, List.Mem.head _, ?_, ?_⟩
      all_goals rw [hsp]
      all_goals cases use256 <;> simp only [span, sp, Bool.false_eq_true, ↓reduceIte] at * <;> bv_omega
    · rw [hBase]
      exact ⟨_, List.Mem.tail _ (List.Mem.head _), Nat.le_refl _, Nat.le_refl _⟩
  have hEntryFrame : RamWriteFrame fr.original
      (KeySchedule.entryMemory use256 args fr.original)
      [span (sp - 248) (if use256 then 608 else 512)] := by
    rw [hStackAddr]
    simpa only [hsp] using KeySchedule.entryMemory_frame use256 args fr.original
      (by simpa only [hsp] using hInitialRoom)
  have hZeroFull := hEntryFrame.trans hZeroFrame hWithin
  have hZeroFr : RamWriteFrame fr.original zeroed.store [fr.region] :=
    (RamWriteFrame.refl _ _).trans hZeroFull hWithinFr
  have hOriginalReady : KeySchedule.Generation.MemoryReady use256 code fr.original sp := by
    refine ⟨?_, hSpRoom, ?_, hReadPanic, hPanic, hReadBounds, hBounds, ?_⟩
    · rw [hStackAddr]; exact hStack
    · rw [hSpNat]
      cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> omega
    · rw [hSpNat]
      cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> omega
  have hZeroReady := KeySchedule.Generation.memoryReady_of_frame hOriginalReady hZeroFull
    (by intro r hr; exact ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩)
  have hzSp : zeroed.values[4].get 64 = sp := by simpa only [hsp] using hz4
  have hzBase : zeroed.values[14].get 64 = base := hz14.trans hBase
  have hzKey : zeroed.values[12].get 64 = fr.rsi := by rw [hz12, ha6]; rfl
  have hzKeyBytes : ∀ i : Fin (variant use256).keyBytes,
      zeroed.store[fr.rsi + BitVec.ofNat 64 i.val]? = some key[i.val] := by
    intro i
    rw [KeySchedule.Prefix.keyBytes_of_frame hZeroFr hpre.1 hpre.2.2 i]
    exact hpre.2.1 i
  obtain ⟨first, hFirst, hfSp, hf12, hf14, hf15, hfPres, hfTypes, hfFrame, hfWords⟩ :=
    KeySchedule.key_input_reaches use256 false (by simp) code hcode zeroed.values zeroed.store
      (by rw [hzSp]; exact hZeroReady) hzTypes (hz22.trans ha22)
      (by rw [hz39, ha39]; rfl) (by rw [hz50, ha50]; rfl) (by rw [hz51, ha51]; rfl)
      (by rw [hzSp, hzBase])
      (by rw [hzKey]; cases use256 <;> exact hpre.1.of_frame hZeroFr)
  have hfSp' : first.values[4].get 64 = sp := hfSp.trans hzSp
  have hf12' : first.values[12].get 64 = fr.rsi := by rw [hf12, hzKey]
  have hf14' : first.values[14].get 64 = base := by rw [hf14, hzBase]
  have hfFrame' : RamWriteFrame zeroed.store first.store footprint := by
    apply (RamWriteFrame.refl _ _).trans hfFrame
    rw [hzSp]
    exact KeySchedule.Prefix.inputRegions_within use256 false sp hSpRoom hSpLow
  have hfSaved := hZeroFrame.trans hfFrame'
    (by intro r hr; exact ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩)
  have hfFull := hZeroFull.trans hfFrame' hWithin
  have hfFr : RamWriteFrame fr.original first.store [fr.region] :=
    (RamWriteFrame.refl _ _).trans hfFull hWithinFr
  have hfReady := KeySchedule.Generation.memoryReady_of_frame hZeroReady hfFrame' hWithin
  have hfFP : first.values[39] = ⟨32, fr.mxcsr⟩ ∧ first.values[50] = ⟨16, fr.ftw⟩ ∧
      first.values[51] = ⟨16, fr.fcw⟩ :=
    ⟨(hfPres 39 (by decide)).trans (hz39.trans ha39),
      (hfPres 50 (by decide)).trans (hz50.trans ha50),
      (hfPres 51 (by decide)).trans (hz51.trans ha51)⟩
  have hfDF : first.values[22] = ⟨1, 0⟩ := (hfPres 22 (by decide)).trans (hz22.trans ha22)
  have hfRound0 : WordsAt first.store base 16
      (Vector.ofFn (Fixslice16.encodeStandard
        (Machine.KeySchedule.roundKeyBlock (variant use256) key ⟨0, by cases use256 <;> decide⟩))) := by
    apply KeySchedule.Prefix.initial_words (variant use256) key
      ⟨0, by cases use256 <;> decide⟩
      (by change 4 ≤ (variant use256).Nk; cases use256 <;> decide)
      zeroed.store first.store fr.rsi base hzKeyBytes
    simpa only [hzSp, hzKey, Bool.false_eq_true, ↓reduceIte, Nat.mul_zero,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, base] using hfWords
  cases use256
  · refine ⟨first.values, first.store, hZeroReach.trans hFirst, hfSp', hfTypes, hfDF,
      hf14', ?_, hfReady.hstack, hfReady.hroom, hfReady.hAlign,
      hfReady.hreadPanic, hfReady.hpanic, hfReady.hreadBounds, hfReady.hbounds,
      hfReady.hslotsApart, ?_, hfFP.1, hfFP.2.1, hfFP.2.2, hfFr, hfSaved⟩
    · simpa only [Bool.false_eq_true, ↓reduceIte, Bool.false_and, Bool.not_false] using hf15.trans hz15
    · intro r hr p
      have he : r.val = 0 := by change r.val < 1 at hr; omega
      have heq : r = ⟨0, by decide⟩ := Fin.ext he
      subst r
      simpa only [wordAddr, Vector.getElem_ofFn, Nat.reduceDiv, Nat.mul_zero,
        Nat.zero_add] using hfRound0 p.val p.isLt
  · have hfKeyBytes : ∀ i : Fin (variant true).keyBytes,
        first.store[fr.rsi + BitVec.ofNat 64 i.val]? = some key[i.val] := by
      intro i
      rw [KeySchedule.Prefix.keyBytes_of_frame hfFr hpre.1 hpre.2.2 i]
      exact hpre.2.1 i
    obtain ⟨second, hSecond, hsSp, hs12, hs14, hs15, hsPres, hsTypes, hsFrame, hsWords⟩ :=
      KeySchedule.key_input_reaches true true (by intro; rfl) code hcode first.values first.store
        (by rw [hfSp']; exact hfReady) hfTypes hfDF
        (by rw [hfFP.1]; rfl) (by rw [hfFP.2.1]; rfl) (by rw [hfFP.2.2]; rfl)
        (by rw [hfSp', hf14'])
        (by rw [hf12']; exact hpre.1.of_frame hfFr)
    have hsFrame' : RamWriteFrame first.store second.store footprint := by
      apply (RamWriteFrame.refl _ _).trans hsFrame
      rw [hfSp']
      exact KeySchedule.Prefix.inputRegions_within true true sp hSpRoom hSpLow
    have hsSaved := hfSaved.trans hsFrame'
      (by intro r hr; exact ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩)
    have hsFull := hfFull.trans hsFrame' hWithin
    have hsFr : RamWriteFrame fr.original second.store [fr.region] :=
      (RamWriteFrame.refl _ _).trans hsFull hWithinFr
    have hsReady := KeySchedule.Generation.memoryReady_of_frame hfReady hsFrame' hWithin
    have hsRound0 : WordsAt second.store base 16
        (Vector.ofFn (Fixslice16.encodeStandard
          (Machine.KeySchedule.roundKeyBlock (variant true) key ⟨0, by decide⟩))) := by
      apply hfRound0.of_frame hsFrame (by decide)
      rw [hfSp']
      refine ⟨?_, ?_⟩
      · change base.toNat + 16 ≤ 2 ^ 64
        simp only [base, ↓reduceIte]
        simp only [↓reduceIte] at hSpLow
        bv_omega
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        all_goals simp only [span, base, ↓reduceIte]
        all_goals bv_omega
    have hsRound1 : WordsAt second.store (base + 16) 16
        (Vector.ofFn (Fixslice16.encodeStandard
          (Machine.KeySchedule.roundKeyBlock (variant true) key ⟨1, by decide⟩))) := by
      apply KeySchedule.Prefix.initial_words (variant true) key
        ⟨1, by decide⟩ (by decide) first.store second.store fr.rsi (base + 16) hfKeyBytes
      simpa only [hfSp', hf12', ↓reduceIte, Nat.mul_one, BitVec.ofNat_eq_ofNat, base] using hsWords
    refine ⟨second.values, second.store, (hZeroReach.trans hFirst).trans hSecond,
      hsSp.trans hfSp', hsTypes, (hsPres 22 (by decide)).trans hfDF,
      (congrArg (Value.get 64) hs14).trans hf14', ?_,
      hsReady.hstack, hsReady.hroom, hsReady.hAlign,
      hsReady.hreadPanic, hsReady.hpanic, hsReady.hreadBounds, hsReady.hbounds,
      hsReady.hslotsApart, ?_, (hsPres 39 (by decide)).trans hfFP.1,
      (hsPres 50 (by decide)).trans hfFP.2.1, (hsPres 51 (by decide)).trans hfFP.2.2,
      hsFr, hsSaved⟩
    · exact hs15.trans hf15
    · intro r hr p
      have he : r.val = 0 ∨ r.val = 1 := by change r.val < 2 at hr; omega
      rcases he with he | he
      · have heq : r = ⟨0, by decide⟩ := Fin.ext he
        subst r
        simpa only [wordAddr, Vector.getElem_ofFn, Nat.reduceDiv, Nat.mul_zero,
          Nat.zero_add, base, sp, ↓reduceIte] using hsRound0 p.val p.isLt
      · have heq : r = ⟨1, by decide⟩ := Fin.ext he
        subst r
        simpa only [wordAddr, Vector.getElem_ofFn, Nat.reduceDiv, Nat.mul_one,
          BitVec.add_assoc, BitVec.ofNat_add, base, sp, ↓reduceIte, BitVec.ofNat_eq_ofNat] using hsRound1 p.val p.isLt

end AesGcm.Proofs.Machine.AES16
