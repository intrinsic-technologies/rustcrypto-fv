import K256.Proofs.Signing.UpdateV.Copy
import K256.Proofs.Verify.Hash.Update.Copy
import K256.Proofs.Verify.Hash.Update.Dispatch
import K256.Proofs.Verify.Hash.Update.State
import K256.Proofs.Verify.LIR.Fn104970
import K256.Proofs.ParseSignature.Call
import K256.Proofs.ParseSignature.Memory
import K256.Proofs.Generate.Generator.Multiply.Prepare.Copy
import K256.Proofs.Common.WordCopy

namespace K256.Proofs.Signing.UpdateV

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.RFC Standards.NIST.SHA2 K256.Proofs.Verify.Hash K256.Proofs.Verify.Hash.Update

private def copyPadWords (src : Ram) (sp : BitVec 64) (start : Ram) : Nat → Ram
  | 0 => start
  | n + 1 => memStore (copyPadWords src sp start n) (sp + BitVec.ofNat 64 (272 + 8 * (7 - n)))
      (memLoad src (sp + BitVec.ofNat 64 (8 + 8 * (7 - n))) 64)

private theorem copyPadWords_load (src start : Ram) (sp : BitVec 64) (n i : Nat)
    (hi : i < 8) (hn : n ≤ 8) (copied : 8 ≤ i + n) :
    memLoad (copyPadWords src sp start n) (sp + BitVec.ofNat 64 (272 + 8 * i)) 64 =
      memLoad src (sp + BitVec.ofNat 64 (8 + 8 * i)) 64 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [copyPadWords]
    by_cases last : i = 7 - n
    · subst i
      exact memLoad_memStore_same _ _ _ (by decide) (by decide)
    · rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (RangeApart.of_offsets rfl rfl (by
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega))]
      exact ih (by omega) (by omega)

set_option maxHeartbeats 1800000 in
set_option maxRecDepth 3000 in
theorem copyContext {fr : Activation} {a : Values Value Reg.count} {key : ByteArray} {m : Ram}
    (entry : Atom.All Extracted.programImage a m (Fn104970.frameAt .l104ace fr))
    (writes : RamWriteFrame fr.original m [fr.region])
    (low : fr.low = fr.rsp - 1200) (depth : 1200 ≤ fr.rsp.toNat)
    (limit : fr.rsp.toNat + 8 < 2^32)
    (ctx : a[14] = ⟨64, fr.rsp - 488 + 168⟩)
    (outer : (⟨(fr.rsp - 488 + 8).toNat, 64⟩ : MemoryRegion).HasBytes m (keyPad key 0x5c))
    (hash : Compression.StateAt m (fr.rsp - 488 + 168) (compressBlocks initialHash (keyPad key 0x36)))
    (used : memLoad m (fr.rsp - 488 + 167) 8 = 0)
    (count : memLoad m (fr.rsp - 488 + 200) 64 = 1) :
    ∃ b t, (program.sem (dialect Extracted.programImage)).Reaches
      ⟨⟨.l104ace, a, m⟩, []⟩ ⟨⟨.l104b63, b, t⟩, []⟩ ∧
      Atom.All Extracted.programImage b t (Fn104970.frameAt .l104b63 fr) ∧
      RamWriteFrame fr.original t [fr.region] ∧
      b[14] = ⟨64, fr.rsp - 488 + 168⟩ ∧
      HmacStateAt t (fr.rsp - 488 + 104) key ByteArray.empty := by
  let sp := fr.rsp - 488
  let slot := sp - 8
  let regs : List MemoryRegion := [⟨slot.toNat, 8⟩, ⟨sp.toNat + 104, 336⟩]
  let padRegion : MemoryRegion := ⟨sp.toNat + 272, 64⟩
  let moved := memCopy m (sp + 336) (sp + 104) 104
  let pads := copyPadWords m sp moved
  let pushed := memStore (pads 8) slot (0x104b63 : BitVec 64)
  let final := memCopy pushed (sp + 104) (sp + 272) 168
  have sn : sp.toNat = fr.rsp.toNat - 488 := BitVec.toNat_sub_of_le (by
    change 488 ≤ fr.rsp.toNat
    omega)
  have ln : fr.low.toNat = fr.rsp.toNat - 1200 := by
    rw [low]
    exact BitVec.toNat_sub_of_le (show (1200 : BitVec 64) ≤ fr.rsp from depth)
  have sl : slot.toNat = sp.toNat - 8 := BitVec.toNat_sub_of_le (by
    change 8 ≤ sp.toNat
    omega)
  have addr (i : Nat) (hi : i ≤ 496) : (sp + BitVec.ofNat 64 i).toNat = sp.toNat + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have a104 : (sp + 104).toNat = sp.toNat + 104 := addr 104 (by decide)
  have a272 : (sp + 272).toNat = sp.toNat + 272 := addr 272 (by decide)
  have a336 : (sp + 336).toNat = sp.toNat + 336 := addr 336 (by decide)
  have slotIn : InRegions regs slot 8 :=
    ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _, by omega⟩
  have window (i n : Nat) (lo : 104 ≤ i) (hi : i + n ≤ 440) :
      InRegions regs (sp + BitVec.ofNat 64 i) n := by
    refine ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩
    change sp.toNat + 104 ≤ _ ∧ _ ≤ sp.toNat + 104 + 336 ∧ _ ≤ 2^64
    rw [addr i (by omega)]
    omega
  have padWithin : RegionsWithin [padRegion] regs := by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩
    change sp.toNat + 104 ≤ sp.toNat + 272 ∧ sp.toNat + 272 + 64 ≤ sp.toNat + 104 + 336
    omega
  have writeWithin : RegionsWithin regs [fr.region] := by
    intro r hr
    refine ⟨fr.region, List.mem_singleton_self _, ?_⟩
    simp only [regs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [Activation.region, sl, ln] <;> omega
  have moveFrame : RamWriteFrame m moved regs :=
    Sec1.Wrapper.Copy.memCopy_frame (.refl _ _) (window 336 104 (by decide) (by decide))
  have padFrame (n : Nat) (hn : n ≤ 8) : RamWriteFrame moved (pads n) [padRegion] := by
    induction n with
    | zero => exact .refl _ _
    | succ n ih =>
      change RamWriteFrame moved (memStore (pads n) _ (_ : BitVec 64)) [padRegion]
      apply (ih (by omega)).memStore
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      change sp.toNat + 272 ≤ _ ∧ _ ≤ sp.toNat + 272 + 64 ∧ _ ≤ 2^64
      rw [addr (272 + 8 * (7-n)) (by omega)]
      omega
  have wordsFrame (n : Nat) (hn : n ≤ 8) : RamWriteFrame m (pads n) regs :=
    moveFrame.trans (padFrame n hn) padWithin
  have pushFrame : RamWriteFrame m pushed regs := (wordsFrame 8 (by decide)).memStore _ slotIn
  have finalFrame : RamWriteFrame m final regs :=
    Sec1.Wrapper.Copy.memCopy_frame pushFrame (window 104 168 (by decide) (by decide))
  simp only [Fn104970.frameAt, Fn104970.frameAtG5, Atom.All, Atom.Holds] at entry
  obtain ⟨rsp, df, bx, bp, r12, r13, r15, mx, ft, fc, bxMem, r12Mem, r13Mem, r14Mem,
    r15Mem, bpMem, retRd, retMem, retLow, stack, stackLow, align, gotRd, gotMem,
    compressRd, compressMem, gotApart⟩ := entry
  have rspBits : a[4].get 64 = sp := congrArg (Value.get 64) rsp
  have dfBits : a[22].get 1 = 0 := congrArg (Value.get 1) df
  have writeAt {t : Ram} (frame : RamWriteFrame m t regs) (i n : Nat) (fits : i + n ≤ 488) :
      Writable Extracted.programImage t (sp + BitVec.ofNat 64 i) n := by
    apply (stack.of_frame frame).sub <;> rw [← low, ln, addr i (by omega)] <;> omega
  have writeSlot {t : Ram} (frame : RamWriteFrame m t regs) : Writable Extracted.programImage t slot 8 := by
    apply (stack.of_frame frame).sub <;> rw [← low, ln, sl] <;> omega
  have keepSmall {t : Ram} (frame : RamWriteFrame m t regs) (i : Nat) (hi : i + 8 ≤ 104) :
      memLoad t (sp + BitVec.ofNat 64 i) 64 = memLoad m (sp + BitVec.ofNat 64 i) 64 := by
    apply frame.memLoad_eq
    refine ⟨?_, ?_⟩
    · rw [addr i (by omega)]; change _ + 8 ≤ 2^64; omega
    · intro r hr
      simp only [regs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [addr i (by omega)];
      · change sp.toNat + i + 8 ≤ slot.toNat ∨ slot.toNat + 8 ≤ sp.toNat + i
        omega
      · change sp.toNat + i + 8 ≤ sp.toNat + 104 ∨ sp.toNat + 104 + 336 ≤ sp.toNat + i
        omega
  have keepGot {t : Ram} (frame : RamWriteFrame m t regs) (x : BitVec 64)
      (hlo : 0x203dd0 ≤ x.toNat) (hhi : x.toNat + 8 ≤ 0x203e18) :
      memLoad t x 64 = memLoad m x 64 := by
    apply frame.memLoad_eq
    refine ⟨by change x.toNat + 8 ≤ 2^64; omega, ?_⟩
    intro r hr
    simp only [regs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change x.toNat + 8 ≤ slot.toNat ∨ slot.toNat + 8 ≤ x.toNat
      omega
    · change x.toNat + 8 ≤ sp.toNat + 104 ∨ sp.toNat + 104 + 336 ≤ x.toNat
      omega
  have keepSaved {t : Ram} (frame : RamWriteFrame m t regs) (x : BitVec 64)
      (hlo : fr.rsp.toNat - 48 ≤ x.toNat) (hhi : x.toNat + 8 ≤ fr.rsp.toNat + 8) :
      memLoad t x 64 = memLoad m x 64 := by
    apply frame.memLoad_eq
    refine ⟨by change x.toNat + 8 ≤ 2^64; omega, ?_⟩
    intro r hr
    simp only [regs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · change x.toNat + 8 ≤ slot.toNat ∨ slot.toNat + 8 ≤ x.toNat
      omega
    · change x.toNat + 8 ≤ sp.toNat + 104 ∨ sp.toNat + 104 + 336 ≤ x.toNat
      omega
  have keepStack {t : Ram} (frame : RamWriteFrame m t regs) (i : Nat) (hi : i ≤ 48) :
      memLoad t (fr.rsp - BitVec.ofNat 64 i) 64 = memLoad m (fr.rsp - BitVec.ofNat 64 i) 64 := by
    have h : (fr.rsp - BitVec.ofNat 64 i).toNat = fr.rsp.toNat - i := by
      rw [BitVec.toNat_sub_of_le (by change i % 2^64 ≤ fr.rsp.toNat; omega),
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact keepSaved frame _ (by rw [h]; omega) (by rw [h]; omega)
  have callCode := fun x hx => Common.fnCode_subset_programImage x (code_l104ace x hx)
  have loadAt (k i : Nat) (hk : k ≤ 8) (hi : i + 8 ≤ 104) :
      LoadOk (pads k) (sp + BitVec.ofNat 64 i) 8 := by
    have h := (writeAt (wordsFrame k hk) i 8 (by omega)).readable
    exact ⟨h.low, h.present⟩
  have storeAt (k i off : Nat) (hk : k ≤ 8) (hi : i + 8 ≤ 488)
      (hc : off + 8 ≤ bytes_l104ace.length) :
      StoreOk Extracted.programImage (pads k) (sp + BitVec.ofNat 64 i) 8
        (0x104ace + BitVec.ofNat 64 off) 8 :=
    ParseSignature.storeOk_of_codeRange (writeAt (wordsFrame k hk) i 8 hi) callCode hc
  have rep : RepMovsOk Extracted.programImage m 0 (sp + 104) (sp + 336) 13 8 0x104ae0 3 :=
    Generate.Generator.Multiply.Prepare.copyGuard
      (writeAt (.refl _ _) 104 104 (by decide)).readable
      (ParseSignature.storeOk_of_codeRange (off := 18) (writeAt (.refl _ _) 336 104 (by decide))
        callCode (by decide +kernel)) (Or.inl (by change (sp + 104).toNat + 104 ≤ (sp + 336).toNat; rw [a104, a336]; omega))
  have push : StoreOk Extracted.programImage (pads 8) slot 8 0x104b5d 6 :=
    ParseSignature.storeOk_of_codeRange (off := 143) (writeSlot (wordsFrame 8 (by decide)))
      callCode (by decide +kernel)
  have gotLoad : LoadOk (pads 8) 0x203dd0 8 := by
    have h := gotRd.of_frame (wordsFrame 8 (by decide))
    exact ⟨h.low, h.present⟩
  have gotTarget : memLoad (pads 8) 0x203dd0 64 = 0x12a820 :=
    (keepGot (wordsFrame 8 (by decide)) _ (by decide) (by decide)).trans gotMem
  have runCall : ∃ ca, program.runBlock (dialect Extracted.programImage) ⟨.l104ace, a, m⟩ =
      .call ⟨.l12a820, ca, pushed⟩ (returnFrame .l104b63 0x104b63) ∧
      ca[7].get 64 = sp + 104 ∧ ca[6].get 64 = sp + 272 ∧ ca[2].get 64 = 168 ∧
      ca[4].get 64 = slot ∧ ca[22].get 1 = 0 ∧
      (∀ i : Fin 53, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → ca[i] = a[i]) := by
    refine Exists.intro ?_ ?_
    rotate_left
    constructor
    · cfg_eval [rspBits, dfBits, rep, Nat.reduceMul, or_true, false_or]
      refine Eq.trans (ite_eq_left (loadAt 0 64 (by decide) (by decide))) ?_
      refine Eq.trans (ite_eq_left (storeAt 0 328 26 (by decide) (by decide) (by decide +kernel))) ?_
      rw [show memLoad moved (sp + 64) 64 = memLoad m (sp + 64) 64 from
        keepSmall (wordsFrame 0 (by decide)) 64 (by decide)]
      rw [show memStore moved (sp + 328) (memLoad m (sp + 64) 64) = pads 1 from rfl]
      refine Eq.trans (ite_eq_left (loadAt 1 56 (by decide) (by decide))) ?_
      refine Eq.trans (ite_eq_left (storeAt 1 320 39 (by decide) (by decide) (by decide +kernel))) ?_
      rw [show memLoad (pads 1) (sp + 56) 64 = memLoad m (sp + 56) 64 from
        keepSmall (wordsFrame 1 (by decide)) 56 (by decide)]
      rw [show memStore (pads 1) (sp + 320) (memLoad m (sp + 56) 64) = pads 2 from rfl]
      refine Eq.trans (ite_eq_left (loadAt 2 48 (by decide) (by decide))) ?_
      refine Eq.trans (ite_eq_left (storeAt 2 312 52 (by decide) (by decide) (by decide +kernel))) ?_
      rw [show memLoad (pads 2) (sp + 48) 64 = memLoad m (sp + 48) 64 from
        keepSmall (wordsFrame 2 (by decide)) 48 (by decide)]
      rw [show memStore (pads 2) (sp + 312) (memLoad m (sp + 48) 64) = pads 3 from rfl]
      refine Eq.trans (ite_eq_left (loadAt 3 40 (by decide) (by decide))) ?_
      refine Eq.trans (ite_eq_left (storeAt 3 304 65 (by decide) (by decide) (by decide +kernel))) ?_
      rw [show memLoad (pads 3) (sp + 40) 64 = memLoad m (sp + 40) 64 from
        keepSmall (wordsFrame 3 (by decide)) 40 (by decide)]
      rw [show memStore (pads 3) (sp + 304) (memLoad m (sp + 40) 64) = pads 4 from rfl]
      refine Eq.trans (ite_eq_left (loadAt 4 32 (by decide) (by decide))) ?_
      refine Eq.trans (ite_eq_left (storeAt 4 296 78 (by decide) (by decide) (by decide +kernel))) ?_
      rw [show memLoad (pads 4) (sp + 32) 64 = memLoad m (sp + 32) 64 from
        keepSmall (wordsFrame 4 (by decide)) 32 (by decide)]
      rw [show memStore (pads 4) (sp + 296) (memLoad m (sp + 32) 64) = pads 5 from rfl]
      refine Eq.trans (ite_eq_left (loadAt 5 24 (by decide) (by decide))) ?_
      refine Eq.trans (ite_eq_left (storeAt 5 288 91 (by decide) (by decide) (by decide +kernel))) ?_
      rw [show memLoad (pads 5) (sp + 24) 64 = memLoad m (sp + 24) 64 from
        keepSmall (wordsFrame 5 (by decide)) 24 (by decide)]
      rw [show memStore (pads 5) (sp + 288) (memLoad m (sp + 24) 64) = pads 6 from rfl]
      refine Eq.trans (ite_eq_left (loadAt 6 8 (by decide) (by decide))) ?_
      refine Eq.trans (ite_eq_left (loadAt 6 16 (by decide) (by decide))) ?_
      refine Eq.trans (ite_eq_left (storeAt 6 280 109 (by decide) (by decide) (by decide +kernel))) ?_
      rw [show memLoad (pads 6) (sp + 16) 64 = memLoad m (sp + 16) 64 from
        keepSmall (wordsFrame 6 (by decide)) 16 (by decide)]
      rw [show memStore (pads 6) (sp + 280) (memLoad m (sp + 16) 64) = pads 7 from rfl]
      refine Eq.trans (ite_eq_left (storeAt 7 272 117 (by decide) (by decide) (by decide +kernel))) ?_
      rw [show memLoad (pads 6) (sp + 8) 64 = memLoad m (sp + 8) 64 from
        keepSmall (wordsFrame 6 (by decide)) 8 (by decide)]
      rw [show memStore (pads 7) (sp + 272) (memLoad m (sp + 8) 64) = pads 8 from rfl]
      simp only [gotLoad, gotTarget]
      refine Eq.trans (ite_eq_left ⟨trivial, push, trivial⟩) ?_
      rfl
    · refine ⟨rfl, rfl, rfl, rfl, dfBits, ?_⟩
      rintro ⟨i, hi⟩ h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h | h | h | h | h | h | h | h <;> cases h <;> rfl
  have readDst := (writeAt (wordsFrame 8 (by decide)) 272 64 (by decide)).readable
  have padBytes : (⟨(sp + 272).toNat, 64⟩ : MemoryRegion).HasBytes (pads 8) (keyPad key 0x5c) := by
    have h := Common.hasBytes_of_word_copy (n := 8) outer (keyPad_size key 0x5c) readDst
    refine ⟨keyPad_size _ _, (h ?_).2⟩
    intro i hi
    simp only [wordAddr, Nat.reduceDiv, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      BitVec.add_assoc, ← BitVec.ofNat_add]
    change memLoad (pads 8) (sp + BitVec.ofNat 64 (272 + 8 * i)) 64 =
      memLoad m (sp + (BitVec.ofNat 64 8 + BitVec.ofNat 64 (8 * i))) 64
    rw [← BitVec.ofNat_add]
    exact copyPadWords_load m moved sp 8 i hi (by decide) (by omega)
  have padBytesPushed : (⟨(sp + 272).toNat, 64⟩ : MemoryRegion).HasBytes pushed (keyPad key 0x5c) :=
    bytesStore padBytes (0x104b63 : BitVec 64) (by
      apply RangeApart.of_offsets (addr_sub _ _) rfl
      decide)
  let innerRegs : List MemoryRegion := [⟨slot.toNat,8⟩, padRegion]
  have afterMove : RamWriteFrame moved pushed innerRegs := by
    have w : RamWriteFrame moved (pads 8) innerRegs :=
      (RamWriteFrame.refl _ _).trans (padFrame 8 (by decide)) (fun r hr =>
        ⟨r, List.mem_cons_of_mem _ hr, Nat.le_refl _, Nat.le_refl _⟩)
    exact w.memStore _ ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _, by omega⟩
  have keepInner (i width : Nat) (lo : 336 ≤ i) (hi : i + width / 8 ≤ 440) :
      memLoad pushed (sp + BitVec.ofNat 64 i) width = memLoad moved (sp + BitVec.ofNat 64 i) width := by
    apply afterMove.memLoad_eq
    refine ⟨by rw [addr i (by omega)]; omega, ?_⟩
    intro r hr
    simp only [innerRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [addr i (by omega)]
    rcases hr with rfl | rfl
    · exact .inr (by change slot.toNat + 8 ≤ sp.toNat + i; omega)
    · exact .inr (by change sp.toNat + 272 + 64 ≤ sp.toNat + i; omega)
  have movedHash : Compression.StateAt moved (sp + 400) (compressBlocks initialHash (keyPad key 0x36)) :=
    (show sp + 336 + 64 = sp + 400 by bv_omega) ▸
      stateAt_memCopy_offset (len := 104) (off := 64) (by decide) (by decide)
        (show Compression.StateAt m (sp + 104 + 64) _ from
          (show sp + 168 = sp + 104 + 64 by bv_omega) ▸ hash)
  have pushedHash : Compression.StateAt pushed (sp + 400) (compressBlocks initialHash (keyPad key 0x36)) := by
    refine ⟨movedHash.1, fun i hi => ?_⟩
    have k := keepInner (400 + 4 * i) 32 (by omega) (by omega)
    have he : wordAddr (sp + 400) 32 i = sp + BitVec.ofNat 64 (400 + 4 * i) := by
      simp only [wordAddr, Nat.reduceDiv, BitVec.ofNat_add, BitVec.add_assoc]
      rfl
    exact (congrArg (fun addr => memLoad pushed addr 32) he).trans
      (k.trans ((congrArg (fun addr => memLoad moved addr 32) he).symm.trans (movedHash.2 i hi)))
  have used' : memLoad pushed (sp + 272 + 127) 8 = 0 := by
    rw [show sp + 272 + 127 = sp + 399 by bv_omega]
    refine (keepInner 399 8 (by decide) (by decide)).trans ?_
    change memLoad moved (sp + 399) 8 = 0
    rw [show sp + 399 = sp + 336 + BitVec.ofNat 64 63 by bv_omega]
    refine (Sec1.Parser.Result.memLoad_memCopy (len := 104) m (sp + 336) (sp + 104)
      (by decide) (by decide)).trans ?_
    rw [show sp + 104 + BitVec.ofNat 64 63 = sp + 167 by bv_omega]
    exact used
  have count' : memLoad pushed (sp + 272 + 160) 64 = 1 := by
    rw [show sp + 272 + 160 = sp + 432 by bv_omega]
    refine (keepInner 432 64 (by decide) (by decide)).trans ?_
    change memLoad moved (sp + 432) 64 = 1
    rw [show sp + 432 = sp + 336 + BitVec.ofNat 64 96 by bv_omega]
    refine (Sec1.Parser.Result.memLoad_memCopy (len := 104) m (sp + 336) (sp + 104)
      (by decide) (by decide)).trans ?_
    rw [show sp + 104 + BitVec.ofNat 64 96 = sp + 200 by bv_omega]
    exact count
  have empty : ByteArray.empty.size < 64 := by decide
  have state : HmacStateAt pushed (sp + 272) key ByteArray.empty := by
    refine ⟨padBytesPushed, ?_, used', ?_, count'⟩
    · rw [remainderBytes_keyPad_short key ByteArray.empty 0x36 empty]
      exact ⟨rfl, fun i => False.elim (Nat.not_lt_zero _ i.isLt)⟩
    · rw [compressBlocks_keyPad_short initialHash key ByteArray.empty 0x36 empty]
      rw [show sp + 272 + 128 = sp + 400 by bv_omega]
      exact pushedHash
  obtain ⟨ca, called, dst, src, size, callRsp, callDf, caKept⟩ := runCall
  have retSlot : memLoad pushed slot 64 = 0x104b63 := memLoad_memStore_same _ _ _ (by decide) (by decide)
  have apart : (sp + 104).toNat + 168 ≤ (sp + 272).toNat := by omega
  obtain ⟨out, run, copied, tag, _, back, kept⟩ :=
    Verify.Hash.Update.memcpy dst src size callRsp callDf
      (writeAt pushFrame 272 168 (by decide)).readable
      (writeAt pushFrame 104 168 (by decide)) (Or.inr apart)
      (by apply RangeApart.of_offsets rfl (addr_sub _ _); decide)
      (writeSlot pushFrame).readable (by rw [retSlot]; decide)
  have backToSp : out.values[4] = ⟨64, sp⟩ := by
    rw [back]
    change (⟨64, sp - 8 + 8⟩ : Value) = ⟨64, sp⟩
    rw [BitVec.sub_add_cancel]
  have keepRegs (i : Fin 53) (hi : i.val ∈ [3,5,12,13,14,15,22,39,50,51]) :
      out.values[i] = a[i] := by
    exact (kept i (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
      omega)).trans (caKept i hi)
  have copied' : out.store = final := copied
  refine ⟨out.values, out.store, ?_, ?_, ?_, (keepRegs 14 (by decide)).trans ctx, ?_⟩
  · have resume := ParseSignature.exec_reaches_resume run (returnFrame .l104b63 0x104b63) []
      (by rw [tag, retSlot]; rfl)
    exact .step (congrArg (Transfer.next _ []) called) resume
  · rw [copied']
    simp only [Fn104970.frameAt, Fn104970.frameAtG5, Atom.All, Atom.Holds]
    refine ⟨backToSp, (keepRegs 22 (by decide)).trans df, (keepRegs 3 (by decide)).trans bx,
      (keepRegs 5 (by decide)).trans bp, (keepRegs 12 (by decide)).trans r12,
      (keepRegs 13 (by decide)).trans r13, (keepRegs 15 (by decide)).trans r15,
      (keepRegs 39 (by decide)).trans mx, (keepRegs 50 (by decide)).trans ft,
      (keepRegs 51 (by decide)).trans fc, ?_, ?_, ?_, ?_, ?_, ?_, retRd.of_frame finalFrame,
      ?_, retLow, stack.of_frame finalFrame, stackLow, align, gotRd.of_frame finalFrame,
      (keepGot finalFrame _ (by decide) (by decide)).trans gotMem, compressRd.of_frame finalFrame,
      (keepGot finalFrame _ (by decide) (by decide)).trans compressMem, gotApart⟩
    · exact (keepStack finalFrame 48 (by decide)).trans bxMem
    · exact (keepStack finalFrame 40 (by decide)).trans r12Mem
    · exact (keepStack finalFrame 32 (by decide)).trans r13Mem
    · exact (keepStack finalFrame 24 (by decide)).trans r14Mem
    · exact (keepStack finalFrame 16 (by decide)).trans r15Mem
    · exact (keepStack finalFrame 8 (by decide)).trans bpMem
    · exact (keepSaved finalFrame fr.rsp (by omega) (by omega)).trans retMem
  · rw [copied']
    exact writes.trans finalFrame writeWithin
  · rw [copied']
    exact state.memCopy

end K256.Proofs.Signing.UpdateV
