import K256.Proofs.Generate.Generator.Multiply.Prepare.Digits
import K256.Proofs.Ecdh.Multiply.Frame
import K256.Proofs.Ecdh.Multiply.Split.Memory
import K256.Proofs.Ecdh.Multiply.Digits.Accumulator

namespace K256.Proofs.Generate.Generator.Multiply.Prepare

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters.Secp256k1

local macro "generator_digits%" name:ident : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `K256.Proofs.Generate.Generator.Multiply.Prepare.Digits
    (`K256.Proofs.Generate.Generator.Multiply.Prepare ++ name.getId)))

local macro "unfold_recoding_copy" : tactic => do
  let copy := Lean.mkIdent (Lean.mkPrivateNameCore `K256.Proofs.Generate.Generator.Multiply.Prepare.Digits
    `K256.Proofs.Generate.Generator.Multiply.Prepare.copyRecodings)
  `(tactic| unfold $copy:ident)

private abbrev recodeSite := generator_digits% recodeSite
private abbrev recodeResume := generator_digits% recodeResume
private abbrev recodeRet := generator_digits% recodeRet
private abbrev recodeSrc := generator_digits% recodeSrc
private abbrev recodeDst := generator_digits% recodeDst
private abbrev recodeReg := generator_digits% recodeReg

private theorem peerStackOffsetNat {fr : Activation} {initial : Registers} {d : Nat} {peer : Projective}
    (entry : PeerCoreEntry fr initial d peer) (k : Nat) (hk : k ≤ 3264) :
    (sp fr + BitVec.ofNat 64 k).toNat = fr.rsp.toNat - 3256 + k := by
  have hs := Split.Caller.peerSpNat entry
  have ho := Split.Caller.peerSlotNat entry k (by omega)
  exact ho.trans (congrArg (· + k) hs)

private theorem peerRecodeScratchNat {fr : Activation} {initial : Registers} {d : Nat} {peer : Projective}
    (entry : PeerCoreEntry fr initial d peer) :
    (sp fr - 8 - 33).toNat = fr.rsp.toNat - 3297 := by
  rw [show sp fr - 8 - 33 = fr.rsp - 3297 by unfold sp; bv_omega]
  exact BitVec.toNat_sub_of_le (Nat.le_trans (by decide) entry.room)

private theorem peerRecodePushNat {fr : Activation} {initial : Registers} {d : Nat} {peer : Projective}
    (entry : PeerCoreEntry fr initial d peer) :
    (sp fr - 8).toNat = fr.rsp.toNat - 3264 := by
  rw [show sp fr - 8 = fr.rsp - 3264 by unfold sp; bv_omega]
  exact BitVec.toNat_sub_of_le (Nat.le_trans (by decide) entry.room)

private abbrev recodeWrites (fr : Activation) (first : Bool) : List MemoryRegion :=
  [⟨(sp fr - 8 - 33).toNat, 41⟩, ⟨(sp fr + recodeDst first).toNat, 33⟩]

set_option maxHeartbeats 500000 in
private theorem peerRecodeCall (recode : type_of% @Radix.execute) (first : Bool)
    {fr : Activation} {initial a : Registers} {m : Ram} {d x : Nat} {peer : Projective}
    (entry : PeerCoreEntry fr initial d peer) (s : State (recodeSite first) fr a m)
    (dst : a[recodeReg first] = ⟨64,sp fr + recodeDst first⟩)
    (words : WordsAt m (sp fr + recodeSrc first) 64 (scalarWords x)) (bound : x < 2^128) :
    ∃ b n, Reaches (recodeSite first) a m (recodeResume first) b n ∧
      State (recodeResume first) fr b n ∧ RamWriteFrame m n (recodeWrites fr first) ∧
      (∀ i : Fin Reg.count, i.val ∈ Sample.nonzeroPreserved → b[i] = a[i]) ∧
      WordsAt n (sp fr + recodeDst first) 8 (Vector.ofFn fun i : Fin 33 => Radix.byte x i.val) := by
  have entryFrame : Fn11c880.frameAt (recodeSite first) fr = Fn11c880.frameAt .l11c9e7 fr := by
    cases first <;> rfl
  have exitFrame : Fn11c880.frameAt (recodeResume first) fr = Fn11c880.frameAt .l11c9e7 fr := by
    cases first <;> rfl
  have ha := s.atoms
  rw [entryFrame] at ha
  obtain ⟨rsp,df,mx,ft,fc,_,_,_,_,_,_,_,_,_,win,_,_,_,_,_,_,_,_⟩ := ha
  change Writable Extracted.programImage m (fr.rsp - 3800) 3800 at win
  have room := entry.room
  change 3800 ≤ fr.rsp.toNat at room
  have high := entry.high
  have stackLo : (fr.rsp - 3800).toNat = fr.rsp.toNat - 3800 :=
    BitVec.toNat_sub_of_le room
  have pushLo := peerRecodePushNat entry
  have scratchLo := peerRecodeScratchNat entry
  have srcLo : (sp fr + recodeSrc first).toNat = fr.rsp.toNat - 3256 + (recodeSrc first).toNat := by
    cases first
    · exact peerStackOffsetNat entry 656 (by decide)
    · exact peerStackOffsetNat entry 624 (by decide)
  have srcHi : (sp fr + recodeSrc first + 8).toNat =
      fr.rsp.toNat - 3256 + (recodeSrc first).toNat + 8 := by
    cases first
    · change (sp fr + 0x290 + 8).toNat = _
      rw [show sp fr + 0x290 + 8 = sp fr + 664 by bv_omega]
      exact peerStackOffsetNat entry 664 (by decide)
    · change (sp fr + 0x270 + 8).toNat = _
      rw [show sp fr + 0x270 + 8 = sp fr + 632 by bv_omega]
      exact peerStackOffsetNat entry 632 (by decide)
  have dstLo : (sp fr + recodeDst first).toNat = fr.rsp.toNat - 3256 + (recodeDst first).toNat := by
    cases first
    · exact peerStackOffsetNat entry 464 (by decide)
    · exact peerStackOffsetNat entry 296 (by decide)
  have srcOff : (recodeSrc first).toNat ≤ 656 := by cases first <;> decide
  have dstOff : 296 ≤ (recodeDst first).toNat ∧ (recodeDst first).toNat ≤ 464 := by cases first <;> decide
  have pushWin : Writable Extracted.programImage m (sp fr - 8) 8 :=
    win.sub (by omega) (by omega)
  obtain ⟨b, run, bsp, bd, bs, bw, bk⟩ := (generator_digits% recodeBlock) first (congrArg (Value.get 64) rsp) dst pushWin s.widths
  let q := memStore m (sp fr - 8) (recodeRet first)
  let c := child fr b q (recodeRet first)
  have csp : c.rsp = sp fr - 8 := rfl
  have cd : c.rdi = sp fr + recodeDst first := congrArg (Value.get 64) bd
  have cs : c.rsi = sp fr + recodeSrc first := congrArg (Value.get 64) bs
  have pushed : RamWriteFrame m q [⟨(sp fr - 8).toNat, 8⟩] := by
    dsimp only [q]
    slot_state region
  have pushedCore : RamWriteFrame fr.original q (coreWrites fr) := by
    refine s.frame.trans pushed ?_
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨fr.region, List.mem_cons_self, ?_, ?_⟩
    have hlo : fr.low.toNat = fr.rsp.toNat - 3800 := by rw [entry.low]; exact stackLo
    · change fr.low.toNat ≤ (sp fr - 8).toNat
      omega
    · change (sp fr - 8).toNat + 8 ≤ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat)
      omega
  have childSaved : SavedWidths b := by
    intro i hi
    rw [bk i (by
      simp only [Activation.calleeSavedNumbers, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with h|h|h|h|h|h <;> simp [Sample.nonzeroPreserved, h])]
    exact s.savedWidths i hi
  have childAtoms : Atom.All Extracted.programImage b q (Fn11aa40.frameAt .l11aa40 c) := by
    change Atom.All Extracted.programImage b q (Fn11aa40.frameInfo.entryAtoms c)
    exact peerChildEntry entry Fn11aa40.frameInfo rfl (by decide) bw childSaved bsp
      ((bk 22 (by decide)).trans df) ((bk 39 (by decide)).trans mx)
      ((bk 50 (by decide)).trans ft) ((bk 51 (by decide)).trans fc) pushedCore
      (memLoad_memStore_same _ _ _ (by decide) (by decide)) (by cases first <;> decide)
  have source : Readable q c.rsi 16 := by
    rw [cs]
    exact (win.readable.sub (by omega) (by omega)).of_frame pushed
  have dest : Writable Extracted.programImage q c.rdi 33 := by
    rw [cd]
    exact (win.sub (by omega) (by omega)).of_frame pushed
  have keepPush {k : Nat} {ptr : BitVec 64} (hk : k ≤ 664) (h : ptr.toNat = fr.rsp.toNat - 3256 + k) :
      Outside [⟨(sp fr - 8).toNat, 8⟩] ptr 8 := by
    refine ⟨by omega, ?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact Or.inr (by change (sp fr - 8).toNat + 8 ≤ ptr.toNat; omega)
  have lo : memLoad q c.rsi 64 = BitVec.ofNat 64 x := by
    rw [cs, pushed.memLoad_eq (keepPush (by omega) srcLo)]
    have h := words 0 (by decide)
    rw [show wordAddr (sp fr + recodeSrc first) 64 0 = sp fr + recodeSrc first from BitVec.add_zero _] at h
    simpa only [scalarWords, Vector.getElem_ofFn, Nat.mul_zero, Nat.pow_zero, Nat.div_one] using h
  have hi : memLoad q (c.rsi + 8) 64 = BitVec.ofNat 64 (x / 2^64) := by
    rw [cs, pushed.memLoad_eq (keepPush (k := (recodeSrc first).toNat + 8)
      (by omega) (by rw [srcHi, Nat.add_assoc]))]
    exact words 1 (by decide)
  obtain ⟨out, call, tag, done_, _, outWidths, outWords, write⟩ :=
    recode Common.fnCode_subset_programImage c b q x bound childAtoms source lo hi dest
      (by rw [csp, cs, pushLo, srcLo]; omega) (by rw [csp, cd, pushLo, dstLo]; omega)
  rw [csp, cd] at write
  rw [cd] at outWords
  have reach : Reaches (recodeSite first) a m (recodeResume first) out.values out.store :=
    Sample.reachesAfterSampleCall run call tag []
  have footprint : RamWriteFrame m out.store (recodeWrites fr first) := by
    refine (((RamWriteFrame.refl m _).trans pushed ?_).trans write ?_)
    · intro r hr
      obtain rfl := List.mem_singleton.mp hr
      refine ⟨_, List.mem_cons_self, ?_, ?_⟩ <;> simp only [pushLo, scratchLo] <;> omega
    · intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, Nat.le_refl _, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩
  have frame : RamWriteFrame fr.original out.store (coreWrites fr) := by
    refine s.frame.trans footprint ?_
    intro r hr
    simp only [recodeWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    have hlo : fr.low.toNat = fr.rsp.toNat - 3800 := by rw [entry.low]; exact stackLo
    rcases hr with rfl | rfl <;>
      refine ⟨fr.region, List.mem_cons_self, ?_, ?_⟩ <;>
      simp only [Activation.region, hlo, scratchLo, dstLo] <;> omega
  have keep : ∀ i : Fin Reg.count, i.val ∈ Sample.nonzeroPreserved → out.values[i] = a[i] := by
    obtain ⟨_,cdf,cbx,cbp,cr12,cr13,cr14,cr15,cmx,cft,cfc,_⟩ := done_
    have old (i : Fin Reg.count) (hs : i.val ∈ Activation.calleeSavedNumbers)
        (hp : i.val ∈ Sample.nonzeroPreserved) :
        (⟨64,b[i].get 64⟩ : Value) = a[i] := by
      rw [bk i hp]
      have hw := s.savedWidths i hs
      generalize a[i] = v at hw ⊢
      cases v with
      | mk w bits => cases hw; rfl
    intro ⟨i, hi⟩ hm
    simp only [Sample.nonzeroPreserved, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact (show out.values[3] = ⟨64,b[3].get 64⟩ from cbx).trans (old 3 (by decide) (by decide))
    · exact (show out.values[5] = ⟨64,b[5].get 64⟩ from cbp).trans (old 5 (by decide) (by decide))
    · exact (show out.values[12] = ⟨64,b[12].get 64⟩ from cr12).trans (old 12 (by decide) (by decide))
    · exact (show out.values[13] = ⟨64,b[13].get 64⟩ from cr13).trans (old 13 (by decide) (by decide))
    · exact (show out.values[14] = ⟨64,b[14].get 64⟩ from cr14).trans (old 14 (by decide) (by decide))
    · exact (show out.values[15] = ⟨64,b[15].get 64⟩ from cr15).trans (old 15 (by decide) (by decide))
    · exact cdf.trans df.symm
    · exact cmx.trans mx.symm
    · exact cft.trans ft.symm
    · exact cfc.trans fc.symm
  have retSp : out.values[4] = a[4] := by
    have h := (show out.values[4] = ⟨64,c.rsp + 8⟩ from done_.1)
    rw [h, csp, BitVec.sub_add_cancel]
    exact (show a[4] = ⟨64,sp fr⟩ from rsp).symm
  have saved : Outside (recodeWrites fr first) (fr.rsp - 48) 56 := by
    have h : (fr.rsp - 48).toNat = fr.rsp.toNat - 48 := BitVec.toNat_sub_of_le (by change 48 ≤ fr.rsp.toNat; omega)
    refine ⟨by omega, ?_⟩
    intro r hr
    simp only [recodeWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Or.inr (by simp only [scratchLo, dstLo, h]; omega)
  have atoms := frameAtoms s.atoms entryFrame exitFrame footprint saved (by omega)
    (entry.loaded_of_frame frame) (by
      intro ⟨i, hi⟩ hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl|rfl|rfl|rfl|rfl
      · exact retSp
      · exact keep 22 (by decide)
      · exact keep 39 (by decide)
      · exact keep 50 (by decide)
      · exact keep 51 (by decide))
  have localOutside (k : Nat) (hk : k ≤ 3264)
      (ha : k + 8 ≤ (recodeDst first).toNat ∨ (recodeDst first).toNat + 33 ≤ k) :
      Outside (recodeWrites fr first) (sp fr + BitVec.ofNat 64 k) 8 := by
    have eq := peerStackOffsetNat entry k hk
    refine ⟨by omega, ?_⟩
    intro r hr
    simp only [recodeWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Or.inr (by change (sp fr - 8 - 33).toNat + 41 ≤ _; omega)
    · change _ ≤ (sp fr + recodeDst first).toNat ∨ (sp fr + recodeDst first).toNat + 33 ≤ _
      omega
  have locals := s.locals.of_frame footprint (by
    intro kv h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl
    · exact localOutside 240 (by decide) (by cases first <;> decide)
    · exact localOutside 256 (by decide) (by cases first <;> decide)
    · exact localOutside 416 (by decide) (by cases first <;> decide)
    · exact localOutside 448 (by decide) (by cases first <;> decide)
    · exact localOutside 584 (by decide) (by cases first <;> decide)
    · exact localOutside 3264 (by decide) (by cases first <;> decide))
  exact ⟨out.values,out.store,reach,⟨atoms,outWidths,by
    intro i hi
    rw [keep i (by
      simp only [Activation.calleeSavedNumbers,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with h|h|h|h|h|h <;> simp [Sample.nonzeroPreserved, h])]
    exact s.savedWidths i hi,frame,locals⟩,footprint,keep,outWords⟩


private abbrev copyRecodings := generator_digits% copyRecodings

set_option maxHeartbeats 1800000 in
private theorem peerCopyBlock {p dest : BitVec 64} {a : Registers} {m : Ram}
    (rsp : a[4].get 64 = p) (idx : a[14].get 64 = 0) (off : a[6].get 64 = 0)
    (win : Readable m p 0xcb8)
    (w7 : a[7].width = 64) (w8 : a[8].width = 64) (w9 : a[9].width = 64)
    (out : Writable Extracted.programImage m dest 66)
    (addr : dest = p + 3384)
    (slot : memLoad m (p + 0xf0) 64 = dest)
    (limit : memLoad m (p + 0x88) 64 = 152) :
    ∃ b, Reaches .l11d579 a m .l11d620 b (copyRecodings m p dest) ∧
      ParseSignature.ArgumentWidths b ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,4,12,13,15,22,39,50,51] → b[i] = a[i]) ∧
      b[5].width = 64 ∧ b[14].width = 64 ∧ b[9] = a[9] ∧
      RamWriteFrame m (copyRecodings m p dest) [⟨dest.toNat, 66⟩] := by
  subst dest
  refine ⟨?b, ?reach, ?widths, ?keep, ?w5, ?w14, ?r9, ?frame⟩
  case reach =>
    apply Semantics.Reaches.single
    change program.step _ _ = _
    unfold Program.step
    have run : program.runBlock (dialect Extracted.programImage) ⟨.l11d579,a,m⟩ =
        .jump ⟨.l11d620,?b,copyRecodings m p (p + 3384)⟩ := by
      dsimp only [copyRecodings]
      unfold_recoding_copy
      arithmetic_segment using code_l11d579 [rsp, idx, off, slot, limit, cmpSpec_ZF]
    rw [run]
    rfl
  case widths =>
    intro ⟨i, hi⟩ hm
    simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl <;> first | rfl | exact w7 | exact w8 | exact w9
  case keep =>
    intro ⟨i, hi⟩ hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  case w5 => rfl
  case w14 => rfl
  case r9 => rfl
  case frame =>
    have low := out.readable.low
    have inside (k n : Nat) (hk : k + n ≤ 66) :
        InRegions [⟨(p + 3384).toNat,66⟩] (p + 3384 + BitVec.ofNat 64 k) n := by
      have addr : (p + 3384 + BitVec.ofNat 64 k).toNat = (p + 3384).toNat + k := by
        rw [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (a := k) (by omega),
          Nat.mod_eq_of_lt (by omega)]
      refine ⟨_,List.mem_cons_self,?_⟩
      change (p + 3384).toNat ≤ _ ∧ _ + n ≤ (p + 3384).toNat + 66 ∧ _ + n ≤ 2^64
      rw [addr]
      omega
    dsimp only [copyRecodings]
    unfold_recoding_copy
    apply RamWriteFrame.memStore _ _ (inside 65 1 (by decide))
    apply RamWriteFrame.memStore _ _ (inside 57 8 (by decide))
    apply RamWriteFrame.memStore _ _ (inside 49 8 (by decide))
    apply RamWriteFrame.memStore _ _ (inside 41 8 (by decide))
    apply RamWriteFrame.memStore _ _ (inside 33 8 (by decide))
    have atBase : InRegions [⟨(p + 3384).toNat,66⟩] (p + 3384) 8 := by
      refine ⟨_,List.mem_cons_self,?_⟩
      change (p + 3384).toNat ≤ (p + 3384).toNat ∧ (p + 3384).toNat + 8 ≤ (p + 3384).toNat + 66 ∧
        (p + 3384).toNat + 8 ≤ 2^64
      omega
    apply RamWriteFrame.memStore _ _ atBase
    apply RamWriteFrame.memStore _ _ (inside 8 8 (by decide))
    apply RamWriteFrame.memStore _ _ (inside 16 8 (by decide))
    apply RamWriteFrame.memStore _ _ (inside 24 8 (by decide))
    exact (RamWriteFrame.refl _ _).memStore _ (inside 32 1 (by decide))

set_option maxHeartbeats 2800000 in
theorem peerPrepareDigits (recode : type_of% @Radix.execute)
    {fr : Activation} {initial a : Registers} {m : Ram} {d : Nat} {peer : Projective}
    (entry : PeerCoreEntry fr initial d peer) (_pos : 0 < d) (bound : d < domain.n)
    (s : PeerTablesReady fr a m d peer) :
    ∃ b n, Reaches .l11d546 a m .l11d620 b n ∧ PeerDigitsReady fr b n d peer := by
  have ⟨_, small₁, small₂⟩ := Curve.split_correct d bound
  have room := entry.room
  have high := entry.high
  change 3800 ≤ fr.rsp.toNat at room
  have scratchLo := peerRecodeScratchNat entry
  have recodeApart (first : Bool) (k len : Nat) (hk : k ≤ 3264) (hl : len ≤ 64)
      (ha : k + len ≤ (recodeDst first).toNat ∨ (recodeDst first).toNat + 33 ≤ k) :
      Outside (recodeWrites fr first) (sp fr + BitVec.ofNat 64 k) len := by
    have eq := peerStackOffsetNat entry k hk
    have dstNat : (sp fr + recodeDst first).toNat = fr.rsp.toNat - 3256 + (recodeDst first).toNat := by
      cases first
      · exact peerStackOffsetNat entry 464 (by decide)
      · exact peerStackOffsetNat entry 296 (by decide)
    refine ⟨by omega, ?_⟩
    intro r hr
    simp only [recodeWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Or.inr (by change (sp fr - 8 - 33).toNat + 41 ≤ _; omega)
    · change _ ≤ (sp fr + recodeDst first).toNat ∨ (sp fr + recodeDst first).toNat + 33 ≤ _
      omega
  have keepExtra {a b : Ram} {first : Bool} (h : Locals fr a [(0x60,66),(0x88,152),(0xc0,0)])
      (frame : RamWriteFrame a b (recodeWrites fr first)) :
      Locals fr b [(0x60,66),(0x88,152),(0xc0,0)] := by
    apply h.of_frame frame
    intro p hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl
    · exact recodeApart first 96 8 (by decide) (by decide) (by cases first <;> decide)
    · exact recodeApart first 136 8 (by decide) (by decide) (by cases first <;> decide)
    · exact recodeApart first 192 8 (by decide) (by decide) (by cases first <;> decide)
  obtain ⟨b, n, reach₁, state₁, frame₁, keep₁, words₁⟩ :=
    peerRecodeCall (x := (firstComponent d).natAbs) recode true entry s.toState s.firstDigitPtr s.toMagnitudes.first small₁
  have second : WordsAt n (sp fr + 0x290) 64 (scalarWords (secondComponent d).natAbs) := by
    intro i hi
    have apart : Outside (recodeWrites fr true) (wordAddr (sp fr + 0x290) 64 i) 8 := by
      change Outside _ (sp fr + BitVec.ofNat 64 656 + BitVec.ofNat 64 (8*i)) 8
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact recodeApart true (656 + 8*i) 8 (by omega) (by decide) (by right; change 329 ≤ _; omega)
    exact (frame₁.memLoad_eq (k := 64) apart).trans (s.toMagnitudes.second i hi)
  obtain ⟨c, o, reach₂, state₂, frame₂, keep₂, words₂⟩ :=
    peerRecodeCall (x := (secondComponent d).natAbs) recode false entry state₁
      ((keep₁ 15 (by decide)).trans s.secondDigitPtr) second small₂
  have first : WordsAt o (sp fr + 0x128) 8 (Vector.ofFn fun i : Fin 33 => Radix.byte (firstComponent d).natAbs i.val) := by
    intro i hi
    have apart : Outside (recodeWrites fr false) (wordAddr (sp fr + 0x128) 8 i) 1 := by
      change Outside _ (sp fr + BitVec.ofNat 64 296 + BitVec.ofNat 64 (1*i)) 1
      rw [Nat.one_mul, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact recodeApart false (296+i) 1 (by omega) (by decide) (by left; change _ ≤ 464; omega)
    exact (frame₂.memLoad_eq (k := 8) apart).trans (words₁ i hi)
  have extra := keepExtra (keepExtra s.extra frame₁) frame₂
  have count : memLoad o (sp fr + 0x60) 64 = 66 := extra (0x60,66) (by decide)
  have limit : memLoad o (sp fr + 0x88) 64 = 152 := extra (0x88,152) (by decide)
  have zero : memLoad o (sp fr + 0xc0) 64 = 0 := extra (0xc0,0) (by decide)
  have ptr : memLoad o (sp fr + 0xf0) 64 = fr.r9 := state₂.locals (0xf0,fr.r9) (by simp)
  have cAtoms := state₂.atoms
  change Atom.All Extracted.programImage c o (Fn11c880.frameAt .l11c9e7 fr) at cAtoms
  obtain ⟨rsp,_,_,_,_,_,_,_,_,_,_,_,_,_,win,_,_,_,_,_,_,_,_⟩ := cAtoms
  change Writable Extracted.programImage o (fr.rsp - 3800) 3800 at win
  have stackLo : (fr.rsp - 3800).toNat = fr.rsp.toNat - 3800 :=
    entry.stackOffset 3800 (by decide)
  have stackNat : (sp fr).toNat = fr.rsp.toNat - 3256 := Split.Caller.peerSpNat entry
  have read : Readable o (sp fr) 0xcb8 := by
    apply win.readable.sub <;> rw [stackLo, stackNat] <;> omega
  obtain ⟨e, branch, eSix, eKeep⟩ := (generator_digits% digitCountBranch) (congrArg (Value.get 64) rsp) read zero count
  have eSp := (eKeep 4 (by decide)).trans rsp
  have eIdx := (eKeep 14 (by decide)).trans ((keep₂ 14 (by decide)).trans ((keep₁ 14 (by decide)).trans s.index))
  have addr : fr.r9 = sp fr + 3384 := by rw [entry.digitPtr]; unfold sp; bv_omega
  obtain ⟨f, copy, widths, keep, w5, w14, _, written⟩ :=
    peerCopyBlock (congrArg (Value.get 64) eSp) (congrArg (Value.get 64) eIdx)
      (congrArg (Value.get 64) eSix) read
      ((congrArg Value.width (eKeep 7 (by decide))).trans (state₂.widths 7 (by decide)))
      ((congrArg Value.width (eKeep 8 (by decide))).trans (state₂.widths 8 (by decide)))
      ((congrArg Value.width (eKeep 9 (by decide))).trans (state₂.widths 9 (by decide)))
      (entry.digitWrite.of_frame state₂.frame) addr ptr limit
  have frame : RamWriteFrame fr.original (copyRecodings o (sp fr) fr.r9) (coreWrites fr) := by
    refine state₂.frame.trans written ?_
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩
  have digitNat : fr.r9.toNat = fr.rsp.toNat + 128 := by rw [entry.digitPtr]; exact entry.aboveStack 128 (by decide)
  have copyApart {b : BitVec 64} {len : Nat} (hl : b.toNat + len ≤ 2^64)
      (ha : b.toNat + len ≤ fr.r9.toNat ∨ fr.r9.toNat + 66 ≤ b.toNat) :
      Outside [⟨fr.r9.toNat,66⟩] b len := by
    refine ⟨hl, ?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ha
  have copyStackApart (k : Nat) (hk : k ≤ 3264) (hlen : k+8 ≤ 3384) :
      Outside [⟨fr.r9.toNat,66⟩] (sp fr + BitVec.ofNat 64 k) 8 := by
    apply copyApart
    · rw [peerStackOffsetNat entry k hk]; omega
    · left; rw [peerStackOffsetNat entry k hk]; omega
  have saved : Outside [⟨fr.r9.toNat,66⟩] (fr.rsp - 48) 56 := by
    have nat48 : (fr.rsp - 48).toNat = fr.rsp.toNat - 48 := BitVec.toNat_sub_of_le (by change 48 ≤ fr.rsp.toNat; omega)
    apply copyApart <;> rw [nat48] <;> omega
  have atoms : Atom.All Extracted.programImage f (copyRecodings o (sp fr) fr.r9) (Fn11c880.frameAt .l11d620 fr) :=
    frameAtoms state₂.atoms rfl rfl written saved (by omega) (entry.loaded_of_frame frame) (by
      intro ⟨i, hi⟩ hm
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with rfl|rfl|rfl|rfl|rfl
      · exact (keep 4 (by decide)).trans (eKeep 4 (by decide))
      · exact (keep 22 (by decide)).trans (eKeep 22 (by decide))
      · exact (keep 39 (by decide)).trans (eKeep 39 (by decide))
      · exact (keep 50 (by decide)).trans (eKeep 50 (by decide))
      · exact (keep 51 (by decide)).trans (eKeep 51 (by decide)))
  have savedWidths : SavedWidths f := by
    intro ⟨i, hi⟩ hm
    simp only [Activation.calleeSavedNumbers,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl
    · exact (congrArg Value.width ((keep 3 (by decide)).trans (eKeep 3 (by decide)))).trans (state₂.savedWidths 3 (by decide))
    · exact w5
    · exact (congrArg Value.width ((keep 12 (by decide)).trans (eKeep 12 (by decide)))).trans (state₂.savedWidths 12 (by decide))
    · exact (congrArg Value.width ((keep 13 (by decide)).trans (eKeep 13 (by decide)))).trans (state₂.savedWidths 13 (by decide))
    · exact w14
    · exact (congrArg Value.width ((keep 15 (by decide)).trans (eKeep 15 (by decide)))).trans (state₂.savedWidths 15 (by decide))
  have locals := state₂.locals.of_frame written (by
    intro kv hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl
    · exact copyStackApart 240 (by decide) (by decide)
    · exact copyStackApart 256 (by decide) (by decide)
    · exact copyStackApart 416 (by decide) (by decide)
    · exact copyStackApart 448 (by decide) (by decide)
    · exact copyStackApart 584 (by decide) (by decide)
    · exact copyStackApart 3264 (by decide) (by decide))
  have table₁ : fr.rcx.toNat = fr.rsp.toNat + 4192 := by rw [entry.tablePtr]; exact entry.aboveStack 4192 (by decide)
  have table₂ : (fr.rcx + 960).toNat = fr.rsp.toNat + 5152 := by
    rw [entry.tablePtr, BitVec.add_assoc]
    exact entry.aboveStack 5152 (by decide)
  have tableApart (first : Bool) {p : BitVec 64} (lo : fr.rsp.toNat ≤ p.toNat)
      (hi : p.toNat + 960 ≤ 2^64) : Outside (recodeWrites fr first) p 960 := by
    refine ⟨hi, ?_⟩
    intro r hr
    simp only [recodeWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · exact Or.inr (by change (sp fr - 8 - 33).toNat + 41 ≤ _; omega)
    · apply Or.inr
      cases first
      · change (sp fr + BitVec.ofNat 64 464).toNat + 33 ≤ _
        rw [peerStackOffsetNat entry 464 (by decide)]
        omega
      · change (sp fr + BitVec.ofNat 64 296).toNat + 33 ≤ _
        rw [peerStackOffsetNat entry 296 (by decide)]
        omega
  have tables₁ := ((s.toPeerTables.firstTable.of_frame frame₁ (tableApart true (by omega) (by omega))).of_frame
    frame₂ (tableApart false (by omega) (by omega))).of_frame written (copyApart (by omega) (Or.inr (by omega)))
  have tables₂ := ((s.toPeerTables.secondTable.of_frame frame₁ (tableApart true (by omega) (by omega))).of_frame
    frame₂ (tableApart false (by omega) (by omega))).of_frame written (copyApart (by omega) (Or.inr (by omega)))
  have ⟨digits₁,digits₂⟩ :
      WordsAt (copyRecodings o (sp fr) fr.r9) fr.r9 8
        (Vector.ofFn fun i : Fin 33 => Radix.byte (firstComponent d).natAbs i.val) ∧
      WordsAt (copyRecodings o (sp fr) fr.r9) (fr.r9 + 33) 8
        (Vector.ofFn fun i : Fin 33 => Radix.byte (secondComponent d).natAbs i.val) :=
    (generator_digits% copyRecodings_words) first words₂
  exact ⟨f,_,((reach₁.trans reach₂).trans branch).trans copy,
    ⟨⟨atoms,widths,savedWidths,frame,locals⟩,⟨tables₁,tables₂⟩,
      (written.memLoad_eq (copyStackApart 96 (by decide) (by decide))).trans count,digits₁,digits₂⟩⟩

end K256.Proofs.Generate.Generator.Multiply.Prepare
