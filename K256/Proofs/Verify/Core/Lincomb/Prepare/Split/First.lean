import K256.Proofs.Verify.Core.Lincomb.Prepare.Split.NegateStaged
import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Verify.Core.Lincomb.Prepare

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (scalarWords)
open Generate.Curve
open Generate.Generator.Multiply.Prepare.Bases.Negate (storeFour)

def secondLabel (k : Nat) : Label :=
  if second k < 0 then .l10f418 else .l10f48a

local macro "split_arguments" ws:term : tactic => `(tactic| (
  intro ⟨i, hi⟩ h
  have old := $ws ⟨i, hi⟩ h
  change i ∈ Activation.argumentNumbers at h
  simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h <;> subst i <;> first | rfl | exact old))

private theorem lowByte (v : Value) : (v.get 64).setWidth 8 = v.get 8 := by
  simp only [Value.get, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64)]

local macro "keep_split" : tactic => `(tactic| (
  rintro ⟨i, hi⟩ h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h <;> subst i <;> rfl))

private theorem signDispatch {a : Registers} {m : Ram} {k : Nat}
    (firstSign : a[14].get 8 = signByte (first k)) (secondSign : a[0].get 8 = signByte (second k))
    (widths : ParseSignature.ArgumentWidths a) :
    ∃ b, Reaches .l10f3c5 a m (if first k < 0 then .l10f3cd else .l10f44c) b m ∧
      b[4] = a[4] ∧ b[15].width = 64 ∧ b[15].get 8 = signByte (second k) ∧
      ParseSignature.ArgumentWidths b ∧ b[0] = a[0] ∧
      (∀ i : Fin Reg.count, i.val ∈ [3, 5, 12, 13, 14, 22, 39, 50, 51] → b[i] = a[i]) := by
  have low : (((a[0].get 64).setWidth 32).setWidth 64).setWidth 8 = a[0].get 8 := by
    simp only [Value.get, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),
      BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32)]
  by_cases h : first k < 0
  case' pos =>
    rw [ite_eq_left h]
    have byte : signByte (first k) = 1 := ite_eq_left h
    have test := firstSign.trans byte
  case' neg =>
    rw [ite_eq_right h]
    have byte : signByte (first k) = 0 := ite_eq_right h
    have test := firstSign.trans byte
  all_goals
    refine ⟨?_, Semantics.Reaches.single ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    rotate_left
    · change (program.runBlock _ _).next _ [] = _
      cfg_eval [lowByte, test, BitVec.and_self, testFlags]
      rfl
    · rfl
    · rfl
    · exact low.trans secondSign
    · split_arguments widths
    · rfl
    · rintro ⟨i, hi⟩ hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm <;> subst i <;> rfl

private theorem sourceLimbs {m : Ram} {base : BitVec 64} {w : Vector (BitVec 64) 4}
    (words : WordsAt m (base + 8) 64 w) :
    memLoad m (base + 8) 64 = w[0] ∧ memLoad m (base + 16) 64 = w[1] ∧
      memLoad m (base + 24) 64 = w[2] ∧ memLoad m (base + 32) 64 = w[3] := by
  have h0 := words 0 (by decide)
  have h1 := words 1 (by decide)
  have h2 := words 2 (by decide)
  have h3 := words 3 (by decide)
  simp only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
    BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] at h0 h1 h2 h3
  exact ⟨h0, h1, h2, h3⟩

set_option maxRecDepth 4096 in
private theorem stageFirst {a : Registers} {m : Ram} {base : BitVec 64} {w : Vector (BitVec 64) 4}
    (rsp : a[4].get 64 = base) (widths : ParseSignature.ArgumentWidths a)
    (words : WordsAt m (base + 8) 64 w)
    (win : Writable Extracted.programImage m base 0x100)
    (below : Writable Extracted.programImage m (base - 8) 8) :
    ∃ b, program.runBlock (dialect Extracted.programImage) ⟨.l10f3cd, a, m⟩ =
      .call ⟨.l110b80, b, memStore (storeFour m (base + 56) w) (base - 8) (0x10f40e : BitVec 64)⟩
        (callResume .l10f40e 0x10f40e) ∧
      b[4] = ⟨64, base - 8⟩ ∧ b[7].get 64 = base + 224 ∧ b[6].get 64 = base + 56 ∧
      b[2].get 64 = 0x2021a0 ∧ ParseSignature.ArgumentWidths b ∧ KeptForMagnitude a b := by
  obtain ⟨x, y, z, t⟩ := sourceLimbs words
  have low := win.readable.low
  refine ⟨?b, ?run, ?r4, ?di, ?si, ?dx, ?width, ?keep⟩
  case run =>
    simp only [storeFour, BitVec.add_assoc, BitVec.reduceAdd]
    cfg_eval [rsp, x, y, z, t]
    segment_words [x, y, z, t]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l10f3cd)
    rfl
  case width => split_arguments widths
  case keep => keep_split
  all_goals rfl

set_option maxRecDepth 4096 in
private theorem copyFirst {a : Registers} {m : Ram} {base : BitVec 64} {w : Vector (BitVec 64) 4}
    {k : Nat} (rsp : a[4].get 64 = base) (widths : ParseSignature.ArgumentWidths a)
    (words : WordsAt m (base + 8) 64 w) (sign : a[15].get 8 = signByte (second k))
    (win : Writable Extracted.programImage m base 0x100) :
    ∃ b, Reaches .l10f44c a m (secondLabel k) b
      (memStore (storeFour m (base + 224) w) (base + 7) (signByte (second k))) ∧
      b[4] = a[4] ∧ KeptForMagnitude a b ∧ ParseSignature.ArgumentWidths b := by
  obtain ⟨x, y, z, t⟩ := sourceLimbs words
  have low := win.readable.low
  by_cases h : second k < 0
  case' pos =>
    have byte : signByte (second k) = 1 := ite_eq_left h
    rw [secondLabel, ite_eq_left h, byte]
    have test := sign.trans byte
  case' neg =>
    have byte : signByte (second k) = 0 := ite_eq_right h
    rw [secondLabel, ite_eq_right h, byte]
    have test := sign.trans byte
  all_goals
    refine ⟨?_, Semantics.Reaches.single ?_, ?_, ?_, ?_⟩
    rotate_left
    · change (program.runBlock _ _).next _ [] = _
      simp only [storeFour, BitVec.add_assoc, BitVec.reduceAdd]
      cfg_eval [rsp, x, y, z, t, lowByte, test, BitVec.and_self, testFlags]
      segment_words [x, y, z, t, lowByte, test]
      repeat' (refine Eq.trans (congrArg _ (ite_eq_left ?_)) ?_; slot_guard using code_l10f44c)
      rfl
    · rfl
    · keep_split
    · split_arguments widths

set_option maxRecDepth 4096 in
private theorem dispatchSecond {a : Registers} {m : Ram} {base : BitVec 64}
    {k : Nat} (rsp : a[4].get 64 = base) (widths : ParseSignature.ArgumentWidths a)
    (sign : a[15].get 8 = signByte (second k))
    (win : Writable Extracted.programImage m base 0x100) :
    ∃ b, Reaches .l10f40e a m (secondLabel k) b (memStore m (base + 7) (signByte (second k))) ∧
      b[4] = a[4] ∧ KeptForMagnitude a b ∧ ParseSignature.ArgumentWidths b := by
  have low := win.readable.low
  by_cases h : second k < 0
  case' pos =>
    have byte : signByte (second k) = 1 := ite_eq_left h
    rw [secondLabel, ite_eq_left h, byte]
    have test := sign.trans byte
  case' neg =>
    have byte : signByte (second k) = 0 := ite_eq_right h
    rw [secondLabel, ite_eq_right h, byte]
    have test := sign.trans byte
  all_goals
    refine ⟨?_, Semantics.Reaches.single ?_, ?_, ?_, ?_⟩
    rotate_left
    · change (program.runBlock _ _).next _ [] = _
      cfg_eval [rsp, lowByte, test, BitVec.and_self, testFlags]
      repeat' (refine Eq.trans (congrArg _ (ite_eq_left ?_)) ?_; slot_guard using code_l10f40e)
      rfl
    · rfl
    · keep_split
    · split_arguments widths

structure FirstMagnitude (initial : Registers) (original : Ram) (sp src tables digits : BitVec 64)
    (k : Nat) (b : Registers) (n : Ram) : Prop extends SplitFrame initial original sp src tables digits b n where
  firstSign : b[14].get 8 = signByte (first k)
  secondSign : memLoad n (frameSp sp + 7) 8 = signByte (second k)
  firstWords : WordsAt n (frameSp sp + 0xe0) 64 (scalarWords (first k).natAbs)
  low : memLoad n (frameSp sp + 0x30) 64 = (scalarWords (splitSecond k))[0]
  midLow : b[12].get 64 = (scalarWords (splitSecond k))[1]
  midHigh : b[5].get 64 = (scalarWords (splitSecond k))[2]
  high : b[13].get 64 = (scalarWords (splitSecond k))[3]

private theorem finishFirst {a b c : Registers} {m n o : Ram} {sp src tables digits : BitVec 64}
    {k : Nat} (entry : RoutineEntry a m sp 0x558)
    (s : Signs a m sp src tables digits k b n)
    (rsp : c[4] = ⟨64, frameSp sp⟩) (keep : KeptForMagnitude b c)
    (args : ParseSignature.ArgumentWidths c)
    (foot : RamWriteFrame n o (negateWrites (frameSp sp) 224))
    (words : WordsAt o (frameSp sp + 224) 64 (scalarWords (first k).natAbs)) :
    FirstMagnitude a m sp src tables digits k c
      (memStore o (frameSp sp + 7) (signByte (second k))) := by
  let base := frameSp sp
  let sign := signByte (second k)
  let result := memStore o (base + 7) sign
  let writes := ⟨base.toNat + 7, 1⟩ :: negateWrites base 224
  have room := entry.room
  have limit := entry.returnSlot.low
  have bn : base.toNat = sp.toNat - 696 :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 696 ≤ sp.toNat; omega))
  have addNat (off : BitVec 64) (fits : off.toNat ≤ 696) :
      (base + off).toNat = base.toNat + off.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have signNat : (base + 7).toNat = base.toNat + 7 := addNat 7 (by decide)
  have dstNat : (base + 224).toNat = base.toNat + 224 := addNat 224 (by decide)
  have signAt : InRegions writes (base + 7) 1 :=
    ⟨_, .head _, by dsimp only; omega, by dsimp only; omega, by omega⟩
  have effect : RamWriteFrame n result writes :=
    (RamWriteFrame.refl n writes |>.trans foot
      (fun r h => ⟨r, .tail _ h, Nat.le_refl _, Nat.le_refl _⟩)).memStore sign signAt
  have savedRead (q : BitVec 64) (left : base.toNat + 8 ≤ q.toNat)
      (right : q.toNat + 8 ≤ sp.toNat)
      (staged : q.toNat + 8 ≤ base.toNat + 56 ∨ base.toNat + 88 ≤ q.toNat)
      (dst : q.toNat + 8 ≤ base.toNat + 224 ∨ base.toNat + 256 ≤ q.toNat) :
      memLoad result q 64 = memLoad n q 64 := by
    apply effect.memLoad_eq
    refine ⟨by change q.toNat + 8 ≤ _; omega, ?_⟩
    intro r hr
    simp only [writes, negateWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · right; dsimp only; omega
    · right; change base.toNat - 56 + 56 ≤ q.toNat; omega
    · exact staged
    · exact dst
  have fromTop (off : BitVec 64) (lo : 8 ≤ off.toNat) (hi : off.toNat ≤ 48) :
      memLoad result (sp - off) 64 = memLoad n (sp - off) 64 := by
    have pos : (sp - off).toNat = sp.toNat - off.toNat :=
      BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))
    apply savedRead <;> omega
  have fromBase (off : BitVec 64) (lo : 8 ≤ off.toNat)
      (hi : off.toNat + 8 ≤ 696)
      (staged : off.toNat + 8 ≤ 56 ∨ 88 ≤ off.toNat)
      (dst : off.toNat + 8 ≤ 224 ∨ 256 ≤ off.toNat) :
      memLoad result (base + off) 64 = memLoad n (base + off) 64 := by
    have pos := addNat off (by omega)
    apply savedRead <;> omega
  refine ⟨⟨s.toSavedFrame.preserve rsp keep fromTop,
    s.frame.trans effect ?within,
    (fromBase 40 (by decide) (by decide) (by decide) (by decide)).trans s.pointPtr,
    (fromBase 216 (by decide) (by decide) (by decide) (by decide)).trans s.digitPtr, args⟩,
    (congrArg (Value.get 8) (keep 14 (by decide))).trans s.firstSign,
    memLoad_memStore_same _ _ _ (by decide) (by decide), ?words,
    (fromBase 48 (by decide) (by decide) (by decide) (by decide)).trans s.low,
    (congrArg (Value.get 64) (keep 12 (by decide))).trans s.midLow,
    (congrArg (Value.get 64) (keep 5 (by decide))).trans s.midHigh,
    (congrArg (Value.get 64) (keep 13 (by decide))).trans s.high⟩
  case within =>
    intro r hr
    simp only [writes, negateWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    refine ⟨_, .head _, ?_⟩
    rcases hr with rfl | rfl | rfl | rfl <;> dsimp only [scratch] <;> omega
  case words =>
    have apart : RangeApart (base + 7) 1 (base + 224) 32 :=
      RangeApart.of_toNat (by omega) (by omega) (.inl (by omega))
    exact words.write_apart _ sign apart

theorem storeFirstMagnitude {a b : Registers} {m n : Ram} {sp src tables digits : BitVec 64}
    {k : Nat} (entry : RoutineEntry a m sp 0x558) (bound : k < domain.n)
    (state : Signs a m sp src tables digits k b n) :
    ∃ c o, Reaches .l10f3c5 b n (secondLabel k) c o ∧ FirstMagnitude a m sp src tables digits k c o := by
  let base := frameSp sp
  let x := splitFirst k
  have room := entry.room
  have limit := entry.returnSlot.low
  have bn : base.toNat = sp.toNat - 696 :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 696 ≤ sp.toNat; omega))
  have bot : (sp - (1368 : BitVec 64)).toNat = sp.toNat - 1368 :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr room)
  have dst : (base + 224).toNat = base.toNat + 224 := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by change base.toNat + 224 < 2^64; omega)]
    rfl
  have stack : Writable Extracted.programImage n (sp - 1368) 1368 := entry.stack.of_frame state.frame
  have win : Writable Extracted.programImage n base 0x100 := stack.sub (by omega) (by omega)
  have hbound : x < domain.n := Nat.mod_lt _ (Nat.zero_lt_of_lt bound)
  have hmag := Generate.Generator.Multiply.Prepare.Bases.selectMagnitude hbound
  change (if signByte (first k) = 0 then scalarWords x else _) = scalarWords (first k).natAbs at hmag
  obtain ⟨p, path, rsp, width15, sign, args, r0, keep⟩ :=
    signDispatch (m := n) (k := k) state.firstSign state.secondSign state.arguments
  have prsp := rsp.trans state.rsp
  have pget := congrArg (Value.get 64) prsp
  have pFrame : SplitFrame a m sp src tables digits p n :=
    { state.toSplitFrame with
      rsp := prsp
      arguments := args
      tableBase := (keep 3 (by decide)).trans state.tableBase
      widths := fun i h => by
        by_cases hi : i.val = 15
        · have eq : i = 15 := Fin.ext hi
          exact eq ▸ width15
        · apply (congrArg Value.width (keep i ?_)).trans (state.widths i h)
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega
      control := fun i h =>
        (keep i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega)).trans
          (state.control i h) }
  have pSigns : Signs a m sp src tables digits k p n :=
    ⟨pFrame, (congrArg (Value.get 8) (keep 14 (by decide))).trans state.firstSign,
      (congrArg (Value.get 8) r0).trans state.secondSign, state.firstWords, state.low,
      (congrArg (Value.get 64) (keep 12 (by decide))).trans state.midLow,
      (congrArg (Value.get 64) (keep 5 (by decide))).trans state.midHigh,
      (congrArg (Value.get 64) (keep 13 (by decide))).trans state.high⟩
  by_cases neg : first k < 0
  · have pn : (base - 8).toNat = base.toNat - 8 :=
      BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 8 ≤ base.toNat; omega))
    have below : Writable Extracted.programImage n (base - 8) 8 := stack.sub (by omega) (by omega)
    obtain ⟨q, call, qrsp, di, si, dx, qargs, qkeep⟩ :=
      stageFirst (base := base) pget args state.firstWords win below
    obtain ⟨r, o, run, rrsp, rkeep, rargs, foot, words⟩ :=
      negateStaged (off := 224) entry pFrame (by decide) (by decide) (by decide : (0x10f40e : BitVec 64).toNat < 2^32)
        hbound qargs qkeep qrsp di si dx call
    have oframe : RamWriteFrame m o [scratch sp 0x558] :=
      state.frame.trans foot (negateWritesWithin room (by decide))
    have ostack : Writable Extracted.programImage o (sp - 1368) 1368 := entry.stack.of_frame oframe
    have owin : Writable Extracted.programImage o base 0x100 :=
      ostack.sub (by omega) (by omega)
    obtain ⟨c, tail, crsp, ckeep, cargs⟩ :=
      dispatchSecond (base := base) (k := k) (congrArg (Value.get 64) rrsp) rargs
        ((congrArg (Value.get 8) (rkeep 15 (by decide))).trans sign) owin
    have start : Reaches .l10f3c5 b n .l10f3cd p n := by
      simpa only [neg, ite_true] using path
    simp only [signByte, neg, ite_true, BitVec.reduceEq, ite_false] at hmag
    change scalarWords (if x = 0 then 0 else domain.n - x) = _ at hmag
    rw [hmag] at words
    exact ⟨_, _, start.trans (run.trans tail), finishFirst entry pSigns (crsp.trans rrsp)
      (fun i h => (ckeep i h).trans (rkeep i h)) cargs foot words⟩
  · obtain ⟨c, tail, crsp, ckeep, cargs⟩ := copyFirst (base := base) (k := k) pget args state.firstWords sign win
    have start : Reaches .l10f3c5 b n .l10f44c p n := by
      simpa only [neg, ite_false] using path
    have inDst : InRegions (negateWrites base 224) (base + 224) 32 :=
      ⟨_, .tail _ (.tail _ (.head _)), by dsimp only; omega, by dsimp only; omega, by omega⟩
    have foot := Serializer.storeWords_frame (scalarWords x) (.refl n _) inDst
    have words : WordsAt (storeFour n (base + 224) (scalarWords x)) (base + 224) 64 (scalarWords x) :=
      Serializer.storeWords_wordsAt n (base + 224) (scalarWords x) (by omega)
    simp only [signByte, neg, ite_false, ite_true] at hmag
    have magWords : WordsAt (storeFour n (base + 224) (scalarWords x)) (base + 224) 64
        (scalarWords (first k).natAbs) := by
      rw [← hmag]
      exact words
    exact ⟨_, _, start.trans tail, finishFirst entry pSigns (crsp.trans prsp)
      ckeep cargs foot magWords⟩

end K256.Proofs.Verify.Core.Lincomb.Prepare
