import K256.Proofs.Signing.Nonce.Initialize.Seed.Reduce.State
import K256.Proofs.Common.Tactic
import K256.Proofs.Verify.Core.Affine.Call

namespace K256.Proofs.Signing.Nonce.Initialize

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.DomainParameters

open Generate.Generator.Multiply (scalarWords)

private def selectScratch (sp : BitVec 64) : MemoryRegion := ⟨(sp - 353).toNat, 17⟩

private def selectDestination (sp : BitVec 64) : MemoryRegion := ⟨(sp - 272).toNat, 32⟩

private def selectKeep (a b : Verify.Core.Registers) : Prop :=
  ∀ r : Fin Reg.count, r.val ∈ [2, 5, 6, 7, 13, 14, 22, 39, 50, 51] → b[r] = a[r]

private theorem selectKeep.trans {a b c : Verify.Core.Registers} (ab : selectKeep a b)
    (bc : selectKeep b c) : selectKeep a c :=
  fun i hi => (bc i hi).trans (ab i hi)

private def selectFlag (choose : Bool) : BitVec 64 := if choose then 1 else 0

private def selectSetup (m : Ram) (sp : BitVec 64) (choose : Bool) : Ram :=
  memStore (memStore (memStore m (sp - 353) ((selectFlag choose).setWidth 8))
    (sp - 352) (4 : BitVec 64)) (sp - 344) (4 : BitVec 64)

local macro "select_bounds" : tactic => `(tactic|
  (simp only [selectScratch, selectDestination, Activation.region,
    BitVec.toNat_sub, BitVec.reduceToNat, Nat.reducePow, BitVec.toNat_add, BitVec.toNat_ofNat] at *
   omega))

local macro "select_kept" : tactic => `(tactic|
  (rintro ⟨i, hi⟩ member
   simp only [List.mem_cons, List.not_mem_nil, or_false] at member
   rcases member with eq | eq | eq | eq | eq | eq | eq | eq | eq | eq <;> subst i <;> rfl))

local macro "select_widths" widths:ident : tactic => `(tactic|
  (rintro ⟨i, hi⟩ member
   have width := $widths ⟨i, hi⟩ member
   simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at member
   rcases member with eq | eq | eq | eq | eq | eq <;> subst i <;> first | exact width | rfl))

set_option maxRecDepth 2500 in
private theorem selectEntry {a : Verify.Core.Registers} {m : Ram} {sp : BitVec 64} {choose : Bool}
    (depth : 2208 ≤ sp.toNat) (limit : sp.toNat + 784 < 2^32)
    (stack : Writable Extracted.programImage m (sp - 2208) 2208)
    (rsp : a[4] = ⟨64,sp - 288⟩) (flag : a[8] = ⟨64,selectFlag choose⟩)
    (dstLen : a[6] = ⟨64,4⟩) (srcLen : a[1] = ⟨64,4⟩)
    (widths : ParseSignature.ArgumentWidths a) :
    ∃ b, Verify.Core.Reaches .l127ea0 a m .l127ed0 b (selectSetup m sp choose) ∧
      selectKeep a b ∧ b[4] = ⟨64,sp - 360⟩ ∧ b[0] = ⟨64,selectFlag choose⟩ ∧
      b[1] = ⟨64,0⟩ ∧ ParseSignature.ArgumentWidths b := by
  have rsp' : a[4].get 64 = sp - 288 := congrArg (Value.get 64) rsp
  have lenD : a[6].get 64 = 4 := congrArg (Value.get 64) dstLen
  have lenS : a[1].get 64 = 4 := congrArg (Value.get 64) srcLen
  have flag' : a[8].get 64 = selectFlag choose := congrArg (Value.get 64) flag
  have flagWidth : ((selectFlag choose).setWidth 8).setWidth 64 = selectFlag choose := by
    cases choose <;> rfl
  have byte : Writable Extracted.programImage m (sp - 353) 1 :=
    stack.sub (by select_bounds) (by select_bounds)
  have byteRead : LoadOk (memStore m (sp - 353) ((selectFlag choose).setWidth 8)) (sp - 353) 1 :=
    LoadOk.of_region (byte.memStore _ _).readable (Nat.le_refl _) (Nat.le_refl _)
  have storeByte : StoreOk Extracted.programImage m (sp - 353) 1 0x127ea4 5 := by
    slot_guard using (fun x hx => Verify.Core.Affine.coreText x (code_l127ea0 x hx))
  have len1 : Writable Extracted.programImage
      (memStore m (sp - 353) ((selectFlag choose).setWidth 8)) (sp - 352) 8 :=
    (stack.sub (by select_bounds) (by select_bounds)).memStore _ _
  have store1 : StoreOk Extracted.programImage
      (memStore m (sp - 353) ((selectFlag choose).setWidth 8)) (sp - 352) 8 0x127eb3 5 := by
    slot_guard using (fun x hx => Verify.Core.Affine.coreText x (code_l127ea0 x hx))
  have len2 : Writable Extracted.programImage
      (memStore (memStore m (sp - 353) ((selectFlag choose).setWidth 8)) (sp - 352) (4 : BitVec 64))
      (sp - 344) 8 :=
    ((stack.sub (by select_bounds) (by select_bounds)).memStore _ _).memStore _ _
  have store2 : StoreOk Extracted.programImage
      (memStore (memStore m (sp - 353) ((selectFlag choose).setWidth 8)) (sp - 352) (4 : BitVec 64))
      (sp - 344) 8 0x127eb8 5 := by
    slot_guard using (fun x hx => Verify.Core.Affine.coreText x (code_l127ea0 x hx))
  have first : ∃ b : Verify.Core.Registers,
      Verify.Core.Reaches .l127ea0 a m .l127ec2 b (selectSetup m sp choose) ∧
        selectKeep a b ∧ b[4] = ⟨64,sp - 360⟩ ∧ b[0] = ⟨64,selectFlag choose⟩ ∧
        b[1] = ⟨64,4⟩ ∧ ParseSignature.ArgumentWidths b := by
    refine ⟨?_, .single ?run, ?keep, ?sp, ?flag, ?index, ?widths⟩
    case run =>
      change (program.runBlock _ _).next _ [] = _
      cfg_eval [rsp', flag', lenD, lenS, cmpSpec_ZF]
      simp only [memLoad_memStore_same _ _ _ (by decide : 8 % 8 = 0) (by decide : 8 ≤ 128),
        flagWidth, selectSetup]
      simp only [ite_eq_left storeByte, ite_eq_left byteRead, ite_eq_left store1, ite_eq_left store2]
      rfl
    case keep => select_kept
    case sp => rfl
    case flag => rfl
    case index => exact srcLen
    case widths => select_widths widths
  obtain ⟨b, run, keep, bp, bflag, index, bw⟩ := first
  have bd : b[6].get 64 = 4 := congrArg (Value.get 64) ((keep 6 (by decide)).trans dstLen)
  have second : ∃ c, Verify.Core.Reaches .l127ec2 b (selectSetup m sp choose) .l127ec7 c
      (selectSetup m sp choose) ∧ selectKeep b c ∧ c[4] = ⟨64,sp - 360⟩ ∧
      c[0] = ⟨64,selectFlag choose⟩ ∧ c[1] = ⟨64,4⟩ ∧ ParseSignature.ArgumentWidths c := by
    refine ⟨?_, .single ?run, ?keep, ?sp, ?flag, ?index, ?widths⟩
    case run =>
      change (program.runBlock _ _).next _ [] = _
      cfg_eval [bd]
      rfl
    case keep => select_kept
    case sp => exact bp
    case flag => exact bflag
    case index => exact index
    case widths => select_widths bw
  obtain ⟨c, next, keep', cp, cflag, ci, cw⟩ := second
  have ci' : c[1].get 64 = 4 := congrArg (Value.get 64) ci
  refine ⟨?_, run.trans (next.trans (.single ?run)), (keep.trans keep').trans ?keep, ?sp, ?flag,
    ?index, ?widths⟩
  case run =>
    change (program.runBlock _ _).next _ [] = _
    cfg_eval [ci']
    rfl
  case keep => select_kept
  case sp => exact cp
  case flag => exact cflag
  case index => rfl
  case widths => select_widths cw


private def selectWord (sp : BitVec 64) (m : Ram) (choose : Bool) (i : Nat) : BitVec 64 :=
  if choose then memLoad m (wordAddr (sp - 176) 64 i) 64
  else memLoad m (wordAddr (sp - 272) 64 i) 64

private def selectLabel (i : Nat) : Label := if i = 4 then .l127eea else .l127ed0

private theorem selectAddr {sp : BitVec 64} {d i : Nat}
    (depth : 2208 ≤ sp.toNat) (limit : sp.toNat + 784 < 2^32)
    (hd : d ≤ 2208) (hi : i < 4) :
    (wordAddr (sp - BitVec.ofNat 64 d) 64 i).toNat = sp.toNat - d + 8*i := by
  have dd : (BitVec.ofNat 64 d).toNat = d := Nat.mod_eq_of_lt (by omega)
  have ii : (BitVec.ofNat 64 (8*i)).toNat = 8*i := Nat.mod_eq_of_lt (by omega)
  have below : (BitVec.ofNat 64 d).toNat ≤ sp.toNat := by omega
  simp only [wordAddr, Nat.reduceDiv, BitVec.toNat_add, BitVec.toNat_sub_of_le below, ii, dd]
  exact Nat.mod_eq_of_lt (by omega)

set_option maxRecDepth 2500 in
private theorem selectIteration {a : Verify.Core.Registers} {m : Ram} {sp : BitVec 64}
    {choose : Bool} {i : Nat}
    (depth : 2208 ≤ sp.toNat) (limit : sp.toNat + 784 < 2^32) (hi : i < 4)
    (stack : Writable Extracted.programImage m (sp - 2208) 2208)
    (ptrS : a[2] = ⟨64,sp - 176⟩) (ptrD : a[7] = ⟨64,sp - 272⟩)
    (len : a[6] = ⟨64,4⟩) (flag : a[0] = ⟨64,selectFlag choose⟩)
    (idx : a[1] = ⟨64,BitVec.ofNat 64 i⟩) :
    ∃ b, Verify.Core.Reaches .l127ed0 a m (selectLabel (i+1)) b
        (memStore m (wordAddr (sp - 272) 64 i) (selectWord sp m choose i)) ∧
      selectKeep a b ∧ b[4] = a[4] ∧ b[0] = a[0] ∧
      b[1] = ⟨64,BitVec.ofNat 64 (i+1)⟩ ∧ ParseSignature.ArgumentWidths b := by
  have ptrS' : a[2].get 64 = sp - 176 := congrArg (Value.get 64) ptrS
  have ptrD' : a[7].get 64 = sp - 272 := congrArg (Value.get 64) ptrD
  have len' : a[6].get 64 = 4 := congrArg (Value.get 64) len
  have flag' : a[0].get 64 = selectFlag choose := congrArg (Value.get 64) flag
  have idx' : a[1].get 64 = BitVec.ofNat 64 i := congrArg (Value.get 64) idx
  have wS : Writable Extracted.programImage m (wordAddr (sp - 176) 64 i) 8 := by
    have addr := selectAddr depth limit (d := 176) (by decide) hi
    change (wordAddr (sp - 176) 64 i).toNat = _ at addr
    exact stack.sub (by select_bounds) (by select_bounds)
  have wD : Writable Extracted.programImage m (wordAddr (sp - 272) 64 i) 8 := by
    have addr := selectAddr depth limit (d := 272) (by decide) hi
    change (wordAddr (sp - 272) 64 i).toNat = _ at addr
    exact stack.sub (by select_bounds) (by select_bounds)
  have loadS : LoadOk m (wordAddr (sp - 176) 64 i) 8 := by slot_guard using code_l127ed0
  have loadD : LoadOk m (wordAddr (sp - 272) 64 i) 8 := by slot_guard using code_l127ed0
  have storeD : StoreOk Extracted.programImage m (wordAddr (sp - 272) 64 i) 8 0x127ede 4 := by
    slot_guard using (fun x hx => Verify.Core.Affine.coreText x (code_l127ed0 x hx))
  have offset (base : BitVec 64) : base + ((BitVec.ofNat 64 i) <<< 3) = wordAddr base 64 i := by
    simp only [wordAddr, Nat.reduceDiv, BitVec.ofNat_mul]
    change base + ((BitVec.ofNat 64 i) <<< 3) = base + ((8 : BitVec 64) * BitVec.ofNat 64 i)
    rw [BitVec.mul_comm (8 : BitVec 64)]
    exact congrArg (base + ·) (BitVec.shiftLeft_eq_mul_twoPow _ _)
  have increment : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i+1) := by
    rw [BitVec.ofNat_add]
    rfl
  have cmp : (4 == BitVec.ofNat 64 (i + 1)) = decide (i+1 = 4) := by
    obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    all_goals decide
  have test : (!(testFlags ((selectFlag choose).setWidth 8 &&& (selectFlag choose).setWidth 8)).ZF.getD false) =
      choose := by cases choose <;> rfl
  refine ⟨?_, .single ?run, ?same, ?sp, ?flag, ?idx, ?widths⟩
  case run =>
    change (program.runBlock _ _).next _ [] = _
    cfg_eval [ptrS', ptrD', len', flag', idx', cmpSpec_ZF]
    simp only [offset, ite_eq_left loadS, ite_eq_left loadD, ite_eq_left storeD, test, increment,
      selectWord, selectLabel]
    by_cases last : i+1 = 4
    · have jump : ¬ ((! (4 == BitVec.ofNat 64 (i+1))) = true) := by rw [cmp]; simp [last]
      rw [ite_eq_right jump, ite_eq_left last]
      rfl
    · have jump : (! (4 == BitVec.ofNat 64 (i+1))) = true := by rw [cmp]; simp [last]
      rw [ite_eq_left jump, ite_eq_right last]
      rfl
  case same => select_kept
  case sp => rfl
  case flag => rfl
  case idx => rfl
  case widths =>
    rintro ⟨i, hi⟩ hm
    simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | rfl | exact congrArg Value.width ptrS | exact congrArg Value.width ptrD |
      exact congrArg Value.width len


private def selectWords (src dst : Vector (BitVec 64) 4) (choose : Bool) (i : Nat) :
    Vector (BitVec 64) 4 :=
  Vector.ofFn fun j => if j.val < i ∧ choose = true then src[j] else dst[j]

private theorem selectWords_zero (src dst : Vector (BitVec 64) 4) (choose : Bool) :
    selectWords src dst choose 0 = dst := by
  ext j hj
  simp [selectWords]

private theorem selectWords_four (src dst : Vector (BitVec 64) 4) (choose : Bool) :
    selectWords src dst choose 4 = if choose then src else dst := by
  ext j hj
  cases choose <;> simp [selectWords]

private theorem selectWords_succ {sp : BitVec 64} {m : Ram} {i : Nat}
    {src dst : Vector (BitVec 64) 4} {choose : Bool}
    (depth : 2208 ≤ sp.toNat) (limit : sp.toNat + 784 < 2^32) (hi : i < 4)
    (source : WordsAt m (sp - 176) 64 src)
    (current : WordsAt m (sp - 272) 64 (selectWords src dst choose i)) :
    WordsAt (memStore m (wordAddr (sp - 272) 64 i) (selectWord sp m choose i))
      (sp - 272) 64 (selectWords src dst choose (i+1)) := by
  have writableSize : (sp - 272).toNat + 64 / 8 * 4 ≤ 2^64 := by select_bounds
  have w := current.write_set hi (selectWord sp m choose i) (by decide) (by decide)
    (by decide) writableSize
  suffices (selectWords src dst choose i).set i (selectWord sp m choose i) hi =
      selectWords src dst choose (i+1) by rwa [this] at w
  apply Vector.ext
  intro j hj
  by_cases same : i = j
  · subst j
    have fromSrc : memLoad m (wordAddr (sp - 176#64) 64 i) 64 = src[i] := source i hi
    have fromDst := current i hi
    simp [selectWords] at fromDst
    simp [selectWords, selectWord, fromSrc, fromDst]
  · have inPrefix : j < i + 1 ↔ j < i := by omega
    simp [selectWords, same, inPrefix]

private theorem selectLoop {sp : BitVec 64} {a : Verify.Core.Registers} {m : Ram}
    {src dst : Vector (BitVec 64) 4} {choose : Bool} {i : Nat}
    (depth : 2208 ≤ sp.toNat) (limit : sp.toNat + 784 < 2^32) (hi : i ≤ 4)
    (stack : Writable Extracted.programImage m (sp - 2208) 2208)
    (ptrS : a[2] = ⟨64,sp - 176⟩) (ptrD : a[7] = ⟨64,sp - 272⟩)
    (len : a[6] = ⟨64,4⟩) (flag : a[0] = ⟨64,selectFlag choose⟩)
    (idx : a[1] = ⟨64,BitVec.ofNat 64 i⟩) (widths : ParseSignature.ArgumentWidths a)
    (source : WordsAt m (sp - 176) 64 src)
    (current : WordsAt m (sp - 272) 64 (selectWords src dst choose i)) :
    ∃ b n, Verify.Core.Reaches (selectLabel i) a m .l127eea b n ∧
      RamWriteFrame m n [selectDestination sp] ∧
      selectKeep a b ∧ b[4] = a[4] ∧ ParseSignature.ArgumentWidths b ∧
      WordsAt n (sp - 272) 64 (if choose then src else dst) := by
  by_cases last : i = 4
  · subst i
    rw [selectWords_four] at current
    exact ⟨a, m, .refl _, .refl _ _, fun _ _ => rfl, rfl, widths, current⟩
  have indexBound : i < 4 := by omega
  obtain ⟨b, run, same, rsp, newFlag, newIdx, newWidths⟩ :=
    selectIteration depth limit indexBound stack ptrS ptrD len flag idx
  have addr := selectAddr depth limit (d := 272) (by decide) indexBound
  change (wordAddr (sp - 272) 64 i).toNat = _ at addr
  let n := memStore m (wordAddr (sp - 272) 64 i) (selectWord sp m choose i)
  have memory : RamWriteFrame m n [selectDestination sp] := by
    apply (RamWriteFrame.refl _ _).memStore
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    simp only [InRegion]
    select_bounds
  have apart : RangeApart (wordAddr (sp - 272) 64 i) 8 (sp - 176) 32 :=
    RangeApart.of_toNat (by select_bounds) (by select_bounds) (.inl (by select_bounds))
  obtain ⟨c, p, rest, writes, same', rsp', w, result⟩ := selectLoop depth limit
    (i := i+1) (by omega) (stack.of_frame memory)
    ((same 2 (by decide)).trans ptrS) ((same 7 (by decide)).trans ptrD)
    ((same 6 (by decide)).trans len) (newFlag.trans flag) newIdx newWidths
    (source.write_apart _ _ apart) (selectWords_succ depth limit indexBound source current)
  rw [show selectLabel i = .l127ed0 from ite_eq_right last]
  exact ⟨c, p, run.trans rest, memory.trans writes (fun r hr => ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩),
    same.trans same', rsp'.trans rsp, w, result⟩
termination_by 4 - i


set_option maxRecDepth 2200 in
private theorem selectReturn {sp : BitVec 64} {a : Verify.Core.Registers} {m : Ram}
    (rsp : a[4] = ⟨64,sp - 360⟩) (ret : memLoad m (sp - 288) 64 = 0x10126c)
    (slot : Readable m (sp - 288) 8) (widths : ParseSignature.ArgumentWidths a) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l127eea,a,m⟩,[]⟩ out ∧
      out.tag = some ⟨64,0x10126c⟩ ∧ out.store = m ∧ selectKeep a out.values ∧
      out.values[4] = ⟨64,sp - 280⟩ ∧ ParseSignature.ArgumentWidths out.values := by
  have sp' : a[4].get 64 = sp - 360 := congrArg (Value.get 64) rsp
  refine ⟨?_, .done ?run, ?tag, ?mem, ?keep, ?sp, ?widths⟩
  case run =>
    unfold Program.step
    cfg_eval [sp']
    segment_words [ret]
    have ok : LoadOk m (sp - 288) 8 ∧ (0x10126c : Nat) < 2^32 :=
      ⟨by slot_guard using code_l127eea, by decide⟩
    rw [ite_eq_left ok]
    rfl
  case tag => rfl
  case mem => rfl
  case keep => select_kept
  case sp => rfl
  case widths => select_widths widths


private theorem selectSetupFrame {sp : BitVec 64} {m : Ram} {choose : Bool}
    (depth : 2208 ≤ sp.toNat) (limit : sp.toNat + 784 < 2^32) :
    RamWriteFrame m (selectSetup m sp choose) [selectScratch sp, selectDestination sp] := by
  unfold selectSetup
  apply ((RamWriteFrame.refl _ _).memStore _ ?_).memStore _ ?_ |>.memStore _ ?_
  all_goals
    refine ⟨selectScratch sp, List.mem_cons_self, ?_⟩
    simp only [InRegion]
    select_bounds

private theorem selectOutside {sp a : BitVec 64} {n : Nat}
    (depth : 2208 ≤ sp.toNat) (limit : sp.toNat + 784 < 2^32)
    (bounded : a.toNat + n ≤ 2^64)
    (scratch : a.toNat + n ≤ sp.toNat - 353 ∨ sp.toNat - 336 ≤ a.toNat)
    (dst : a.toNat + n ≤ sp.toNat - 272 ∨ sp.toNat - 240 ≤ a.toNat) :
    Outside [selectScratch sp, selectDestination sp] a n := by
  refine ⟨bounded, ?_⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rcases scratch with lo | hi
    · exact .inl (by select_bounds)
    · exact .inr (by select_bounds)
  · rcases dst with lo | hi
    · exact .inl (by select_bounds)
    · exact .inr (by select_bounds)

set_option maxRecDepth 3000 in
theorem selectDigest {fr : Activation} {a : Verify.Core.Registers} {m : Ram} {x : Nat}
    (depth : 2208 ≤ fr.rsp.toNat) (low : fr.low = fr.rsp - 2208)
    (limit : fr.rsp.toNat + 784 < 2^32)
    (selected : (if x < Secp256k1.domain.n then scalarWords x else
      Common.Invert.ModularShift.words (digestDifference x).1) = scalarWords (x % Secp256k1.domain.n))
    (h : DigestSelect fr a m x) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l127ea0,a,m⟩,[]⟩ out ∧
      out.tag = some ⟨64,0x10126c⟩ ∧ ReducedLimbs fr out.values out.store (x % Secp256k1.domain.n) := by
  let choose := decide (x < Secp256k1.domain.n)
  have flag : a[8] = ⟨64,selectFlag choose⟩ := by
    simpa only [selectFlag, choose, decide_eq_true_eq] using h.flag
  have atoms := h.atoms
  simp only [Fn100ea0.frameAt, Fn100ea0.frameAtG1, Atom.All, Atom.Holds] at atoms
  obtain ⟨_, df, r14, mx, ft, fc, w9, wdx, wsi, wdi, wbx, w12, w13, w14, w15, wbp,
    callerRead, callerRet, retLow, stack, room, align, rd1, w1, rd2, w2, rd3, w3, rd4, w4,
    separation, _⟩ := atoms
  let setup := selectSetup m fr.rsp choose
  have setupFrame : RamWriteFrame m setup [selectScratch fr.rsp, selectDestination fr.rsp] :=
    selectSetupFrame depth limit
  have source : WordsAt setup (fr.rsp - 176) 64 (scalarWords x) := by
    intro i hi
    have addr := selectAddr depth limit (d := 176) (by decide) hi
    change (wordAddr (fr.rsp - 176) 64 i).toNat = _ at addr
    rw [setupFrame.memLoad_eq (selectOutside depth limit (by select_bounds)
      (.inr (by select_bounds)) (.inr (by select_bounds)))]
    exact h.originalWords i hi
  have target : WordsAt setup (fr.rsp - 272) 64
      (selectWords (scalarWords x) (Common.Invert.ModularShift.words (digestDifference x).1) choose 0) := by
    rw [selectWords_zero]
    unfold setup selectSetup
    apply ((h.subtracted.write_apart _ _ ?_).write_apart _ _ ?_).write_apart _ _ ?_
    all_goals apply RangeApart.of_toNat (by select_bounds) (by select_bounds) (.inl (by select_bounds))
  obtain ⟨b, entry, keepB, spB, flagB, indexB, widthsB⟩ :=
    selectEntry depth limit stack h.rsp flag h.dstLen h.srcLen h.widths
  obtain ⟨c, n, loop, loopFrame, keepC, spC, widthsC, words⟩ := selectLoop depth limit (i := 0)
    (by decide) (stack.of_frame setupFrame) ((keepB 2 (by decide)).trans h.src)
    ((keepB 7 (by decide)).trans h.dst) ((keepB 6 (by decide)).trans h.dstLen)
    flagB indexB widthsB source target
  have writes : RamWriteFrame m n [selectScratch fr.rsp, selectDestination fr.rsp] := by
    apply setupFrame.trans loopFrame
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, .tail _ (.head _), Nat.le_refl _, Nat.le_refl _⟩
  have ret : memLoad n (fr.rsp - 288) 64 = 0x10126c :=
    (writes.memLoad_eq (selectOutside depth limit (by select_bounds)
      (.inr (by select_bounds)) (.inl (by select_bounds)))).trans h.ret
  have stackN := stack.of_frame writes
  have retRead : Readable n (fr.rsp - 288) 8 := stackN.readable.sub (by select_bounds) (by select_bounds)
  obtain ⟨out, runs, tag, outStore, keepO, outSP, widths⟩ :=
    selectReturn (spC.trans spB) ret retRead widthsC
  have keep := keepB.trans (keepC.trans keepO)
  have frame := h.writes.trans writes (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [List.mem_singleton]
    refine ⟨fr.region, rfl, ?_⟩
    rcases hr with rfl | rfl
    all_goals simp only [Activation.region, low]; constructor <;> select_bounds)
  have saved {d : Nat} (hd : d ≤ 112) :
      memLoad n (fr.rsp - BitVec.ofNat 64 d) 64 = memLoad m (fr.rsp - BitVec.ofNat 64 d) 64 := by
    have dd : (BitVec.ofNat 64 d).toNat = d := Nat.mod_eq_of_lt (by omega)
    have below : (BitVec.ofNat 64 d).toNat ≤ fr.rsp.toNat := by rw [dd]; omega
    have addr : (fr.rsp - BitVec.ofNat 64 d).toNat = fr.rsp.toNat - d := by
      rw [BitVec.toNat_sub_of_le below, dd]
    exact writes.memLoad_eq (selectOutside depth limit (by omega)
      (.inr (by omega)) (.inr (by omega)))
  have tables {ptr : BitVec 64} (lo : 0x203dd0 ≤ ptr.toNat) (hi : ptr.toNat + 8 ≤ 0x2046c8 - 353) :
      memLoad n ptr 64 = memLoad m ptr 64 := by
    apply writes.memLoad_eq
    apply selectOutside depth limit (by omega)
    · rcases separation with apart | apart
      · exact .inl (by omega)
      · exact .inr (by omega)
    · rcases separation with apart | apart
      · exact .inl (by omega)
      · exact .inr (by omega)
  have savedReg (i : Fin Reg.count) (hi : i.val ∈ [14,22,39,50,51]) :
      out.values[i] = (a.set 4 ⟨64,fr.rsp - 280⟩)[i] := by
    have member : i.val ∈ [2, 5, 6, 7, 13, 14, 22, 39, 50, 51] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
      omega
    have ne : 4 ≠ i.val := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      omega
    change out.values[i.val] = (a.set 4 ⟨64,fr.rsp - 280⟩)[i.val]
    rw [Vector.getElem_set_ne (by decide) i.isLt ne]
    exact keep i member
  have callerRetN : memLoad n fr.rsp 64 = fr.ret :=
    (writes.memLoad_eq (selectOutside depth limit (by omega) (.inr (by omega)) (.inr (by omega)))).trans callerRet
  refine ⟨out, Program.Exec.of_sem ((entry.trans loop).exec runs.sem), tag, ?_, (keep 5 (by decide)).trans h.rbp,
    (congrArg Value.width (keep 13 (by decide))).trans h.r13Width, ?_, widths⟩
  · refine ⟨?_, outStore ▸ frame⟩
    rw [outStore]
    simp only [Fn100ea0.frameAt, Fn100ea0.frameAtG1, Atom.All, Atom.Holds]
    exact ⟨outSP, (savedReg 22 (by decide)).trans df, (savedReg 14 (by decide)).trans r14,
      (savedReg 39 (by decide)).trans mx, (savedReg 50 (by decide)).trans ft,
      (savedReg 51 (by decide)).trans fc,
      (saved (d := 112) (by decide)).trans w9, (saved (d := 104) (by decide)).trans wdx,
      (saved (d := 96) (by decide)).trans wsi, (saved (d := 88) (by decide)).trans wdi,
      (saved (d := 48) (by decide)).trans wbx, (saved (d := 40) (by decide)).trans w12,
      (saved (d := 32) (by decide)).trans w13, (saved (d := 24) (by decide)).trans w14,
      (saved (d := 16) (by decide)).trans w15, (saved (d := 8) (by decide)).trans wbp,
      callerRead.of_frame writes, callerRetN, retLow, stackN, room, align,
      rd1.of_frame writes, (tables (by decide) (by decide)).trans w1,
      rd2.of_frame writes, (tables (by decide) (by decide)).trans w2,
      rd3.of_frame writes, (tables (by decide) (by decide)).trans w3,
      rd4.of_frame writes, (tables (by decide) (by decide)).trans w4, separation, trivial⟩
  · rw [outStore, ← selected]
    simpa only [choose, decide_eq_true_eq] using words

end K256.Proofs.Signing.Nonce.Initialize
