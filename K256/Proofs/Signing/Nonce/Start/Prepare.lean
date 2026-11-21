import K256.Proofs.Signing.Nonce.Start.State
import K256.Proofs.Signing.Nonce.Start.Prepare.Scalar
import K256.Proofs.Verify.Hash.Output
import K256.Proofs.Verify.Choice
import K256.Proofs.Generate.Wrapper.Scalar.Octets

namespace K256.Proofs.Signing.Nonce.Start

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Verify.LIR
  Standards.SECG.DomainParameters.Secp256k1 Standards.NIST.SHA2
open Generate.Generator.Multiply (scalarWords)
open Generate.Wrapper (writeScalarWords scalarOctets)
open Verify.Core (Registers Reaches)
open Verify.Hash

private def orderOffset : Nat → Nat
  | 0 => 600
  | 1 => 592
  | 2 => 616
  | _ => 608

private def orderWord : Nat → BitVec 64
  | 0 => 0xbaaedce6af48a03b
  | 1 => 0xbfd25e8cd0364141
  | 2 => 0xffffffffffffffff
  | _ => 0xfffffffffffffffe

private def storeOrder (m : Ram) (sp : BitVec 64) : Nat → Ram
  | 0 => m
  | i + 1 => memStore (storeOrder m sp i) (sp + BitVec.ofNat 64 (orderOffset i)) (orderWord i)

private theorem offsetNat {sp : BitVec 64} (limit : sp.toNat + 1160 < 2^32)
    (off : Nat) (h : off ≤ 1160) : (sp + BitVec.ofNat 64 off).toNat = sp.toNat + off := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega),
    Nat.mod_eq_of_lt (by omega)]

private theorem wordOffset (sp off : BitVec 64) (width i : Nat) :
    wordAddr (sp + off) width i =
      sp + BitVec.ofNat 64 (off.toNat + width / 8 * i) := by
  rw [wordAddr, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_assoc]

private theorem storeOrder_reads {m : Ram} {sp : BitVec 64}
    (limit : sp.toNat + 1160 < 2^32) :
    WordsAt (storeOrder m sp 4) (sp+592) 64 (scalarWords domain.n) := by
  have apart (i j : Nat) (hi : i ≤ 1160) (hj : j ≤ 1160)
      (h : i + 8 ≤ j ∨ j + 8 ≤ i) :
      RangeApart (sp + BitVec.ofNat 64 i) 8 (sp + BitVec.ofNat 64 j) 8 := by
    apply RangeApart.of_toNat <;> simp only [offsetNat limit i hi, offsetNat limit j hj] <;> omega
  have readApart (t : Ram) (v : BitVec 64) (i j : Nat) (hi : i ≤ 1160) (hj : j ≤ 1160)
      (h : i+8 ≤ j ∨ j+8 ≤ i) :
      memLoad (memStore t (sp + BitVec.ofNat 64 i) v) (sp + BitVec.ofNat 64 j) 64 =
        memLoad t (sp + BitVec.ofNat 64 j) 64 :=
    memLoad_memStore_of_rangeApart _ _ _ _ _ (apart i j hi hj h)
  intro i hi
  simp only [wordOffset, BitVec.reduceToNat, Nat.reduceDiv, Vector.getElem_ofFn]
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl|rfl|rfl|rfl
  all_goals simp only [storeOrder, orderOffset, orderWord, Nat.reduceMul, Nat.reduceAdd]
  · rw [readApart _ _ 608 592 (by decide) (by decide) (by decide),
      readApart _ _ 616 592 (by decide) (by decide) (by decide),
      memLoad_memStore_same _ _ _ (by decide) (by decide)]
    decide +kernel
  · rw [readApart _ _ 608 600 (by decide) (by decide) (by decide),
      readApart _ _ 616 600 (by decide) (by decide) (by decide),
      readApart _ _ 592 600 (by decide) (by decide) (by decide),
      memLoad_memStore_same _ _ _ (by decide) (by decide)]
    decide +kernel
  · rw [memLoad_memStore_same _ _ _ (by decide) (by decide)]
    decide +kernel
  · rw [readApart _ _ 608 616 (by decide) (by decide) (by decide),
      memLoad_memStore_same _ _ _ (by decide) (by decide)]
    decide +kernel

private theorem scalarStoreFrame {m : Ram} {dst : BitVec 64} {word : Nat → BitVec 64}
    {regions : List MemoryRegion} (n : Nat)
    (within : ∀ i < n, InRegions regions (wordAddr dst 64 i) 8) :
    RamWriteFrame m (writeScalarWords dst word m n) regions := by
  induction n with
  | zero => exact .refl _ _
  | succ n ih => exact (ih fun i hi => within i (by omega)).memStore _ (within n (by omega))

private theorem scalarStoreReads {m : Ram} {dst : BitVec 64} {word : Nat → BitVec 64}
    {n : Nat} (low : dst.toNat + 8 * n ≤ 2^32) :
    ∀ i < n, memLoad (writeScalarWords dst word m n) (wordAddr dst 64 i) 64 = word i := by
  induction n with
  | zero => omega
  | succ n ih =>
    intro i hi
    change memLoad (memStore (writeScalarWords dst word m n) (wordAddr dst 64 n) (word n))
      (wordAddr dst 64 i) 64 = word i
    rcases Nat.lt_or_eq_of_le (show i ≤ n by omega) with lt | rfl
    · have addr (j : Nat) (hj : j ≤ n) :
          (wordAddr dst 64 j).toNat = dst.toNat + 8 * j := by
        simp only [wordAddr, Nat.reduceDiv, BitVec.toNat_add, BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (a := 8 * j) (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [memLoad_memStore_of_rangeApart]
      · exact ih (by omega) i lt
      · apply RangeApart.of_toNat <;> simp only [addr n (by omega), addr i (by omega)] <;> omega
    · exact memLoad_memStore_same _ _ _ (by decide) (by decide)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 350000 in
private theorem prepareBlock {a : Registers} {m : Ram} {sp : BitVec 64} {digest : Array UInt32}
    (rspBits : a[4].get 64 = sp)
    (hashLoad : ∀ i < 8, LoadOk m (sp + BitVec.ofNat 64 (72+4*i)) 4)
    (hashWord : ∀ i < 8, memLoad m (sp + BitVec.ofNat 64 (72+4*i)) 32 = digest[i]!.toBitVec)
    (digestStore : ∀ i off len, i < 8 → off + len ≤ bytes_l105758.length →
      StoreOk Extracted.programImage (storeDigestWords m (sp+352) digest i)
        (sp + BitVec.ofNat 64 (352+4*i)) 4 (0x105758 + BitVec.ofNat 64 off) len)
    (orderStore : ∀ i off len, i < 4 → off + len ≤ bytes_l105758.length →
      StoreOk Extracted.programImage (storeOrder (storeDigestWords m (sp+352) digest 8) sp i)
        (sp + BitVec.ofNat 64 (orderOffset i)) 8 (0x105758 + BitVec.ofNat 64 off) len)
    (keyLoad : LoadOk (storeOrder (storeDigestWords m (sp+352) digest 8) sp 4) (sp+344) 8)
    (keyPtr : memLoad (storeOrder (storeDigestWords m (sp+352) digest 8) sp 4) (sp+344) 64 = sp+1016)
    (pushStore : StoreOk Extracted.programImage (storeOrder (storeDigestWords m (sp+352) digest 8) sp 4)
      (sp-8) 8 0x105815 5) :
    let pushed := memStore (storeOrder (storeDigestWords m (sp+352) digest 8) sp 4) (sp-8)
      (0x10581a : BitVec 64)
    ∃ child, program.runBlock (dialect Extracted.programImage) ⟨.l105758,a,m⟩ =
      .call ⟨.l109e30,child,pushed⟩ (Verify.resumeAt .l10581a 0x10581a) ∧
      child[4].get 64 = sp-8 ∧ child[6].get 64 = sp+1016 ∧ child[7].get 64 = sp+8 ∧
      child[12] = ⟨64,sp+8⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,13,14,15,22,39,50,51] → child[i] = a[i]) := by
  dsimp only
  have blockLen : bytes_l105758.length = 194 := by decide +kernel
  have l0 := hashLoad 0 (by decide)
  have l1 := hashLoad 1 (by decide)
  have l2 := hashLoad 2 (by decide)
  have l3 := hashLoad 3 (by decide)
  have l4 := hashLoad 4 (by decide)
  have l5 := hashLoad 5 (by decide)
  have l6 := hashLoad 6 (by decide)
  have l7 := hashLoad 7 (by decide)
  have w0 := hashWord 0 (by decide)
  have w1 := hashWord 1 (by decide)
  have w2 := hashWord 2 (by decide)
  have w3 := hashWord 3 (by decide)
  have w4 := hashWord 4 (by decide)
  have w5 := hashWord 5 (by decide)
  have w6 := hashWord 6 (by decide)
  have w7 := hashWord 7 (by decide)
  have g0 := digestStore 0 54 7 (by decide) (by rw [blockLen]; decide)
  have g1 := digestStore 1 61 7 (by decide) (by rw [blockLen]; decide)
  have g2 := digestStore 2 68 7 (by decide) (by rw [blockLen]; decide)
  have g3 := digestStore 3 75 7 (by decide) (by rw [blockLen]; decide)
  have g4 := digestStore 4 82 7 (by decide) (by rw [blockLen]; decide)
  have g5 := digestStore 5 89 8 (by decide) (by rw [blockLen]; decide)
  have g6 := digestStore 6 97 8 (by decide) (by rw [blockLen]; decide)
  have g7 := digestStore 7 105 8 (by decide) (by rw [blockLen]; decide)
  have o0 := orderStore 0 123 8 (by decide) (by rw [blockLen]; decide)
  have o1 := orderStore 1 141 8 (by decide) (by rw [blockLen]; decide)
  have o2 := orderStore 2 149 12 (by decide) (by rw [blockLen]; decide)
  have o3 := orderStore 3 161 12 (by decide) (by rw [blockLen]; decide)
  simp only [Nat.reduceMul, Nat.reduceAdd]
    at l0 l1 l2 l3 l4 l5 l6 l7 w0 w1 w2 w3 w4 w5 w6 w7
  simp only [storeOrder, orderOffset, orderWord, storeDigestWords, wordOffset,
    Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd, BitVec.reduceToNat, BitVec.ofNat_eq_ofNat,
    BitVec.reduceAdd] at g0 g1 g2 g3 g4 g5 g6 g7 o0 o1 o2 o3 keyLoad keyPtr pushStore
  refine ⟨?child, ?eval, ?_, ?_, ?_, ?_, ?_⟩
  case eval =>
    cfg_eval [rspBits]
    simp only [BitVec.ofNat_eq_ofNat, w0, w1, w2, w3, w4, w5, w6, w7,
      l0, l1, l2, l3, l4, l5, l6, l7, g0, g1, g2, g3, g4, g5, g6, g7,
      o0, o1, o2, o3, keyLoad, keyPtr, pushStore, ↓reduceIte]
    simp only [storeOrder, orderOffset, orderWord, storeDigestWords,
      wordOffset, Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd, BitVec.reduceToNat,
      BitVec.ofNat_eq_ofNat]
    rfl
  all_goals try rfl
  · rintro ⟨i,hi⟩ hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

set_option maxRecDepth 2048 in
set_option maxHeartbeats 350000 in
set_option linter.unusedVariables false in
theorem prepare {a : Registers} {m : Ram} {sp : BitVec 64} {d : Nat} {message : ByteArray}
    (rsp : a[4] = ⟨64,sp⟩) (df : a[22] = ⟨1,0⟩)
    (r13 : a[13] = ⟨64,sp + 256⟩)
    (widths : ∀ i : Fin Reg.count, i.val ∈ [3,5,14,15] → a[i].width = 64)
    (mxcsr : a[39].width = 32) (ftw : a[50].width = 16) (fcw : a[51].width = 16)
    (image : ∀ b ∈ Extracted.programImage, m[b.1]? = some b.2)
    (stack : Writable Extracted.programImage m (sp-2232) 3392)
    (depth : 2232 ≤ sp.toNat) (limit : sp.toNat + 1160 < 2^32) (align : sp.toNat % 16 = 0)
    (hash : Compression.StateAt m (sp+72) (compressBlocks initialHash (bytePadding message)))
    (key : memLoad m (sp+344) 64 = sp+1016)
    (secret : WordsAt m (sp+1016) 64 (scalarWords d))
    (bound : d < domain.n) :
    ∃ b t, Reaches .l105758 a m .l10581a b t ∧ Prepared b t sp d message ∧
      (∀ i : Fin Reg.count, i.val ∈ [39,50,51] → b[i] = a[i]) ∧
      RamWriteFrame m t (initializationRegions sp) := by
  let digest := compressBlocks initialHash (bytePadding message)
  let dig := storeDigestWords m (sp+352) digest
  let ord := storeOrder (dig 8) sp
  let pushed := memStore (ord 4) (sp-8) (0x10581a : BitVec 64)
  let word (i : Nat) := bswapSpec (BitVec.ofNat 64 (d / 2 ^ (64 * (3 - i))))
  let encoded := writeScalarWords (sp+8) word pushed
  let digestRegion : MemoryRegion := ⟨sp.toNat+352,32⟩
  let orderRegion : MemoryRegion := ⟨sp.toNat+592,32⟩
  let callRegion : MemoryRegion := ⟨sp.toNat-8,8⟩
  let setupRegions := [digestRegion, orderRegion, callRegion]
  let scalarRegion : MemoryRegion := ⟨sp.toNat - 2232, 2272⟩
  have addNat (j : Nat) (hj : j ≤ 1160) := offsetNat limit j hj
  have baseNat : (sp-2232).toNat = sp.toNat-2232 :=
    BitVec.toNat_sub_of_le (show (2232 : BitVec 64) ≤ sp from depth)
  have slotNat : (sp-8).toNat = sp.toNat-8 :=
    BitVec.toNat_sub_of_le (show (8 : BitVec 64) ≤ sp from by change 8 ≤ sp.toNat; omega)
  have openStack (j len : Nat) (inside : j + len ≤ 1160) :
      Writable Extracted.programImage m (sp+BitVec.ofNat 64 j) len := by
    apply stack.sub <;> rw [baseNat, addNat _ (by omega)] <;> omega
  have callSlot : Writable Extracted.programImage m (sp-8) 8 :=
    stack.sub (by rw [baseNat, slotNat]; omega) (by rw [baseNat, slotNat]; omega)
  have digestFrame (n : Nat) (hn : n ≤ 8) : RamWriteFrame m (dig n) setupRegions := by
    apply storeDigestWords_frame
    intro i hi
    refine ⟨digestRegion, List.mem_cons_self, ?_⟩
    change sp.toNat + 352 ≤ _ ∧ _ ≤ sp.toNat + 352 + 32 ∧ _
    simp only [wordOffset, BitVec.reduceToNat, Nat.reduceDiv]
    rw [addNat _ (by omega)]
    omega
  have orderFits (i : Nat) (hi : i < 4) : 592 ≤ orderOffset i ∧ orderOffset i + 8 ≤ 624 := by
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl|rfl|rfl|rfl <;> decide
  have orderFrame {o : Ram} {regions : List MemoryRegion}
      (start : RamWriteFrame o (dig 8) regions) (member : orderRegion ∈ regions)
      (n : Nat) (hn : n ≤ 4) : RamWriteFrame o (ord n) regions := by
    induction n with
    | zero => exact start
    | succ n ih =>
      have off := orderFits n (by omega)
      apply (ih (by omega)).memStore
      refine ⟨orderRegion, member, ?_⟩
      change sp.toNat + 592 ≤ _ ∧ _ ≤ sp.toNat + 592 + 32 ∧ _
      rw [addNat _ (by omega)]
      omega
  have ordFrame (n : Nat) (hn : n ≤ 4) : RamWriteFrame m (ord n) setupRegions :=
    orderFrame (digestFrame 8 (by decide)) (List.mem_cons_of_mem _ List.mem_cons_self) n hn
  have pushFrame : RamWriteFrame m pushed setupRegions := by
    apply (ordFrame 4 (by decide)).memStore
    refine ⟨callRegion, by simp only [setupRegions, List.mem_cons, true_or, or_true], ?_⟩
    change sp.toNat - 8 ≤ _ ∧ _ ≤ sp.toNat - 8 + 8 ∧ _
    rw [slotNat]
    omega
  have encodedFrame (n : Nat) (hn : n ≤ 4) :
      RamWriteFrame pushed (encoded n) [scalarRegion] := by
    apply scalarStoreFrame
    intro i hi
    refine ⟨scalarRegion, List.mem_cons_self, ?_⟩
    change sp.toNat - 2232 ≤ _ ∧ _ ≤ sp.toNat - 2232 + 2272 ∧ _
    simp only [wordOffset, BitVec.reduceToNat, Nat.reduceDiv]
    rw [addNat _ (by omega)]
    omega
  have pushScalarFrame : RamWriteFrame (ord 4) (encoded 4) [scalarRegion] := by
    have push : RamWriteFrame (ord 4) pushed [scalarRegion] := by
      apply (RamWriteFrame.refl _ _).memStore
      refine ⟨scalarRegion, List.mem_cons_self, ?_⟩
      change sp.toNat - 2232 ≤ _ ∧ _ ≤ sp.toNat - 2232 + 2272 ∧ _
      rw [slotNat]
      omega
    exact push.trans (encodedFrame 4 (by decide)) fun r hr =>
      ⟨r,hr,Nat.le_refl _,Nat.le_refl _⟩
  have finalFrame : RamWriteFrame m (encoded 4) (initializationRegions sp) := by
    have first : RamWriteFrame m pushed (initializationRegions sp) := by
      apply (RamWriteFrame.refl _ _).trans pushFrame
      intro r hr
      simp only [setupRegions,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl
      · exact ⟨digestRegion, by simp only [initializationRegions,digestRegion,List.mem_cons,true_or,or_true],
          Nat.le_refl _, Nat.le_refl _⟩
      · exact ⟨orderRegion, by simp only [initializationRegions,orderRegion,List.mem_cons,true_or,or_true],
          Nat.le_refl _, Nat.le_refl _⟩
      · exact ⟨scalarRegion, List.mem_cons_self, by dsimp [scalarRegion,callRegion]; omega,
          by dsimp [scalarRegion,callRegion]; omega⟩
    exact first.trans (encodedFrame 4 (by decide)) fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨_,List.mem_cons_self,Nat.le_refl _,Nat.le_refl _⟩
  have outsideSetup (j len : Nat) (hi : j = 344 ∧ len = 8 ∨ 1016 ≤ j ∧ j + len ≤ 1048) :
      Outside setupRegions (sp+BitVec.ofNat 64 j) len := by
    rw [Outside, addNat _ (by omega)]
    refine ⟨by omega, fun r hr => ?_⟩
    simp only [setupRegions,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl <;> dsimp [digestRegion,orderRegion,callRegion] <;> omega
  have outsideScalar (j len : Nat) (hl : 40 ≤ j) (hi : j + len ≤ 1160) :
      Outside [scalarRegion] (sp+BitVec.ofNat 64 j) len := by
    rw [Outside, addNat _ (by omega)]
    refine ⟨by omega, fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    exact Or.inr (by dsimp [scalarRegion]; omega)
  have keyLoad : LoadOk (ord 4) (sp+344) 8 :=
    let rd := (openStack 344 8 (by decide)).readable.of_frame (ordFrame 4 (by decide))
    ⟨rd.low, rd.present⟩
  have keyPtr : memLoad (ord 4) (sp+344) 64 = sp+1016 :=
    ((ordFrame 4 (by decide)).memLoad_eq (a := sp+344) (k := 64)
      (outsideSetup 344 8 (by decide))).trans key
  have hashLoad (i : Nat) (hi : i < 8) :
      LoadOk m (sp + BitVec.ofNat 64 (72+4*i)) 4 :=
    let rd := (openStack _ 4 (by omega)).readable
    ⟨rd.low, rd.present⟩
  have hashWord (i : Nat) (hi : i < 8) :
      memLoad m (sp + BitVec.ofNat 64 (72+4*i)) 32 = digest[i]!.toBitVec := by
    have h := hash.2 i hi
    simpa only [wordOffset, BitVec.reduceToNat, Nat.reduceDiv, Vector.getElem_ofFn] using h
  have blockCode (x) (hx : x ∈ codeRange 0x105758 bytes_l105758) :
      x ∈ Extracted.programImage := Common.fnCode_subset_programImage x (code_l105758 x hx)
  have digestStore (i off len : Nat) (hi : i < 8) (code : off + len ≤ bytes_l105758.length) :
      StoreOk Extracted.programImage (dig i) (sp + BitVec.ofNat 64 (352+4*i)) 4
        (0x105758 + BitVec.ofNat 64 off) len :=
    ParseSignature.storeOk_of_codeRange
      ((openStack _ 4 (by omega)).of_frame (digestFrame i (by omega))) blockCode code
  have orderStore (i off len : Nat) (hi : i < 4) (code : off + len ≤ bytes_l105758.length) :
      StoreOk Extracted.programImage (ord i) (sp + BitVec.ofNat 64 (orderOffset i)) 8
        (0x105758 + BitVec.ofNat 64 off) len := by
    have fits := orderFits i hi
    exact ParseSignature.storeOk_of_codeRange
      ((openStack _ 8 (by omega)).of_frame (ordFrame i (by omega))) blockCode code
  have pushStore : StoreOk Extracted.programImage (ord 4) (sp-8) 8 0x105815 5 :=
    ParseSignature.storeOk_of_codeRange (off := 189)
      (callSlot.of_frame (ordFrame 4 (by decide))) blockCode (by decide +kernel)
  have rspBits : a[4].get 64 = sp := congrArg (Value.get 64) rsp
  obtain ⟨child, blocks, crsp, crsi, crdi, cr12, ckeep⟩ :=
    prepareBlock rspBits hashLoad hashWord digestStore orderStore keyLoad keyPtr pushStore
  have loadSecret (i : Nat) (hi : i < 4) :
      LoadOk pushed (wordAddr (sp+1016) 64 i) 8 := by
    simp only [wordOffset, BitVec.reduceToNat, Nat.reduceDiv]
    let rd := (openStack (1016+8*i) 8 (by omega)).readable.of_frame pushFrame
    exact ⟨rd.low, rd.present⟩
  have readSecret (i : Nat) (hi : i < 4) :
      bswapSpec (memLoad pushed (wordAddr (sp+1016) 64 (3-i)) 64) = word i := by
    have apart : Outside setupRegions (wordAddr (sp+1016) 64 (3-i)) 8 := by
      simp only [wordOffset, BitVec.reduceToNat, Nat.reduceDiv]
      exact outsideSetup _ 8 (by omega)
    have before := secret (3-i) (by omega)
    rw [Vector.getElem_ofFn] at before
    exact congrArg bswapSpec ((pushFrame.memLoad_eq (a := wordAddr (sp+1016) 64 (3-i))
      (k := 64) apart).trans before)
  have scalarStore (i off len : Nat) (hi : i < 4) (code : off + len ≤ bytes_l109e30.length) :
      StoreOk Extracted.programImage (encoded i) (wordAddr (sp+8) 64 i) 8
        (0x109e30 + BitVec.ofNat 64 off) len := by
    simp only [wordOffset, BitVec.reduceToNat, Nat.reduceDiv]
    exact ParseSignature.storeOk_of_codeRange
      (((openStack _ 8 (by omega)).of_frame pushFrame).of_frame (encodedFrame i (by omega)))
      (fun x hx => Common.fnCode_subset_programImage x (code_l109e30 x hx)) code
  have retLoad : LoadOk (encoded 4) (sp-8) 8 :=
    let rd := (callSlot.readable.of_frame pushFrame).of_frame (encodedFrame 4 (by decide))
    ⟨rd.low, rd.present⟩
  have retTag : memLoad (encoded 4) (sp-8) 64 = 0x10581a := by
    have onlyDst : RamWriteFrame pushed (encoded 4) [⟨(sp+8).toNat,32⟩] := by
      apply scalarStoreFrame
      intro i hi
      refine ⟨_,List.mem_cons_self,?_⟩
      change (sp+8).toNat ≤ _ ∧ _ ≤ (sp+8).toNat + 32 ∧ _
      simp only [wordOffset, BitVec.reduceToNat, Nat.reduceDiv]
      rw [addNat _ (by omega), show (sp+8).toNat = sp.toNat+8 from addNat 8 (by decide)]
      omega
    rw [onlyDst.memLoad_eq (a := sp-8) (k := 64)]
    · exact memLoad_memStore_same _ _ _ (by decide) (by decide)
    · refine ⟨by rw [slotNat]; omega, fun r hr => ?_⟩
      obtain rfl := List.mem_singleton.mp hr
      left
      change (sp-8).toNat + 8 ≤ (sp+8).toNat
      rw [slotNat, show (sp+8).toNat = sp.toNat+8 from addNat 8 (by decide)]
      omega
  obtain ⟨out, run, tag, mem, outRsp, outKept⟩ := serializeScalarBlock
    crsp crsi crdi loadSecret readSecret
    (by
      have h := scalarStore 0 30 3 (by decide) (by decide)
      rwa [show wordAddr (sp+8) 64 0 = sp+8 from BitVec.add_zero _] at h)
    (scalarStore 1 33 4 (by decide) (by decide))
    (scalarStore 2 37 4 (by decide) (by decide))
    (scalarStore 3 41 4 (by decide) (by decide))
    retLoad retTag (by decide)
  have childExec : program.Exec (dialect Extracted.programImage) ⟨⟨.l109e30,child,pushed⟩,[]⟩ out :=
    .done (by simp only [Program.step,run,Transfer.next])
  have exec := Verify.reachesOfCall blocks childExec tag
  have reaches : Reaches .l105758 a m .l10581a out.values (encoded 4) :=
    Eq.mp (congrArg (fun t => Reaches .l105758 a m .l10581a out.values t) mem) exec
  have same (i : Fin Reg.count) (hi : i.val ∈ [3,5,13,14,15,22,39,50,51]) :
      out.values[i] = a[i] := by
    refine (outKept i ?_).trans (ckeep i hi)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
    omega
  refine ⟨_,_,reaches,⟨?_,?_,?_,?_,?_,?_,?_,?_⟩,?_,finalFrame⟩
  · simpa only [BitVec.sub_add_cancel] using outRsp
  · exact (same 22 (by decide)).trans df
  · exact (outKept 12 (by decide)).trans cr12
  · exact (same 13 (by decide)).trans r13
  · intro i hi
    rw [same i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega)]
    exact widths i hi
  · rw [← serializeHash_compressBlocks_bytePadding]
    have bytes := storeDigestWords_hasBytes m (sp+352) (hash := digest) hash.1
    refine ⟨bytes.1, fun i => ?_⟩
    have hi : i.val < 32 := by
      have h : i.val < (serializeHash digest).size := i.isLt
      have sz : (serializeHash digest).size = 32 := bytes.1
      omega
    have addr : BitVec.ofNat 64 ((sp+352).toNat + i.val) = sp+BitVec.ofNat 64 (352+i.val) := by
      rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.ofNat_add,
        BitVec.add_assoc] <;> rfl
    change (encoded 4)[BitVec.ofNat 64 ((sp+352).toNat+i.val)]? = _
    rw [addr, pushScalarFrame.outside _ (outsideScalar _ 1 (by omega) (by omega))]
    have onlyOrder := orderFrame (RamWriteFrame.refl (dig 8) [orderRegion])
      List.mem_cons_self 4 (by decide)
    rw [onlyOrder.outside (sp+BitVec.ofNat 64 (352+i.val))]
    · rw [← addr]
      exact bytes.2 i
    · rw [Outside, addNat _ (by omega)]
      refine ⟨by omega, fun r hr => ?_⟩
      obtain rfl := List.mem_singleton.mp hr
      left
      dsimp [orderRegion]
      omega
  · intro i hi
    have original := storeOrder_reads (m := dig 8) limit i hi
    simp only [wordOffset, BitVec.reduceToNat, Nat.reduceDiv] at original ⊢
    rw [pushScalarFrame.memLoad_eq (a := sp+BitVec.ofNat 64 (592+8*i)) (k := 64)
      (outsideScalar _ 8 (by omega) (by omega))]
    exact original
  · apply scalarOctets
    · intro i hi
      rw [Vector.getElem_ofFn]
      exact scalarStoreReads ((openStack 8 32 (by decide)).readable.low) i hi
    · exact ((openStack 8 32 (by decide)).readable.of_frame pushFrame).of_frame
        (encodedFrame 4 (by decide))
  · intro i hi
    exact same i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega)

end K256.Proofs.Signing.Nonce.Start
