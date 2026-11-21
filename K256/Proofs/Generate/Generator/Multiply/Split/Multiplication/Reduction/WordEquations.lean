import K256.Proofs.Generate.Generator.Multiply.Split.Multiplication.ProductFlags
import K256.Proofs.Generate.Generator.Multiply.Split.Multiplication.Reduction.Layout

namespace K256.Proofs.Generate.Generator.Multiply.Split.Reduction.Replay

open X86Proofs Common.Invert.LinearCombination

private theorem mergeCarry (c : Bool) :
    mergeGPR 8 (if c then 1 else 0) 0 = carryWord c :=
  ProductSchedule.bit_of_merge c

private theorem v98_eq (w : Vector (BitVec 64) 8) : v98 w = carryWord (v96 w) :=
  mergeCarry (v96 w)

private theorem v112_eq (w : Vector (BitVec 64) 8) : v112 w = carryWord (v110 w) :=
  mergeCarry (v110 w)

private theorem v142_eq (w : Vector (BitVec 64) 8) : v142 w = carryWord (v138 w) :=
  mergeCarry (v138 w)

private theorem v154_eq (w : Vector (BitVec 64) 8) : v154 w = carryWord (v152 w) :=
  mergeCarry (v152 w)

private theorem v182_eq (w : Vector (BitVec 64) 8) : v182 w = carryWord (v180 w) :=
  mergeCarry (v180 w)

private theorem v201_eq (w : Vector (BitVec 64) 8) : v201 w = carryWord (v199 w) :=
  mergeCarry (v199 w)

private theorem firstLowCarry (w : Vector (BitVec 64) 8) :
    (lowColumns w[0] w[1] w[4] w[5]).carry = v103 w := by
  simp only [lowColumns, v103, v101, v98_eq, v96, v95, v91, v89, v88, v85, v82,
    v81, v79, v77, v75, v71, v69, v68, v66, v64, v62, v60, v59, v57, v55, v53,
    mulResult_fst]

private theorem firstMiddle (w : Vector (BitVec 64) 8) :
    middleColumn w[2] (v103 w) w[6] w[5] w[4] = ⟨v144 w, v147 w⟩ := by
  simp only [middleColumn, v147, v145, v144, v142_eq, v138, v137, v133, v131, v130,
    v128, v126, v125, v123, v121, v119, v117, v116, v114, v112_eq, v110, v109,
    v105, v77, v73, v55, v53, mulResult_fst]

private theorem firstMiddleNext (w : Vector (BitVec 64) 8) :
    middleColumn w[3] (v147 w) w[7] w[6] w[5] = ⟨v184 w, v187 w⟩ := by
  simp only [middleColumn, v187, v185, v184, v182_eq, v180, v179, v175, v173, v172,
    v170, v168, v167, v165, v163, v161, v159, v158, v156, v154_eq, v152, v151,
    v140, v105, v77, v73, v55, mulResult_fst]

private theorem firstUpper (w : Vector (BitVec 64) 8) :
    upperColumns (v187 w) w[6] w[7] = ⟨v203 w, v222 w, carryWord (v223 w)⟩ := by
  simp only [upperColumns, v223, v222, v220, v206, v204, v203, v201_eq, v199, v198,
    v194, v192, v191, v189, v140, v105, v77, mulResult_fst]

private theorem first0_eq (w : Vector (BitVec 64) 8) : (firstFold w)[0] = v84 w := by
  change (lowColumns w[0] w[1] w[4] w[5]).low = _
  simp only [lowColumns, mulResult_fst, v84, v64, v59, v57, v53]

private theorem first1_eq (w : Vector (BitVec 64) 8) : (firstFold w)[1] = v100 w := by
  change (lowColumns w[0] w[1] w[4] w[5]).next = _
  simp only [lowColumns, mulResult_fst, v100, v95, v88, v85, v81, v79, v77, v71, v68,
    v66, v64, v62, v60, v59, v57, v55, v53]

private theorem first2_eq (w : Vector (BitVec 64) 8) : (firstFold w)[2] = v144 w := by
  change (middleColumn _ _ _ _ _).low = _
  rw [firstLowCarry, firstMiddle]

private theorem first3_eq (w : Vector (BitVec 64) 8) : (firstFold w)[3] = v184 w := by
  change (middleColumn _ (middleColumn _ _ _ _ _).carry _ _ _).low = _
  rw [firstLowCarry, firstMiddle, firstMiddleNext]

private theorem first4_eq (w : Vector (BitVec 64) 8) : (firstFold w)[4] = v203 w := by
  change (upperColumns (middleColumn _ (middleColumn _ _ _ _ _).carry _ _ _).carry _ _).low = _
  rw [firstLowCarry, firstMiddle, firstMiddleNext, firstUpper]

private theorem first5_eq (w : Vector (BitVec 64) 8) : (firstFold w)[5] = v222 w := by
  change (upperColumns (middleColumn _ (middleColumn _ _ _ _ _).carry _ _ _).carry _ _).next = _
  rw [firstLowCarry, firstMiddle, firstMiddleNext, firstUpper]

private theorem first6_eq (w : Vector (BitVec 64) 8) : (firstFold w)[6] = carryWord (v223 w) := by
  change (upperColumns (middleColumn _ (middleColumn _ _ _ _ _).carry _ _ _).carry _ _).carry = _
  rw [firstLowCarry, firstMiddle, firstMiddleNext, firstUpper]

private theorem mulCarryLo (c : Bool) (k : BitVec 64) :
    carryWord c * k = if c then k else 0 := by
  cases c
  · exact BitVec.zero_mul
  · exact BitVec.one_mul k

private theorem mulCarryHi (c : Bool) (k : BitVec 64) :
    (mulResult (carryWord c) k).2 = 0 := by
  have h := Common.Field.mulResult_toNat_add (carryWord c) k
  rw [mulResult_fst, mulCarryLo, carryWord_value] at h
  apply BitVec.eq_of_toNat_eq
  cases c
  · simp only [Bool.false_eq_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat,
      Nat.reducePow, Nat.zero_mod, carryWord, Bool.toNat_false, Nat.zero_add, Nat.zero_mul] at h ⊢
    omega
  · simp only [↓reduceIte, Nat.reducePow, carryWord, Bool.toNat_true, Nat.one_mul, Nat.add_eq_left,
      BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.zero_mod] at h ⊢
    omega

private theorem carryNeZero (c : Bool) : (carryWord c != 0) = c := by
  cases c <;> rfl

private theorem v259_eq (w : Vector (BitVec 64) 8) : v259 w = carryWord (v257 w) :=
  mergeCarry (v257 w)

private theorem v271_eq (w : Vector (BitVec 64) 8) : v271 w = carryWord (v269 w) :=
  mergeCarry (v269 w)

private theorem v290_eq (w : Vector (BitVec 64) 8) : v290 w = carryWord (v288 w) :=
  mergeCarry (v288 w)

private theorem v302_eq (w : Vector (BitVec 64) 8) : v302 w = carryWord (v300 w) :=
  mergeCarry (v300 w)

private theorem v318_eq (w : Vector (BitVec 64) 8) : v318 w = carryWord (v316 w) :=
  mergeCarry (v316 w)

private theorem secondLow (w : Vector (BitVec 64) 8) :
    lowColumns (v84 w) (v100 w) (v203 w) (v222 w) = ⟨v245 w, v261 w, v264 w⟩ := by
  simp only [lowColumns, v264, v262, v261, v259_eq, v257, v256, v252, v250, v249,
    v246, v245, v243, v242, v240, v238, v236, v234, v232, v231, v229, v218, v216,
    v214, v213, v208, v210, v73, mulResult_fst]

private theorem v280_eq (w : Vector (BitVec 64) 8) :
    v280 w = (addSpec (v227 w) (v268 w)).1 :=
  BitVec.add_comm _ _

private theorem v281_eq (w : Vector (BitVec 64) 8) :
    v281 w = (addSpec (v227 w) (v268 w)).2.CF :=
  ProductSchedule.addCF_comm _ _

private theorem secondMiddle (w : Vector (BitVec 64) 8) :
    middleColumn (v144 w) (v264 w) (carryWord (v223 w)) (v222 w) (v203 w) =
      ⟨v292 w, v295 w⟩ := by
  simp only [middleColumn, mulCarryLo, mulCarryHi, v295, v293, v292, v290_eq, v288, v287,
    v283, v281_eq, v280_eq, v278, v277, v275, v273, v271_eq, v269, v268, v227,
    v225, v210, v73, mulResult_fst]
  rw [show ∀ x : BitVec 64, (addSpec x 0).1 = x from BitVec.add_zero]

private theorem secondUpper (w : Vector (BitVec 64) 8) :
    upperSmall (v184 w) (v295 w) (v222 w) (carryWord (v223 w)) = ⟨v320 w, v323 w⟩ := by
  simp only [upperSmall, carryNeZero, v323, v321, v320, v318_eq, v316, v315, v311,
    v309, v307, v302_eq, v300, v299, v275,
    show v304 w = v222 w from rfl, show v305 w = v223 w from rfl]

private theorem second0_eq (w : Vector (BitVec 64) 8) :
    (secondFold (firstFold w))[0] = v245 w := by
  change (lowColumns (firstFold w)[0] (firstFold w)[1]
    (firstFold w)[4] (firstFold w)[5]).low = _
  rw [first0_eq, first1_eq, first4_eq, first5_eq, secondLow]

private theorem second1_eq (w : Vector (BitVec 64) 8) :
    (secondFold (firstFold w))[1] = v261 w := by
  change (lowColumns (firstFold w)[0] (firstFold w)[1]
    (firstFold w)[4] (firstFold w)[5]).next = _
  rw [first0_eq, first1_eq, first4_eq, first5_eq, secondLow]

private theorem second2_eq (w : Vector (BitVec 64) 8) :
    (secondFold (firstFold w))[2] = v292 w := by
  change (middleColumn _ (lowColumns _ _ _ _).carry _ _ _).low = _
  rw [first0_eq, first1_eq, first2_eq, first4_eq, first5_eq, first6_eq, secondLow, secondMiddle]

private theorem second3_eq (w : Vector (BitVec 64) 8) :
    (secondFold (firstFold w))[3] = v320 w := by
  change (upperSmall _ (middleColumn _ (lowColumns _ _ _ _).carry _ _ _).carry _ _).low = _
  rw [first0_eq, first1_eq, first2_eq, first3_eq, first4_eq, first5_eq, first6_eq,
    secondLow, secondMiddle, secondUpper]

private theorem second4_eq (w : Vector (BitVec 64) 8) :
    (secondFold (firstFold w))[4] = v323 w := by
  change (upperSmall _ (middleColumn _ (lowColumns _ _ _ _).carry _ _ _).carry _ _).carry = _
  rw [first0_eq, first1_eq, first2_eq, first3_eq, first4_eq, first5_eq, first6_eq,
    secondLow, secondMiddle, secondUpper]

private theorem v351_eq (w : Vector (BitVec 64) 8) : v351 w = carryWord (v349 w) :=
  mergeCarry (v349 w)

private theorem lastFold_eq (w : Vector (BitVec 64) 8) :
    lastFold (secondFold (firstFold w)) = (⟨v353 w, v356 w, v359 w, v362 w⟩, v363 w) := by
  simp only [lastFold, second0_eq, second1_eq, second2_eq, second3_eq, second4_eq,
    v363, v362, v360, v359, v357, v356, v354, v353, v351_eq, v349, v348, v344, v342,
    v341, v339, v338, v336, v334, v332, v330, v329, v327, v325, v275, v73, mulResult_fst]

theorem word353_eq (w : Vector (BitVec 64) 8) : v353 w = (lastFold (secondFold (firstFold w))).1.l0 := by
  rw [lastFold_eq]

theorem word356_eq (w : Vector (BitVec 64) 8) : v356 w = (lastFold (secondFold (firstFold w))).1.l1 := by
  rw [lastFold_eq]

theorem word359_eq (w : Vector (BitVec 64) 8) : v359 w = (lastFold (secondFold (firstFold w))).1.l2 := by
  rw [lastFold_eq]

theorem word362_eq (w : Vector (BitVec 64) 8) : v362 w = (lastFold (secondFold (firstFold w))).1.l3 := by
  rw [lastFold_eq]

theorem word478_eq (w : Vector (BitVec 64) 8) :
    v478 w = carryWord (lastFold (secondFold (firstFold w))).2 := by
  rw [lastFold_eq]
  unfold v478 v365
  rw [setWidth_mergeGPR8]
  exact ProductSchedule.bit_of_byte (v363 w)

private theorem lowBorrow (a : BitVec 64) :
    borrow a orderLimbs.l0 (a - orderLimbs.l0) = (~~~a ||| (a + complementLo)) >>> 63 := by
  have low : a - orderLimbs.l0 = a + complementLo := by rw [BitVec.sub_eq_add_neg]; rfl
  apply BitVec.eq_of_toNat_eq
  simp only [borrow, low, shift63_toNat, BitVec.msb_or, BitVec.msb_and, BitVec.msb_not,
    show orderLimbs.l0.msb = true from rfl]
  cases a.msb <;> cases (a + complementLo).msb <;> rfl

private theorem lowSub (a : BitVec 64) : a - orderLimbs.l0 = complementLo + a := by
  rw [BitVec.sub_eq_add_neg, BitVec.add_comm]
  rfl

private theorem lowBorrowReordered (a : BitVec 64) :
    borrow a orderLimbs.l0 (complementLo + a) = (~~~a ||| (complementLo + a)) >>> 63 := by
  calc
    _ = borrow a orderLimbs.l0 (a - orderLimbs.l0) := congrArg _ (lowSub a).symm
    _ = (~~~a ||| (a + complementLo)) >>> 63 := lowBorrow a
    _ = _ := congrArg (fun z => (~~~a ||| z) >>> 63) (BitVec.add_comm _ _)

private theorem subWordZero (a b carry : BitVec 64) :
    subWord a b carry = (0 - carry).sshiftRight 63 + (a - b) :=
  congrArg (fun (word : BitVec 64) => word.sshiftRight 63 + (a - b)) (BitVec.zero_sub carry).symm

private theorem subRawOrder_eq (a : Limbs) :
    subRaw a orderLimbs =
      let r0 := complementLo + a.l0
      let c0 := ((~~~a.l0) ||| r0) >>> 63
      let r1 := (0 - c0).sshiftRight 63 + (a.l1 - orderLimbs.l1)
      let c1 := borrow a.l1 orderLimbs.l1 r1
      let r2 := (0 - c1).sshiftRight 63 + (a.l2 - orderLimbs.l2)
      let c2 := borrow a.l2 orderLimbs.l2 r2
      let r3 := (0 - c2).sshiftRight 63 + (a.l3 - orderLimbs.l3)
      (⟨r0, r1, r2, r3⟩, borrow a.l3 orderLimbs.l3 r3) := by
  simp only [subRaw, subWordZero, lowSub, lowBorrowReordered]

private theorem replaySub_eq (w : Vector (BitVec 64) 8) :
    subRaw ⟨v353 w, v356 w, v359 w, v362 w⟩ orderLimbs =
      (⟨v368 w, v393 w, v424 w, v455 w⟩, v471 w) :=
  subRawOrder_eq _

theorem word368_eq (w : Vector (BitVec 64) 8) :
    v368 w = (subRaw (lastFold (secondFold (firstFold w))).1 orderLimbs).1.l0 := by
  rw [lastFold_eq, replaySub_eq]

theorem word393_eq (w : Vector (BitVec 64) 8) :
    v393 w = (subRaw (lastFold (secondFold (firstFold w))).1 orderLimbs).1.l1 := by
  rw [lastFold_eq, replaySub_eq]

theorem word424_eq (w : Vector (BitVec 64) 8) :
    v424 w = (subRaw (lastFold (secondFold (firstFold w))).1 orderLimbs).1.l2 := by
  rw [lastFold_eq, replaySub_eq]

theorem word455_eq (w : Vector (BitVec 64) 8) :
    v455 w = (subRaw (lastFold (secondFold (firstFold w))).1 orderLimbs).1.l3 := by
  rw [lastFold_eq, replaySub_eq]

private theorem borrowWord (r : Limbs) :
    carryWord ((subRaw r orderLimbs).2 != 0) = (subRaw r orderLimbs).2 := by
  obtain h | h := eq_zero_or_one (subRaw_toNat r orderLimbs).1 <;> rw [h] <;> rfl

theorem word476_eq (w : Vector (BitVec 64) 8) :
    v476 w = -carryWord ((subRaw (lastFold (secondFold (firstFold w))).1 orderLimbs).2 != 0) := by
  rw [borrowWord, lastFold_eq, replaySub_eq]
  exact BitVec.zero_sub _

end K256.Proofs.Generate.Generator.Multiply.Split.Reduction.Replay
