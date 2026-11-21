import K256.Proofs.Generate.Generator.Multiply.Radix.State

namespace K256.Proofs.Generate.Generator.Multiply.Radix

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine
open K256.Proofs.Generate.LIR K256.Proofs.Common.Tactic Prelude

private theorem byteSwapByte (w : BitVec 64) (s : Nat)
    (aligned : s % 8 = 0) (within : s ≤ 56) :
    ((bswapSpec w) >>> s).setWidth 8 = (w >>> (56 - s)).setWidth 8 := by
  have atLane : s / 8 * 8 = s := by omega
  have atReverse : (7 - s / 8) * 8 = 56 - s := by omega
  change (bswapSpec w).extractLsb' s 8 = w.extractLsb' (56 - s) 8
  rw [← atLane, show 56 - s / 8 * 8 = (7 - s / 8) * 8 by omega]
  change lane 8 (bswapSpec w) (s / 8) = lane 8 w (7 - s / 8)
  rw [bswapSpec, lane_ofLanes (n := 64) _ _ (by omega)]

private theorem lowByteNibble (w : BitVec 8) :
    w &&& 15 = BitVec.ofNat 8 (w.toNat % 16) := by
  decide +kernel +revert

private theorem highByteNibble (w : BitVec 8) :
    w >>> 4 = BitVec.ofNat 8 (w.toNat / 16) := by
  decide +kernel +revert

private theorem powerNibble (i : Nat) : 16 ^ i = 2 ^ (4 * i) := by
  rw [Nat.pow_mul]

private theorem lowShiftNibble (x s : Nat) (aligned : s % 8 = 0) (within : s ≤ 56) :
    (((bswapSpec (BitVec.ofNat 64 x)) >>> s).setWidth 8) &&& 15 =
      BitVec.ofNat 8 (nibble x ((56 - s) / 4)) := by
  rw [byteSwapByte _ _ aligned within, lowByteNibble, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, nibble, powerNibble,
    show 4 * ((56 - s) / 4) = 56 - s by omega,
    Nat.mod_mod_of_dvd _ (by decide : 16 ∣ 2^8),
    show 2 ^ (64 : Nat) = 2 ^ (56 - s) * 2 ^ (s + 8) by
      rw [← Nat.pow_add, show 56 - s + (s + 8) = 64 by omega],
    Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega : 4 ≤ s + 8))]
  rfl

private theorem highShiftNibble (x s : Nat) (aligned : s % 8 = 0) (within : s ≤ 56) :
    (((bswapSpec (BitVec.ofNat 64 x)) >>> s).setWidth 8) >>> 4 =
      BitVec.ofNat 8 (nibble x ((56 - s) / 4 + 1)) := by
  rw [byteSwapByte _ _ aligned within, highByteNibble, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, nibble, powerNibble,
    show 4 * ((56 - s) / 4 + 1) = 56 - s + 4 by omega,
    show 2^8 = 16*16 by decide, Nat.mod_mul_right_div_self, Nat.div_div_eq_div_mul,
    show 2 ^ (56 - s) * 16 = 2 ^ (56 - s + 4) by rw [Nat.pow_add],
    show 2 ^ (64 : Nat) = 2 ^ (56 - s + 4) * 2 ^ (s + 4) by
      rw [← Nat.pow_add, show 56 - s + 4 + (s + 4) = 64 by omega],
    Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega : 4 ≤ s + 4))]
  rfl

private theorem highTopByte {n : Nat} (w : BitVec n) (s : Nat) (width : s + 8 = n) :
    (w >>> (s + 4)).setWidth 8 = ((w >>> s).setWidth 8) >>> 4 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hj, decide_true, Bool.true_and,
    Nat.add_assoc]
  by_cases h : 4 + j < 8
  · simp only [h, decide_true, Bool.true_and]
  · simp only [h, decide_false, Bool.false_and, BitVec.getLsbD_of_ge w (s + (4 + j)) (by omega)]

private theorem topShift (w : BitVec 64) :
    (w >>> 60).setWidth 8 = ((w >>> 56).setWidth 8) >>> 4 :=
  highTopByte w 56 (by decide)

private theorem lowByteShift32 (w : BitVec 64) (s : Nat) (within : s + 8 ≤ 32) :
    ((w.setWidth 32) >>> s).setWidth 8 = (w >>> s).setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hj, decide_true, Bool.true_and]
  simp only [show s + j < 32 by omega, decide_true, Bool.true_and]

private theorem topShift32 (w : BitVec 64) :
    (w.setWidth 32 >>> 28).setWidth 8 = ((w >>> 24).setWidth 8) >>> 4 := by
  have h : (w.setWidth 32 >>> 28).setWidth 8 = ((w.setWidth 32 >>> 24).setWidth 8) >>> 4 :=
    highTopByte (w.setWidth 32) 24 (by decide)
  rw [h, lowByteShift32 w 24 (by decide)]

private theorem upperWordNibble (x i : Nat) : nibble (x / 2^64) i = nibble x (16 + i) := by
  simp only [nibble, powerNibble, Nat.div_div_eq_div_mul, ← Nat.pow_add]
  rw [show 64 + 4 * i = 4 * (16 + i) by omega]


private theorem lowFinalNibble (x : Nat) :
    (bswapSpec (BitVec.ofNat 64 x)).setWidth 8 &&& 15 = BitVec.ofNat 8 (nibble x 14) := by
  simpa only [BitVec.ushiftRight_zero] using lowShiftNibble x 0 (by decide) (by decide)

private theorem highFinalNibble (x : Nat) :
    (bswapSpec (BitVec.ofNat 64 x)).setWidth 8 >>> 4 = BitVec.ofNat 8 (nibble x 15) := by
  simpa only [BitVec.ushiftRight_zero] using highShiftNibble x 0 (by decide) (by decide)

private def writeNibbles (m : Ram) (base : BitVec 64) (x : Nat) : Nat → Ram
  | 0 => memStore m (base + 32) (0 : BitVec 8)
  | i + 1 => memStore (writeNibbles m base x i) (base + BitVec.ofNat 64 i)
      (BitVec.ofNat 8 (nibble x i))

private theorem stackByte_zero (x i : Nat) : stackByte x 0 i = BitVec.ofNat 8 (nibble x i) := by
  simp only [stackByte, Nat.not_lt_zero, ite_false]
  split
  · rename_i h
    subst i
    rfl
  · rfl

private theorem writeNibbles_words (m : Ram) (base : BitVec 64) (x : Nat) (bound : x < 2^128) :
    WordsAt (writeNibbles m base x 32) base 8 (Vector.ofFn fun i : Fin 33 => stackByte x 0 i.val) := by
  have loaded (k : Nat) (hk : k ≤ 32) (i : Nat) (hi : i ≤ 32) (h : i < k ∨ i = 32) :
      memLoad (writeNibbles m base x k) (base + BitVec.ofNat 64 i) 8 = BitVec.ofNat 8 (nibble x i) := by
    induction k with
    | zero =>
      obtain rfl : i = 32 := by omega
      have hz : nibble x 32 = 0 := by
        rw [nibble, Nat.div_eq_of_lt bound]
      rw [hz]
      exact memLoad_memStore_same m (base + 32) (0 : BitVec 8) (by decide) (by decide)
    | succ k ih =>
      by_cases he : i = k
      · subst i
        exact memLoad_memStore_same _ _ _ (by decide) (by decide)
      · have apart : RangeApart (base + BitVec.ofNat 64 k) 1 (base + BitVec.ofNat 64 i) 1 := by
          intro j hj l hl eq
          obtain rfl : j = 0 := by omega
          obtain rfl : l = 0 := by omega
          have kb : k < 2^64 := by omega
          have ib : i < 2^64 := by omega
          have bitEq : BitVec.ofNat 64 k = BitVec.ofNat 64 i := by bv_omega
          have hki := congrArg BitVec.toNat bitEq
          simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt kb, Nat.mod_eq_of_lt ib] at hki
          exact he hki.symm
        rw [writeNibbles, memLoad_memStore_of_rangeApart _ _ _ _ 8 apart]
        exact ih (by omega) (by omega)
  intro i hi
  rw [Vector.getElem_ofFn, stackByte_zero]
  simpa only [wordAddr, Nat.reduceDiv, Nat.one_mul] using loaded 32 (by decide) i (by omega) (by omega)

set_option maxHeartbeats 1500000 in
theorem extractNibbles {code : CodeMap} (included : ∀ a ∈ fnCode, a ∈ code)
    (fr : Activation) (args : Values Value Reg.count) (mem : Ram) (x : Nat)
    (bound : x < 2^128)
    (atoms : Atom.All code args mem (Fn11aa40.frameAt .l11aa40 fr))
    (src : Readable mem fr.rsi 16)
    (lo : memLoad mem fr.rsi 64 = BitVec.ofNat 64 x)
    (hi : memLoad mem (fr.rsi + 8) 64 = BitVec.ofNat 64 (x / 2^64))
    (srcAbove : fr.rsp.toNat + 8 ≤ fr.rsi.toNat) :
    ∃ b n, Path code .l11aa40 args mem .l11ac00 b n ∧ LoopState code fr mem n b x 0 := by
  simp only [Fn11aa40.frameAt, Fn11aa40.frameAtG1, Atom.All, Atom.Holds] at atoms
  obtain ⟨sp, df, cx, dx, bx, bp, si, di, r8, r9, r12, r13, r14, r15, mx, ftw, fcw,
    retRead, ret, retLow, stack, low, align, _⟩ := atoms
  have getSp : args[4].get 64 = fr.rsp := congrArg (Value.get 64) sp
  have getSi : args[6].get 64 = fr.rsi := congrArg (Value.get 64) si
  have getDi : args[7].get 64 = fr.rdi := congrArg (Value.get 64) di
  have incl := fun a h => included a (code_l11aa40 a h)
  have stackNat : (fr.rsp - 33).toNat = fr.rsp.toNat - 33 :=
    BitVec.toNat_sub_of_le (by change 33 ≤ fr.rsp.toNat; omega)
  have highNat : (fr.rsi + 8).toNat = fr.rsi.toNat + 8 := by
    rw [BitVec.toNat_add]
    change (fr.rsi.toNat + 8) % 2^64 = _
    exact Nat.mod_eq_of_lt (by have := src.1; omega)
  refine ⟨?outRegs, ?outMem, ?path, ?state⟩
  case path =>
    have run : program.runBlock (dialect code) ⟨.l11aa40, args, mem⟩ =
        .jump ⟨.l11ac00, ?outRegs, ?outMem⟩ := by
      arithmetic_segment using incl [getSp, getSi, getDi, lo, hi,
        Lift.reduceAddOffset, Lift.reduceSubOffset, Lift.reduceAddNeg, Lift.reduceSubNeg,
        BitVec.reduceAdd, BitVec.reduceSub]
    refine .step (b := ⟨⟨.l11ac00, _, _⟩, []⟩) ?_ (Star.refl _)
    simp only [Program.sem, Program.step, run, Transfer.next]
  case state =>
    refine ⟨?entryAtoms, ?widths, rfl, ?current, ?digits, ?frame⟩
    case frame => slot_state region
    case entryAtoms =>
      simp only [Fn11aa40.frameAt, Fn11aa40.frameAtG1, Atom.All, Atom.Holds]
      refine ⟨rfl, df, rfl, bx, bp, r9, r12, r13, r14, r15, mx, ftw, fcw,
        ?readRet, ?wordRet, retLow, ?win, low, align, trivial⟩
      case' readRet | win => slot_state region
      case wordRet => segment_words [ret]
    case widths =>
      intro ⟨i, ib⟩ h
      simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | rfl | exact congrArg Value.width r9
    case current =>
      simp only [pending, Generate.Curve.radixCarry, Nat.add_zero]
      let w := bswapSpec (BitVec.ofNat 64 x) >>> 56
      change (mergeGPR 8 (w.setWidth 8 &&& 15) w).setWidth 8 = _
      rw [setWidth_mergeGPR8]
      exact lowShiftNibble x 56 (by decide) (by decide)
    case digits =>
      refine Eq.mpr (congrArg (fun n =>
        WordsAt n (fr.rsp - 33) 8 (Vector.ofFn fun i : Fin 33 => stackByte x 0 i.val)) ?_)
        (writeNibbles_words mem (fr.rsp - 33) x bound)
      simp (disch := decide) only [writeNibbles, setWidth_mergeGPR8,
        BitVec.setWidth_setWidth_of_le (k := 8) (l := 32) _ (by decide),
        topShift, topShift32, lowByteShift32, lowShiftNibble, highShiftNibble, lowFinalNibble,
        highFinalNibble, Nat.reduceSub, Nat.reduceDiv, Nat.reduceAdd, upperWordNibble,
        Lift.reduceAddOffset]

end K256.Proofs.Generate.Generator.Multiply.Radix
