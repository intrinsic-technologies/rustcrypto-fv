import K256.Proofs.Verify.Core.Lincomb.Recode.Even

namespace K256.Proofs.Verify.Core.Lincomb.Recode

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

theorem cmpNatCF {x y : Nat} (hx : x < 2^64) (hy : y < 2^64) :
    (cmpSpec (BitVec.ofNat 64 x) (BitVec.ofNat 64 y)).CF = decide (x < y) := by
  simp only [cmpSpec_CF, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

theorem cmpNatZF {x y : Nat} (hx : x < 2^64) (hy : y < 2^64) :
    (cmpSpec (BitVec.ofNat 64 x) (BitVec.ofNat 64 y)).ZF = decide (x = y) := by
  rw [cmpSpec_ZF, Bool.eq_iff_iff]
  simp only [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

structure OddRegisters (a b : Registers) (sp dst : BitVec 64) (i w : Nat) : Prop where
  stack : b[4] = ⟨64, sp-136⟩
  width : b[12] = ⟨64, 5⟩
  bitIndex : b[15] = ⟨64, BitVec.ofNat 64 i⟩
  length : b[14] = ⟨64, BitVec.ofNat 64 i⟩
  skip : b[5] = ⟨64, BitVec.ofNat 64 (Naf.skip (128-i) w)⟩
  carry : b[13] = ⟨64, BitVec.ofNat 64 (Naf.carry w)⟩
  room : b[0] = ⟨64, BitVec.ofNat 64 (257-i)⟩
  dest : b[6] = ⟨64,dst⟩
  saved : ControlSaved a b

abbrev oddTail (i w : Nat) : Label :=
  if Naf.skip (128-i) w < 2 then .l110830 else .l110912

set_option maxHeartbeats 800000 in
theorem writeOddDigit {a b : Registers} {m : Ram} {sp dst : BitVec 64} {i c w : Nat}
    (regs : LoopRegisters a b sp i c) (fields : LoopMemory m sp dst)
    (bound : i < 128) (wins : w ≤ 32) (progress : 1 ≤ Naf.skip (128-i) w)
    (dest : b[6] = ⟨64,dst⟩) (window : b[2].get 64 = BitVec.ofNat 64 w)
    (capacity : LoadOk m (sp-136) 8) (half : LoadOk m (sp-104) 8) (radix : LoadOk m (sp-124) 4)
    (write : Writable Extracted.programImage m dst 257)
    (bits : LoadOk (memStore m (digitAddr dst i) (BitVec.ofInt 8 (Naf.digit w))) (sp-112) 8)
    (bitsWord : memLoad (memStore m (digitAddr dst i) (BitVec.ofInt 8 (Naf.digit w))) (sp-112) 64 = 128) :
    ∃ r, Continues .l1108d0 b m (oddTail i w) r
      (memStore m (digitAddr dst i) (BitVec.ofInt 8 (Naf.digit w))) ∧
      OddRegisters a r sp dst i w := by
  let m' := memStore m (digitAddr dst i) (BitVec.ofInt 8 (Naf.digit w))
  have rsp : b[4].get 64 = sp-136 := congrArg (Value.get 64) regs.stack
  have length : b[14].get 64 = BitVec.ofNat 64 i := congrArg (Value.get 64) regs.length
  have neg : b[5].get 64 = -(BitVec.ofNat 64 i) := congrArg (Value.get 64) regs.negIndex
  have width : b[12].get 64 = 5 := congrArg (Value.get 64) regs.width
  have dstGet : b[6].get 64 = dst := congrArg (Value.get 64) dest
  have cf : (cmpSpec (257 : BitVec 64) (BitVec.ofNat 64 i)).CF = false :=
    (cmpNatCF (by decide : 257 < 2^64) (by omega : i < 2^64)).trans (decide_eq_false (by omega))
  have zf : (cmpSpec (257 : BitVec 64) (BitVec.ofNat 64 i)).ZF = false :=
    (cmpNatZF (by decide : 257 < 2^64) (by omega : i < 2^64)).trans (decide_eq_false (by omega))
  have count : (257 : BitVec 64) - BitVec.ofNat 64 i = BitVec.ofNat 64 (257-i) := by
    have hi : (BitVec.ofNat 64 i).toNat = i := Nat.mod_eq_of_lt (by omega)
    apply BitVec.eq_of_toNat_eq
    have le : (BitVec.ofNat 64 i).toNat ≤ (257 : BitVec 64).toNat := by
      rw [hi]
      change i ≤ 257
      omega
    rw [subNat le, hi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rfl
  have ok : StoreOk Extracted.programImage m (digitAddr dst i) 1 0x1108f5 4 :=
    storeGuard (off := 24) (writableDigit write (by omega)) code_l1108dd (by decide)
  have signCF : (cmpSpec (BitVec.ofNat 64 w) 16).CF = decide (w < 16) :=
    cmpNatCF (by omega : w < 2^64) (by decide : 16 < 2^64)
  have newCarry : mergeGPR 8 (if (!(cmpSpec (BitVec.ofNat 64 w) 16).CF) = true
        then (1 : BitVec 8) else 0) 0 = BitVec.ofNat 64 (Naf.carry w) := by
    rw [signCF]
    by_cases h : w < 16
    · simp only [h, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, Naf.carry, ite_true]
      rfl
    · simp only [h, decide_false, Bool.not_false, ite_true, Naf.carry, ite_false]
      rfl
  have digitVal : (mergeGPR 8 ((BitVec.ofNat 64 w).setWidth 8 -
        (if (!(cmpSpec (BitVec.ofNat 64 w) 16).CF) = true then (32 : BitVec 32) else 0).setWidth 8)
        (BitVec.ofNat 64 w)).setWidth 8 = BitVec.ofInt 8 (Naf.digit w) := by
    rw [setWidth_mergeGPR8, ← negativeDigit, signCF]
    by_cases h : w < 16
    · simp only [h, Nat.not_le_of_lt h, decide_true, Bool.not_true, Bool.false_eq_true,
        ite_false, BitVec.setWidth_ofNat_of_le (by decide : 8 ≤ 64)]
      rfl
    · simp only [h, Nat.le_of_not_gt h, decide_false, Bool.not_false, ite_true, BitVec.setWidth_ofNat_of_le (by decide : 8 ≤ 64)]
      rfl
  have cb := Naf.carry_le_one w
  have room : i + Naf.carry w ≤ 128 := by omega
  have remaining : -(BitVec.ofNat 64 i) + 128 - BitVec.ofNat 64 (Naf.carry w) =
      BitVec.ofNat 64 (128-i-Naf.carry w) := by
    have sum : i + (128-i-Naf.carry w) + Naf.carry w = 128 := by omega
    have bv := congrArg (BitVec.ofNat 64) sum
    rw [BitVec.ofNat_add, BitVec.ofNat_add] at bv
    bv_omega
  have minSkip : (if (!(cmpSpec (BitVec.ofNat 64 (128-i-Naf.carry w)) 5).CF) = true
      then 5 else BitVec.ofNat 64 (128-i-Naf.carry w)) = BitVec.ofNat 64 (Naf.skip (128-i) w) := by
    have cf : (cmpSpec (BitVec.ofNat 64 (128-i-Naf.carry w)) 5).CF =
        decide (128-i-Naf.carry w < 5) :=
      cmpNatCF (by omega) (by decide : 5 < 2^64)
    rw [cf]
    by_cases h : 128-i-Naf.carry w < 5
    · simp only [h, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, Naf.skip,
        Nat.min_eq_right (by omega : 128-i-Naf.carry w ≤ 5)]
    · simp only [h, decide_false, Bool.not_false, ite_true, Naf.skip,
        Nat.min_eq_left (by omega : 5 ≤ 128-i-Naf.carry w)]
      rfl
  have skipLim : Naf.skip (128-i) w ≤ 5 := Nat.min_le_left ..
  have skipCF : (cmpSpec (BitVec.ofNat 64 (Naf.skip (128-i) w)) 2).CF =
      decide (Naf.skip (128-i) w < 2) :=
    cmpNatCF (by omega : Naf.skip (128-i) w < 2^64) (by decide : 2 < 2^64)
  have subCF : (subSpec (257 : BitVec 64) (BitVec.ofNat 64 i)).snd.CF = false := cf
  have subZF : (subSpec (257 : BitVec 64) (BitVec.ofNat 64 i)).snd.ZF = false := zf
  have route : ∃ q r : Registers,
      program.runBlock machine ⟨.l1108d0,b,m⟩ = .jump ⟨.l1108dd,q,m⟩ ∧
      program.runBlock machine ⟨.l1108dd,q,m⟩ = .jump ⟨oddTail i w,r,m'⟩ ∧
      OddRegisters a r sp dst i w := by
    by_cases one : Naf.skip (128-i) w < 2
    all_goals
      refine ⟨?_, ?_, ?branch, ?store, ?post⟩
      case branch =>
        cfg_eval [rsp, length, capacity, fields.limit]
        simp only [subCF, subZF, Bool.false_or, Bool.false_eq_true, ite_false, count]
        <;> rfl
      case store =>
        cfg_eval [rsp, length, window, dstGet, neg, width, half, radix, fields.half, fields.radix]
        rw [ite_eq_left ok, digitVal, ite_eq_left bits, bitsWord, newCarry, remaining, minSkip, skipCF]
        first
        | rw [decide_eq_true one, ite_eq_left (by rfl), show oddTail i w = .l110830 from ite_eq_left one]
        | rw [decide_eq_false one, ite_eq_right (by decide : false ≠ true),
            show oddTail i w = .l110912 from ite_eq_right one]
      case post =>
        refine ⟨regs.stack, regs.width, regs.bitIndex, regs.length, rfl, rfl, rfl, dest, ?_⟩
        intro ⟨j,hj⟩ keep
        simp only [List.mem_cons, List.not_mem_nil, or_false] at keep
        rcases keep with rfl | rfl | rfl | rfl
        · exact regs.saved 22 (by decide)
        · exact regs.saved 39 (by decide)
        · exact regs.saved 50 (by decide)
        · exact regs.saved 51 (by decide)
  obtain ⟨q,r,step,store,post⟩ := route
  exact ⟨r, (continueJump step).trans (continueJump store), post⟩

end K256.Proofs.Verify.Core.Lincomb.Recode
