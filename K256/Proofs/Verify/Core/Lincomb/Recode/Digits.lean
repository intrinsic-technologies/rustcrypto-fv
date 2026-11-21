import K256.Proofs.Verify.Core.Lincomb.Recode.Read

namespace K256.Proofs.Verify.Core.Lincomb.Recode

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

abbrev digitAddr (dst : BitVec 64) (i : Nat) : BitVec 64 := dst + BitVec.ofNat 64 i

theorem digitAddress {dst : BitVec 64} {i : Nat} (low : dst.toNat + 257 ≤ 2^32)
    (hi : i < 257) : (digitAddr dst i).toNat = dst.toNat + i := by
  simp only [digitAddr, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := i) (by omega : i < 2^64),
    Nat.mod_eq_of_lt (by omega : dst.toNat+i < 2^64)]

theorem writableDigit {m : Ram} {dst : BitVec 64} {i : Nat}
    (w : Writable Extracted.programImage m dst 257) (hi : i < 257) :
    Writable Extracted.programImage m (digitAddr dst i) 1 := by
  have addr := digitAddress w.readable.low hi
  exact w.sub (by rw [addr]; omega) (by rw [addr]; omega)

theorem storeDigitFrame {m : Ram} {dst : BitVec 64} {i : Nat}
    (w : Writable Extracted.programImage m dst 257) (hi : i < 257) (v : BitVec 8) :
    RamWriteFrame m (memStore m (digitAddr dst i) v) [⟨dst.toNat,257⟩] := by
  refine (RamWriteFrame.refl _ _).memStore _ ⟨_, List.mem_singleton_self _, ?_⟩
  have low := w.readable.low
  have addr := digitAddress low hi
  simp only [InRegion, addr, Nat.reduceDiv]
  omega

theorem digitBytes_zeroStore {m : Ram} {dst : BitVec 64} {ds : List Int} {i : Nat}
    (h : DigitBytes m dst ds) (w : Writable Extracted.programImage m dst 257)
    (hi : i < 257) (past : ds.length ≤ i) :
    DigitBytes (memStore m (digitAddr dst i) (0 : BitVec 8)) dst ds := by
  intro j
  by_cases same : i = j.val
  · subst i
    rw [memLoad_memStore_same _ _ _ (by decide) (by decide), List.getElem?_eq_none past]
    rfl
  · have apart : RangeApart (digitAddr dst i) 1 (digitAddr dst j.val) 1 := by
      intro k hk l hl he
      have sk : k = 0 := by omega
      have sl : l = 0 := by omega
      subst k l
      have eq : digitAddr dst i = digitAddr dst j.val := by
        bv_omega
      have addr1 := digitAddress w.readable.low hi
      have addr2 := digitAddress w.readable.low j.isLt
      have hn := congrArg BitVec.toNat eq
      omega
    rw [memLoad_memStore_of_rangeApart _ _ _ _ _ apart]
    exact h j

theorem classifyWindow {a b : Registers} {m : Ram} {sp dst : BitVec 64} {i c : Nat}
    {lo hi : BitVec 64} (regs : LoopRegisters a b sp i c) (bound : i < 128) (carry : c ≤ 1)
    (shifted : b[2].get 64 = shiftedWindow lo hi i) (fields : LoopMemory m sp dst)
    (maskRead : LoadOk m (sp-96) 8) (dstRead : LoadOk m (sp-120) 8) :
    let window := (((hi ++ lo).toNat / 2^i) % (32 : Nat)) + c
    ∃ r : Registers, program.runBlock machine ⟨.l11088d,b,m⟩ =
      .jump ⟨(if window % 2 = 0 then .l11089f else .l1108d0),r,m⟩ ∧
      LoopRegisters a r sp i c ∧ r[2].get 64 = BitVec.ofNat 64 window ∧
      r[6] = ⟨64, dst⟩ := by
  let window := (((hi ++ lo).toNat / 2^i) % (32 : Nat)) + c
  change ∃ r : Registers, program.runBlock machine ⟨.l11088d,b,m⟩ =
      .jump ⟨(if window % 2 = 0 then .l11089f else .l1108d0),r,m⟩ ∧
      LoopRegisters a r sp i c ∧ r[2].get 64 = BitVec.ofNat 64 window ∧ r[6] = ⟨64,dst⟩
  have rsp : b[4].get 64 = sp-136 := congrArg (Value.get 64) regs.stack
  have cy : b[13].get 64 = BitVec.ofNat 64 c := congrArg (Value.get 64) regs.carry
  have calcWindow : (shiftedWindow lo hi i &&& 31) + BitVec.ofNat 64 c = BitVec.ofNat 64 window :=
    windowWord lo hi i c bound carry
  have parity : (testFlags ((BitVec.ofNat 64 window).setWidth 8 &&& 1)).ZF.getD false =
      decide (window % 2 = 0) := by
    unfold testFlags
    apply Bool.eq_iff_iff.mpr
    simp only [Option.getD_some, beq_iff_eq, decide_eq_true_eq]
    rw [← BitVec.toNat_inj, BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    change (((window % (2^64)) % (2^8)) &&& 1) = 0 ↔ _
    rw [show (1 : Nat) = 2^1-1 by decide, Nat.and_two_pow_sub_one_eq_mod]
    have flips : window ≤ 32 := by
      have onlyFive := Nat.mod_lt ((hi ++ lo).toNat / 2^i) (by decide : 0 < 32)
      dsimp only [window]
      omega
    rw [Nat.mod_eq_of_lt (by omega : window < 2^64), Nat.mod_eq_of_lt (by omega : window < 2^8)]
  by_cases even : window % 2 = 0
  · rw [ite_eq_left even]
    refine ⟨?_, ?step, ?post⟩
    case step =>
      cfg_eval [rsp, cy, shifted, maskRead, dstRead, fields.mask, fields.buffer, calcWindow, parity, even]
      simp only [decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
      <;> rfl
    case post =>
      refine ⟨⟨regs.stack, regs.width, regs.bitIndex, regs.length, regs.negIndex, regs.carry, ?_⟩, rfl,rfl⟩
      intro ⟨j, bound⟩ hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl
      · exact regs.saved 22 (by decide)
      · exact regs.saved 39 (by decide)
      · exact regs.saved 50 (by decide)
      · exact regs.saved 51 (by decide)
  · rw [ite_eq_right even]
    refine ⟨?_, ?step, ?post⟩
    case step =>
      cfg_eval [rsp, cy, shifted, maskRead, dstRead, fields.mask, fields.buffer, calcWindow, parity, even]
      simp only [decide_false, Bool.not_false, ite_true]
      <;> rfl
    case post =>
      refine ⟨⟨regs.stack, regs.width, regs.bitIndex, regs.length, regs.negIndex, regs.carry, ?_⟩, rfl,rfl⟩
      intro ⟨j, bound⟩ hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl
      · exact regs.saved 22 (by decide)
      · exact regs.saved 39 (by decide)
      · exact regs.saved 50 (by decide)
      · exact regs.saved 51 (by decide)

end K256.Proofs.Verify.Core.Lincomb.Recode
