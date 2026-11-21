import K256.Proofs.Verify.Core.Lincomb.Recode.Setup
import K256.Proofs.Verify.Core.Lincomb.Recode.Window

namespace K256.Proofs.Verify.Core.Lincomb.Recode

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

abbrev pushRead (m : Ram) (sp : BitVec 64) : Ram :=
  memStore m (sp-144) (0x11085e : BitVec 64)

structure ReadArgs (a b r : Registers) (sp : BitVec 64) (i c : Nat) : Prop where
  rsp : r[4] = ⟨64, sp-144⟩
  iterator : r[7].get 64 = sp-88
  wordIndex : r[6].get 64 = BitVec.ofNat 64 (i/64)
  offset : r[3] = ⟨64, BitVec.ofNat 64 (i%64)⟩
  offsetNeg : r[5] = b[5]
  width : r[12] = b[12]
  carry : r[13] = b[13]
  length : r[14] = b[14]
  bitIndex : r[15] = b[15]
  saved : ControlSaved a r

theorem callRead {a b : Registers} {m : Ram} {sp : BitVec 64} {i c : Nat}
    (regs : LoopRegisters a b sp i c) (hi : i < 128)
    (ok : StoreOk Extracted.programImage m (sp-144) 8 0x110859 5) :
    ∃ r, program.runBlock machine ⟨.l110847,b,m⟩ =
      .call ⟨.l124100,r,pushRead m sp⟩ (returnTo .l11085e 0x11085e) ∧ ReadArgs a b r sp i c := by
  have rsp : b[4].get 64 = sp-136 := congrArg (Value.get 64) regs.stack
  have idx : b[15].get 64 = BitVec.ofNat 64 i := congrArg (Value.get 64) regs.bitIndex
  have word : (BitVec.ofNat 64 i) >>> 6 = BitVec.ofNat 64 (i/64) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
      Nat.reducePow, Nat.mod_eq_of_lt (a := i) (by omega : i < 2^64),
      Nat.mod_eq_of_lt (a := i/64) (by omega : i/64 < 2^64)]
  have offset : (((BitVec.ofNat 64 i).setWidth 32) &&& 63).setWidth 64 = BitVec.ofNat 64 (i%64) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth_of_le (by decide), BitVec.toNat_and, BitVec.toNat_setWidth,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2^64),
      Nat.mod_eq_of_lt (by omega : i < 2^32), BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : i%64 < 2^64)]
    exact Nat.and_two_pow_sub_one_eq_mod _ 6
  refine ⟨?_, ?step, ?regs⟩
  case step =>
    cfg_eval [rsp, idx, ok, word, offset]
    rfl
  case regs =>
    refine ⟨rfl, rfl, rfl, congrArg (fun x : BitVec 64 => (⟨64,x⟩ : Value)) offset, rfl, rfl, rfl, rfl, rfl, ?_⟩
    intro ⟨j, bound⟩ hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl
    · exact regs.saved 22 (by decide)
    · exact regs.saved 39 (by decide)
    · exact regs.saved 50 (by decide)
    · exact regs.saved 51 (by decide)

private theorem maskedShift (x : BitVec 64) :
    shiftCount 64 ((x.setWidth 32).setWidth 8) = x.toNat % 64 := by
  simp only [shiftCount, ite_true, BitVec.toNat_setWidth, Nat.reducePow]
  omega

private theorem rightCount (i : Nat) :
    shiftCount 64 (((BitVec.ofNat 64 (i%64)).setWidth 32).setWidth 8) = i%64 := by
  rw [maskedShift, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i%64 < 2^64), Nat.mod_mod]

private theorem leftCount {i : Nat} (hi : i < 128) (cross : ¬i%64+5 < 64) :
    shiftCount 64 (((-(BitVec.ofNat 64 i)).setWidth 32).setWidth 8) = 64-i%64 := by
  have pos : 0 < i := by omega
  rw [maskedShift, BitVec.toNat_neg, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2^64)]
  omega

abbrev shiftedWindow (lo hi : BitVec 64) (i : Nat) : BitVec 64 :=
  let s := i % 64
  let x := if i < 64 then lo else hi
  let y := if i < 64 then hi else 0
  if s + 5 < 64 then x >>> s else (y <<< (64-s)) ||| (x >>> s)

theorem shiftWindow {a b : Registers} {m : Ram} {sp : BitVec 64} {i c : Nat}
    {lo hi : BitVec 64}
    (regs : LoopRegisters a b sp i c) (bound : i < 128)
    (offset : b[3].get 64 = BitVec.ofNat 64 (i%64))
    (x : b[0].get 64 = if i < 64 then lo else hi)
    (y : b[2].get 64 = if i < 64 then hi else 0) :
    ∃ r q,
      program.runBlock machine ⟨.l11085e,b,m⟩ =
        .jump ⟨(if i%64+5 < 64 then .l110868 else .l110880), r,m⟩ ∧
      program.runBlock machine ⟨(if i%64+5 < 64 then .l110868 else .l110880),r,m⟩ =
        .jump ⟨.l11088d,q,m⟩ ∧
      LoopRegisters a q sp i c ∧ q[2].get 64 = shiftedWindow lo hi i := by
  have width : b[12].get 64 = 5 := congrArg (Value.get 64) regs.width
  have neg : b[5].get 64 = -(BitVec.ofNat 64 i) := congrArg (Value.get 64) regs.negIndex
  have stepCF : (cmpSpec (BitVec.ofNat 64 (i%64) + 5) 64).CF = decide (i%64+5 < 64) := by
    rw [cmpSpec_CF, BitVec.toNat_add, BitVec.toNat_ofNat]
    congr 1
    simp only [BitVec.reduceToNat, Nat.mod_eq_of_lt (a := i%64) (by omega : i%64 < 2^64),
      Nat.mod_eq_of_lt (a := i%64+5) (by omega : i%64+5 < 2^64)]
  by_cases small : i%64+5 < 64
  · rw [ite_eq_left small]
    refine ⟨?_, ?_, ?branch, ?shift, ?post⟩
    case branch =>
      cfg_eval [offset, width]
      have skip : (!(cmpSpec (BitVec.ofNat 64 (i%64) + 5) 64).CF) ≠ true := by
        rw [stepCF, decide_eq_true small]
        decide
      rw [ite_eq_right skip]
    case shift =>
      cfg_eval [offset, x, rightCount i]
      rfl
    case post =>
      refine ⟨⟨regs.stack, regs.width, regs.bitIndex, regs.length, regs.negIndex, regs.carry, ?_⟩, ?_⟩
      · intro ⟨j, bound⟩ hj
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl | rfl
        · exact regs.saved 22 (by decide)
        · exact regs.saved 39 (by decide)
        · exact regs.saved 50 (by decide)
        · exact regs.saved 51 (by decide)
      · change (if i < 64 then lo else hi) >>>
          shiftCount 64 (((BitVec.ofNat 64 (i%64)).setWidth 32).setWidth 8) = _
        rw [rightCount i, shiftedWindow, ite_eq_left small]
  · rw [ite_eq_right small]
    refine ⟨?_, ?_, ?branch, ?shift, ?post⟩
    case branch =>
      cfg_eval [offset, width]
      have take : (!(cmpSpec (BitVec.ofNat 64 (i%64) + 5) 64).CF) = true := by
        rw [stepCF, decide_eq_false small]
        rfl
      rw [ite_eq_left take]
    case shift =>
      cfg_eval [offset, x, y, neg, rightCount i, leftCount bound small]
      rfl
    case post =>
      refine ⟨⟨regs.stack, regs.width, regs.bitIndex, regs.length, regs.negIndex, regs.carry, ?_⟩, ?_⟩
      · intro ⟨j, bound⟩ hj
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl | rfl
        · exact regs.saved 22 (by decide)
        · exact regs.saved 39 (by decide)
        · exact regs.saved 50 (by decide)
        · exact regs.saved 51 (by decide)
      · change (if i < 64 then hi else 0) <<<
          shiftCount 64 (((-(BitVec.ofNat 64 i)).setWidth 32).setWidth 8) |||
            (if i < 64 then lo else hi) >>>
              shiftCount 64 (((BitVec.ofNat 64 (i%64)).setWidth 32).setWidth 8) = _
        rw [rightCount i, leftCount bound small, shiftedWindow, ite_eq_right small]

end K256.Proofs.Verify.Core.Lincomb.Recode
