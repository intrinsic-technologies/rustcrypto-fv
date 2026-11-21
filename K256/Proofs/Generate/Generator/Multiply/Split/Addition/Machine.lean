import K256.Proofs.Generate.Generator.Multiply.Split.Addition.Words
import K256.Proofs.Generate.Generator.Multiply.Split.Contract
import K256.Proofs.Common.Invert.LinearCombination.Core

namespace K256.Proofs.Generate.Generator.Multiply.Split.Addition

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters.Secp256k1

private theorem mergeFlag (b : Bool) :
    mergeGPR 8 (if b then 1 else 0) 0 = (if b then 1 else 0 : BitVec 64) := by
  cases b <;> decide

private theorem widenFlag (b : Bool) :
    ((if b then 1 else 0 : BitVec 8).setWidth 64) = (if b then 1 else 0 : BitVec 64) := by
  cases b <;> decide

private theorem widenSelector (b : Prop) [Decidable b] (v : BitVec 64) :
    (((if b then 1 else 0 : BitVec 8) &&& v.setWidth 8).setWidth 64) =
      ((if b then 1 else 0 : BitVec 64) &&& v) := by
  by_cases h : b
  · simp only [ite_eq_left h]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_and]
    by_cases hz : i = 0 <;> simp [hz, hi]
  · simp [h]

private theorem adcLow (c : Bool) (x y : BitVec 64) :
    (adcSpec c x y).1 = x + y + BitVec.ofNat 64 c.toNat := rfl

set_option maxHeartbeats 1800000 in
set_option maxRecDepth 8192 in
theorem run {fr : Activation} {a : Registers} {m : Ram} {x y p : Words}
    (entry : Atom.All Extracted.programImage a m (Fn1109b0.frameAt .l1109b0 fr))
    (srcX : Readable m fr.rsi 32) (srcY : Readable m fr.rdx 32)
    (modulus : Readable m fr.rcx 32) (dst : Writable Extracted.programImage m fr.rdi 32)
    (above : fr.rsp.toNat + 8 ≤ fr.rdi.toNat)
    (apart : ∀ src ∈ [fr.rsi, fr.rdx, fr.rcx],
      src.toNat + 32 ≤ fr.rsp.toNat - 64 ∨ fr.rsp.toNat ≤ src.toNat)
    (wx : WordsAt m fr.rsi 64 x) (wy : WordsAt m fr.rdx 64 y) (wp : WordsAt m fr.rcx 64 p) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l1109b0, a, m⟩, []⟩ out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧ Atom.All Extracted.programImage out.values out.store (Fn1109b0.doneAt fr) ∧
      ParseSignature.ArgumentWidths out.values ∧ WordsAt out.store fr.rdi 64 (addWords x y p) ∧
      RamWriteFrame m out.store [⟨fr.rsp.toNat - 64, 64⟩, ⟨fr.rdi.toNat, 32⟩] := by
  simp only [Fn1109b0.frameAt, Fn1109b0.frameAtG1, Atom.All, Atom.Holds] at entry
  obtain ⟨sp, df, cx, dx, bx, bp, si, di, r8, r9, r12, r13, r14, r15, mx, ftw, fcw,
    retRead, ret, retLow, win, room, align, _⟩ := entry
  have sl := retRead.low
  have xl := srcX.low
  have yl := srcY.low
  have pl := modulus.low
  have dl := dst.readable.low
  have ax := apart fr.rsi (by simp)
  have ay := apart fr.rdx (by simp)
  have ap := apart fr.rcx (by simp)
  have v4 : a[4].get 64 = fr.rsp := congrArg (Value.get 64) sp
  have v1 : a[1].get 64 = fr.rcx := congrArg (Value.get 64) cx
  have v2 : a[2].get 64 = fr.rdx := congrArg (Value.get 64) dx
  have v6 : a[6].get 64 = fr.rsi := congrArg (Value.get 64) si
  have v7 : a[7].get 64 = fr.rdi := congrArg (Value.get 64) di
  have v3 : a[3].get 64 = fr.rbx := congrArg (Value.get 64) bx
  have v5 : a[5].get 64 = fr.rbp := congrArg (Value.get 64) bp
  have v12 : a[12].get 64 = fr.r12 := congrArg (Value.get 64) r12
  have v13 : a[13].get 64 = fr.r13 := congrArg (Value.get 64) r13
  have v14 : a[14].get 64 = fr.r14 := congrArg (Value.get 64) r14
  have v15 : a[15].get 64 = fr.r15 := congrArg (Value.get 64) r15
  have loads {base : BitVec 64} {w : Words} (hw : WordsAt m base 64 w) :
      memLoad m base 64 = w[0] ∧ memLoad m (base + 8) 64 = w[1] ∧
      memLoad m (base + 16) 64 = w[2] ∧ memLoad m (base + 24) 64 = w[3] := by
    refine ⟨?_, hw 1 (by decide), hw 2 (by decide), hw 3 (by decide)⟩
    simpa only [wordAddr, Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hw 0 (by decide)
  obtain ⟨x0, x1, x2, x3⟩ := loads wx
  obtain ⟨y0, y1, y2, y3⟩ := loads wy
  obtain ⟨p0, p1, p2, p3⟩ := loads wp
  refine ⟨?out, Program.Exec.done ?run, ?tag, ?done_, ?widths, ?words, ?frame⟩
  case run =>
    unfold Program.step
    generate_block [v4, v1, v2, v6, v7, v3, v5, v12, v13, v14, v15,
      BitVec.add_zero, Lift.reduceAddOffset, Lift.reduceSubOffset, Lift.reduceAddNeg, Lift.reduceSubNeg,
      BitVec.reduceAdd, BitVec.reduceSub]
    segment_words [x0, x1, x2, x3, y0, y1, y2, y3, p0, p1, p2, p3, ret, retLow, and_true]
    repeat' (refine Eq.trans (congrArg _ (ite_eq_left ?_)) ?_; slot_guard using code_l1109b0)
    rfl
  case tag => rfl
  case done_ =>
    refine ⟨?_, df, ?_, ?_, ?_, ?_, ?_, ?_, mx, ftw, fcw, trivial⟩
    all_goals first | rfl | (segment_words []; rfl)
  case widths =>
    intro ⟨i, hi⟩ hm
    simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  case frame =>
    dsimp only
    have depth : 64 ≤ fr.rsp.toNat := by omega
    first | slot_state region |
      (repeat' refine RamWriteFrame.memStore ?_ _ ?_
       exact RamWriteFrame.refl _ _
       all_goals simp only [InRegions, InRegion, List.mem_cons, List.not_mem_nil, or_false,
         exists_eq_or_imp, exists_eq_left] <;> bv_omega)
  case words =>
    intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    all_goals
      simp only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
      segment_words []
      simp only [addWords, sum, Common.Invert.LinearCombination.subRaw, Common.Invert.LinearCombination.subWord,
        Common.Invert.LinearCombination.borrow, flagWord, selectWord,
        List.getElem_toArray, Vector.getElem_mk, List.getElem_cons_zero, List.getElem_cons_succ,
        setWidth_mergeGPR8,
        beq_iff_eq, adcLow, Common.Invert.LinearCombination.addSpec_low]
      simp only [mergeFlag, widenFlag, widenSelector]
      simp only [BitVec.ofNat_eq_ofNat, BitVec.zero_sub, BitVec.add_zero]

end K256.Proofs.Generate.Generator.Multiply.Split.Addition
