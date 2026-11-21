import K256.Proofs.Generate.Generator.Multiply.Prepare.Frame
import K256.Proofs.Generate.LIR.Fn110b80.Frame
import K256.Proofs.Generate.Generator.Multiply.Split.Parameters
import K256.Proofs.Generate.Generator.Multiply.Split.WideProduct
import K256.Proofs.Common.Invert.LinearCombination.Wide

namespace K256.Proofs.Generate.Generator.Multiply.Prepare

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters.Secp256k1
open Common.Invert.LinearCombination (Limbs subRaw subWord borrow subRaw_toNat)

private def limbs (w : Vector (BitVec 64) 4) : Limbs :=
  ⟨w[0], w[1], w[2], w[3]⟩

private def negateWords (p x : Vector (BitVec 64) 4) : Vector (BitVec 64) 4 :=
  let r := (subRaw (limbs p) (limbs x)).1
  if x[0] ||| x[1] ||| x[2] ||| x[3] = 0 then #v[0, 0, 0, 0] else #v[r.l0, r.l1, r.l2, r.l3]

private theorem suppressZero (t w : BitVec 64) :
    ((if (orFlags t).ZF.getD false = true then (1 : BitVec 8) else 0).setWidth 64 - 1) &&& w =
      if t = 0 then 0 else w := by
  change ((if (t == 0) = true then (1 : BitVec 8) else 0).setWidth 64 - 1) &&& w = _
  by_cases h : t = 0
  · rw [h]
    change 0#64 &&& w = 0#64
    exact BitVec.zero_and
  · simp only [beq_iff_eq, ite_eq_right h]
    change BitVec.allOnes 64 &&& w = w
    exact BitVec.allOnes_and

private theorem scalarValue_injective {a b : Vector (BitVec 64) 4}
    (he : Split.scalarValue a = Split.scalarValue b) : a = b := by
  apply Vector.ext
  intro i hi
  apply BitVec.eq_of_toNat_eq
  have a0 := a[0].isLt
  have a1 := a[1].isLt
  have a2 := a[2].isLt
  have a3 := a[3].isLt
  have b0 := b[0].isLt
  have b1 := b[1].isLt
  have b2 := b[2].isLt
  have b3 := b[3].isLt
  change (limbs a).toNat = (limbs b).toNat at he
  simp only [limbs, Limbs.toNat, Nat.reducePow] at he
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with
    rfl | rfl | rfl | rfl <;> omega

private theorem testZero_eq (a : Vector (BitVec 64) 4) :
    (a[0] ||| a[1] ||| a[2] ||| a[3] = 0) ↔ Split.scalarValue a = 0 := by
  change (a[0] ||| a[1] ||| a[2] ||| a[3] = 0#64) ↔ _
  rw [BitVec.or_eq_zero_iff, BitVec.or_eq_zero_iff, BitVec.or_eq_zero_iff]
  simp only [BitVec.toNat_eq, BitVec.toNat_zero]
  change _ ↔ (limbs a).toNat = 0
  simp only [limbs, Limbs.toNat, Nat.reducePow]
  omega

private theorem negateWords_eq {x : Nat} (hx : x < domain.n) :
    negateWords (scalarWords domain.n) (scalarWords x) =
      scalarWords (if x = 0 then 0 else domain.n - x) := by
  have hn : domain.n < 2^256 := by decide +kernel
  generalize domain.n = n at hx hn ⊢
  have hv := Split.scalarWords_value x (Nat.lt_trans hx hn)
  have hp := Split.scalarWords_value n hn
  let p := limbs (scalarWords n)
  let a := limbs (scalarWords x)
  let r := (subRaw p a).1
  let w := #v[r.l0, r.l1, r.l2, r.l3]
  have hw : Split.scalarValue w = r.toNat := rfl
  have hsmall := Split.scalarValue_lt w
  have hdiff := (subRaw_toNat p a).2
  change r.toNat + a.toNat = p.toNat + 2^256 * (subRaw p a).2.toNat at hdiff
  change a.toNat = x at hv
  change p.toNat = n at hp
  rw [hw] at hsmall
  simp only [negateWords, testZero_eq, Split.scalarWords_value _ (Nat.lt_trans hx hn)]
  by_cases hz : x = 0
  · simp only [ite_eq_left hz]
    decide +kernel
  · simp only [ite_eq_right hz]
    change w = _
    apply scalarValue_injective
    rw [hw, Split.scalarWords_value _ (by omega)]
    rw [hv, hp] at hdiff
    omega

set_option maxHeartbeats 1800000 in
set_option maxRecDepth 8192 in
private theorem scalarNegMachine {fr : Activation} {a : Registers} {m : Ram}
    {p x : Vector (BitVec 64) 4}
    (entry : Atom.All Extracted.programImage a m (Fn110b80.frameAt .l110b80 fr))
    (src : Readable m fr.rsi 32) (dst : Writable Extracted.programImage m fr.rdi 32)
    (modulus : Readable m fr.rdx 32)
    (aboveSrc : fr.rsp.toNat + 8 ≤ fr.rsi.toNat) (aboveDst : fr.rsp.toNat + 8 ≤ fr.rdi.toNat)
    (apart : fr.rdx.toNat + 32 ≤ fr.rsp.toNat - 48 ∨ fr.rsp.toNat ≤ fr.rdx.toNat)
    (input : WordsAt m fr.rsi 64 x) (modWords : WordsAt m fr.rdx 64 p) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l110b80, a, m⟩, []⟩ out ∧
      out.tag = some ⟨64,fr.ret⟩ ∧ Atom.All Extracted.programImage out.values out.store (Fn110b80.doneAt fr) ∧
      ParseSignature.ArgumentWidths out.values ∧
      RamWriteFrame m out.store [⟨fr.rsp.toNat - 48,48⟩,⟨fr.rdi.toNat,32⟩] ∧
      WordsAt out.store fr.rdi 64 (negateWords p x) := by
  simp only [Fn110b80.frameAt, Fn110b80.frameAtG1, Atom.All, Atom.Holds] at entry
  obtain ⟨sp, df, cx, dx, bx, bp, si, di, r8, r9, r12, r13, r14, r15, mx, ftw, fcw,
    retRead, ret, retLow, win, room, align, _⟩ := entry
  have sl := retRead.low
  have xl := src.low
  have pl := modulus.low
  have dl := dst.readable.low
  have v4 : a[4].get 64 = fr.rsp := congrArg (Value.get 64) sp
  have v2 : a[2].get 64 = fr.rdx := congrArg (Value.get 64) dx
  have v6 : a[6].get 64 = fr.rsi := congrArg (Value.get 64) si
  have v7 : a[7].get 64 = fr.rdi := congrArg (Value.get 64) di
  have v3 : a[3].get 64 = fr.rbx := congrArg (Value.get 64) bx
  have v5 : a[5].get 64 = fr.rbp := congrArg (Value.get 64) bp
  have v12 : a[12].get 64 = fr.r12 := congrArg (Value.get 64) r12
  have v13 : a[13].get 64 = fr.r13 := congrArg (Value.get 64) r13
  have v14 : a[14].get 64 = fr.r14 := congrArg (Value.get 64) r14
  have v15 : a[15].get 64 = fr.r15 := congrArg (Value.get 64) r15
  have loads {base : BitVec 64} {w : Vector (BitVec 64) 4} (hw : WordsAt m base 64 w) :
      memLoad m base 64 = w[0] ∧ memLoad m (base + 8) 64 = w[1] ∧
      memLoad m (base + 16) 64 = w[2] ∧ memLoad m (base + 24) 64 = w[3] := by
    refine ⟨?_, hw 1 (by decide), hw 2 (by decide), hw 3 (by decide)⟩
    simpa only [wordAddr, Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hw 0 (by decide)
  obtain ⟨x0, x1, x2, x3⟩ := loads input
  obtain ⟨p0, p1, p2, p3⟩ := loads modWords
  refine ⟨?out, Program.Exec.done ?run, ?tag, ?done_, ?widths, ?frame, ?words⟩
  case run =>
    unfold Program.step
    generate_block [v4, v2, v6, v7, v3, v5, v12, v13, v14, v15,
      BitVec.add_zero, Lift.reduceAddOffset, Lift.reduceSubOffset, Lift.reduceAddNeg, Lift.reduceSubNeg,
      BitVec.reduceAdd, BitVec.reduceSub]
    segment_words [x0, x1, x2, x3, p0, p1, p2, p3, ret, retLow, and_true]
    repeat' (refine Eq.trans (congrArg _ (ite_eq_left ?_)) ?_; slot_guard using code_l110b80)
    rfl
  case tag => rfl
  case done_ =>
    refine ⟨?_, df, ?_, ?_, ?_, ?_, ?_, ?_, mx, ftw, fcw, trivial⟩
    all_goals first | assumption | rfl | (segment_words []; rfl)
  case widths =>
    intro ⟨i, hi⟩ hm
    simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
    · change a[7].width = 64
      exact congrArg Value.width di
    all_goals rfl
  case frame =>
    dsimp only
    have depth : 48 ≤ fr.rsp.toNat := by omega
    slot_state region
  case words =>
    have zeroSub (u : BitVec 64) : (0 : BitVec 64) - u = -u := BitVec.zero_sub u
    intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    all_goals
      simp only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
      segment_words []
      rw [BitVec.or_comm x[1] x[0], suppressZero]
      by_cases hz : x[0] ||| x[1] ||| x[2] ||| x[3] = 0
      · simp only [negateWords, ite_eq_left hz] <;> rfl
      · simp only [negateWords, ite_eq_right hz, limbs, subRaw, subWord, borrow, zeroSub,
          Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]

set_option linter.unusedVariables false in
theorem scalarNegCall {fr : Activation} {a : Registers} {m : Ram}
    (atoms : Atom.All Extracted.programImage a m (Fn110b80.frameAt .l110b80 fr))
    (loaded : ∀ v ∈ Extracted.programImage, m[v.1]? = some v.2)
    (src : Readable m fr.rsi 32) (dst : Writable Extracted.programImage m fr.rdi 32)
    (aboveSrc : fr.rsp.toNat + 8 ≤ fr.rsi.toNat) (aboveDst : fr.rsp.toNat + 8 ≤ fr.rdi.toNat)
    (apart : fr.rsi.toNat + 32 ≤ fr.rdi.toNat ∨ fr.rdi.toNat + 32 ≤ fr.rsi.toNat)
    (order : fr.rdx = 0x2021a0) {x : Nat} (bound : x < domain.n)
    (input : WordsAt m fr.rsi 64 (scalarWords x)) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l110b80, a, m⟩, []⟩ out ∧
      out.tag = some ⟨64,fr.ret⟩ ∧ Atom.All Extracted.programImage out.values out.store (Fn110b80.doneAt fr) ∧
      ParseSignature.ArgumentWidths out.values ∧
      RamWriteFrame m out.store [⟨fr.rsp.toNat - 48,48⟩,⟨fr.rdi.toNat,32⟩] ∧
      WordsAt out.store fr.rdi 64 (scalarWords (if x = 0 then 0 else domain.n - x)) := by
  have atOrder := Split.parameterAt loaded (p := (0x2021a0 : BitVec 64)) (x := domain.n)
    (by simp only [Split.parameters, List.mem_cons, true_or, or_true])
  rw [← order] at atOrder
  have layout := atoms
  simp only [Fn110b80.frameAt, Fn110b80.frameAtG1, Atom.All, Atom.Holds] at layout
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, win, room, _⟩ := layout
  have sep := atOrder.apart win (by decide)
  have base_eq : (fr.rsp - (48 : BitVec 64)).toNat = fr.rsp.toNat - 48 :=
    BitVec.toNat_sub_of_le (by
      change 48 ≤ fr.rsp.toNat
      omega)
  have separate : fr.rdx.toNat + 32 ≤ fr.rsp.toNat - 48 ∨ fr.rsp.toNat ≤ fr.rdx.toNat := by
    rw [base_eq] at sep
    omega
  obtain ⟨out, exec, tag, done_, widths, frame, words⟩ :=
    scalarNegMachine atoms src dst atOrder.readable aboveSrc aboveDst separate input atOrder.words
  rw [negateWords_eq bound] at words
  exact ⟨out, exec, tag, done_, widths, frame, words⟩

end K256.Proofs.Generate.Generator.Multiply.Prepare
