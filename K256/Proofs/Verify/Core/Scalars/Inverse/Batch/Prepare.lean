import K256.Proofs.Verify.Core.Scalars.Inverse.Batch.Registers
import K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch.Input
import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Verify.Core.Scalars.Inverse.Batch

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Verify.LIR
open Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Affine.Invert
open Generate.Generator.Affine.Invert.Core (signedAt)
open Generate.Generator.Affine.Invert.Core.Batch (lowWord lowWord_congruent)
open SafeGcd.Batch (Words)

private theorem signedAt_zero {p : Ram} {addr : Word} {x : Int}
    (h : signedAt p addr x)
    (lo : memLoad p addr 64 = 0)
    (lo₁ : memLoad p (addr + 8) 64 = 0)
    (lo₂ : memLoad p (addr + 16) 64 = 0)
    (lo₃ : memLoad p (addr + 24) 64 = 0) : x = 0 := by
  obtain ⟨w, neg, words, _, rfl⟩ := h
  have h₀ : w[0] = 0 := (words 0 (by decide)).symm.trans
    (by simpa only [wordAddr, Nat.mul_zero, BitVec.add_zero] using lo)
  have h₁ : w[1] = 0 := (words 1 (by decide)).symm.trans lo₁
  have h₂ : w[2] = 0 := (words 2 (by decide)).symm.trans lo₂
  have h₃ : w[3] = 0 := (words 3 (by decide)).symm.trans lo₃
  have hv : value w = 0 := by
    simp only [value, h₀, h₁, h₂, h₃]
    decide +kernel
  rw [hv]
  cases neg <;> rfl

private def selectCount (n : Word) : BitVec 32 :=
  let low := n.setWidth 32
  let mask := (((n - 62).setWidth 32 &&& ~~~low) >>> 31).setWidth 8
  ((low ^^^ (62 : BitVec 32)) &&& -mask.setWidth 32) ^^^ (62 : BitVec 32)

private theorem selectCount_eq (n : Nat) :
    selectCount (BitVec.ofNat 64 (591 - n)) = BitVec.ofNat 32 (count n) := by
  have small : ∀ k : Fin 592, selectCount (BitVec.ofNat 64 k.val) =
      BitVec.ofNat 32 (min 62 k.val) := by decide +kernel
  exact small ⟨591-n, by omega⟩

private def initialWords (delta : Word) (p : Ram) (sp : Word) : Words where
  delta := delta
  f := lowWord (memLoad p (base sp + 8) 64) (memLoad p (base sp + 40) 8)
  g := lowWord (memLoad p (base sp + 48) 64) (memLoad p (base sp + 80) 8)
  u := 1
  v := 0
  q := 0
  r := 1

private theorem initialWords_low {a b : Registers} {m p : Ram} {sp : Word} {s n : Nat}
    {d e : Int} (state : LoopState a m sp s n b p d e) (hn : n ≤ 591) :
    SafeGcd.LowBitsEq 63 (SafeGcd.Batch.state (initialWords (b[12].get 64) p sp))
      (Inverse.model s n) := by
  refine ⟨?_, ?_, ?_⟩
  · change (b[12].get 64).toInt = _
    rw [state.delta]
    change (BitVec.ofInt 64 (Inverse.model s n).delta).toInt = _
    have h := Generate.Generator.Affine.Invert.Core.Batch.deltaBound n ⟨1, domain.n, s⟩
    change (Inverse.model s n).delta.natAbs ≤ 1+2*n at h
    apply BitVec.toInt_ofInt_eq_self (by decide) <;> omega
  · simpa only [SafeGcd.Batch.state, initialWords, BitVec.add_assoc,
      show (8 : Word) + 32 = 40 from rfl] using lowWord_congruent state.fValue
  · simpa only [SafeGcd.Batch.state, initialWords, BitVec.add_assoc,
      show (48 : Word) + 32 = 80 from rfl] using lowWord_congruent state.gValue

private theorem loadInputs {b : Registers} {p : Ram} {sp : Word} {n : Nat}
    (rsp : b[4].get 64 = base sp)
    (remaining : b[6].get 64 = BitVec.ofNat 64 (591-n))
    (window : Writable Extracted.programImage p (base sp) 344) (more : n < 591) :
    ∃ (c : Registers) (q : Ram), program.runBlock (dialect Extracted.programImage) ⟨.l109824, b, p⟩ =
      .jump ⟨.l10988a, c, q⟩ ∧
      c[2] = b[2] ∧ c[4] = b[4] ∧ c[12] = b[12] ∧
      c[6].get 64 = memLoad p (base sp + 8) 64 ∧
      c[0].get 64 = (memLoad p (base sp + 40) 8).setWidth 64 ∧
      c[9].get 32 = BitVec.ofNat 32 (count n) ∧
      (∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → c[i] = b[i]) ∧
      RamWriteFrame p q (setupWrites sp) ∧
      memLoad q (base sp + 176) 8 = memLoad p (base sp + 80) 8 ∧
      memLoad q (base sp + 336) 64 = BitVec.ofNat 64 (591-n) := by
  have chosen := selectCount_eq n
  dsimp only [selectCount] at chosen
  have flag : (xorFlags (BitVec.ofNat 32 (count n))).ZF.getD false = false := by
    have bound : 0 < count n ∧ count n ≤ 62 := by unfold count; omega
    simp only [xorFlags, Option.getD_some, Bool.eq_false_iff]
    intro he
    have hz := congrArg BitVec.toNat (LawfulBEq.eq_of_beq he)
    change Nat.mod (count n) (2 ^ 32) = 0 at hz
    have small : count n < 2 ^ 32 := by omega
    exact (Nat.ne_of_gt bound.1) ((Nat.mod_eq_of_lt small).symm.trans hz)
  refine ⟨?c, ?q, ?run, ?post⟩
  case run =>
    cfg_eval [b_l109824, b_l109824_1, rsp, remaining]
    segment_words []
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l109824)
    simp only [chosen, flag, Bool.false_eq_true, ↓reduceIte]
    rfl
  case post =>
    refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · segment_words []
    · segment_words []
    · change ((BitVec.ofNat 32 (count n)).setWidth 64).setWidth 32 = _
      rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
    · intro ⟨i, hi⟩ hh
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
      rcases hh with rfl | rfl | rfl | rfl <;> rfl
    · have bounds := window.readable.low
      unfold setupWrites
      slot_state region
    · segment_words []
    · segment_words []

private theorem initializeRows {c : Registers} {q : Ram} {sp : Word} {left : Nat}
    {f g delta : Word} {signF signG : BitVec 8}
    (window : Writable Extracted.programImage q (base sp) 344)
    (rsp : c[4].get 64 = base sp) (d : c[12].get 64 = delta)
    (rf : c[6].get 64 = f) (rg : c[2].get 64 = g)
    (sf : c[0].get 64 = signF.setWidth 64)
    (sg : memLoad q (base sp + 176) 8 = signG)
    (counter : c[9].get 32 = BitVec.ofNat 32 left) :
    ∃ out : Registers, program.runBlock (dialect Extracted.programImage) ⟨.l10988a, c, q⟩ =
      .jump ⟨.l109925, out, q⟩ ∧
      out[4] = c[4] ∧ out[9].get 32 = BitVec.ofNat 32 left ∧
      (∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → out[i] = c[i]) ∧
      Inner out ⟨delta, lowWord f signF, lowWord g signG, 1, 0, 0, 1⟩ left := by
  have k : (c[9].get 64).setWidth 32 = BitVec.ofNat 32 left :=
    (BitVec.setWidth_setWidth_of_le _ (by decide)).trans counter
  refine ⟨?out, ?run, ?post⟩
  case run =>
    cfg_eval [b_l10988a, b_l10988a_1, rsp, d, rf, rg, sf, sg, k]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l10988a)
    rfl
  case post =>
    refine ⟨rfl, counter, ?_, ⟨d, ?_, ?_, rfl, ?_, ?_, rfl, ?_⟩⟩
    · intro ⟨i, hi⟩ hh
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
      rcases hh with rfl | rfl | rfl | rfl <;> rfl
    · lifted_word_eq [lowWord]
    · lifted_word_eq [lowWord]
    · lifted_word_eq []
    · lifted_word_eq []
    · change ((BitVec.ofNat 32 left).setWidth 64).setWidth 32 = _
      rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

theorem prepare {a b : Registers} {m p : Ram} {sp : Word} {s n : Nat} {d e : Int}
    (h : Entry a m sp s) (state : LoopState a m sp s n b p d e) (more : n < 591) :
    (∃ c, Reaches .l1097fe b p .l109948 c p ∧ LoopState a m sp s n c p d e ∧
      (Inverse.model s n).g = 0) ∨
    ∃ c q w, Reaches .l1097fe b p .l109925 c q ∧ Inner c w (count n) ∧
      SafeGcd.LowBitsEq 63 (SafeGcd.Batch.state w) (Inverse.model s n) ∧
      SafeGcd.Batch.matrix w = SafeGcd.Matrix.identity ∧
      c[4] = b[4] ∧ c[9].get 32 = BitVec.ofNat 32 (count n) ∧
      (∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → c[i] = b[i]) ∧
      RamWriteFrame p q (setupWrites sp) ∧
      memLoad q (base sp + 336) 64 = BitVec.ofNat 64 (591-n) := by
  have room := h.depthBound
  have hi := h.high
  have window : Writable Extracted.programImage p (base sp) 344 :=
    (h.stack.of_frame state.frame).sub (by unfold base; bv_omega) (by unfold base; bv_omega)
  have rd : Readable p (base sp) 80 := window.readable.sub (by bv_omega) (by bv_omega)
  have rsp : b[4].get 64 = base sp := congrArg (Value.get 64) state.rsp
  obtain ⟨b', guard, g, kept⟩ := zeroGuard rsp rd
  have controls (i : Fin Reg.count) (hi : i.val ∈ [22,39,50,51]) : b'[i] = b[i] := by
    apply kept
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
    rcases hi with h | h | h | h <;> simp only [h, or_true, true_or]
  by_cases hz : memLoad p (base sp + 48) 64 = 0 ∧ memLoad p (base sp + 56) 64 = 0 ∧
      memLoad p (base sp + 64) 64 = 0 ∧ memLoad p (base sp + 72) 64 = 0
  · rw [ite_eq_left hz] at guard
    have stopped : LoopState a m sp s n b' p d e :=
      { state with
        rsp := (kept 4 (by decide)).trans state.rsp
        delta := (kept 12 (by decide)).trans state.delta
        remaining := (kept 6 (by decide)).trans state.remaining
        kept := fun i hi => (controls i hi).trans (state.kept i hi) }
    refine Or.inl ⟨b', guard, stopped, ?_⟩
    apply signedAt_zero state.gValue hz.1
    · simpa only [BitVec.add_assoc, show (48 : Word) + 8 = 56 from rfl] using hz.2.1
    · simpa only [BitVec.add_assoc, show (48 : Word) + 16 = 64 from rfl] using hz.2.2.1
    · simpa only [BitVec.add_assoc, show (48 : Word) + 24 = 72 from rfl] using hz.2.2.2
  · rw [ite_eq_right hz] at guard
    have rsp' := (kept 4 (by decide)).trans state.rsp
    have remaining := (kept 6 (by decide)).trans state.remaining
    obtain ⟨c, q, init, rg, rc, dc, rf, sf, k, keptC, frame, sg, rem⟩ :=
      loadInputs (congrArg (Value.get 64) rsp') (congrArg (Value.get 64) remaining) window more
    obtain ⟨out, rows, ro, ko, keptOut, inner⟩ :=
      initializeRows (window.of_frame frame) (congrArg (Value.get 64) (rc.trans rsp'))
        (congrArg (Value.get 64) (dc.trans (kept 12 (by decide)))) rf
        (congrArg (Value.get 64) (rg.trans g)) sf sg k
    refine Or.inr ⟨out, q, initialWords (b[12].get 64) p sp, ?_, inner,
      initialWords_low state (Nat.le_of_lt more), rfl,
      ro.trans (rc.trans (kept 4 (by decide))), ko, ?_, frame, rem⟩
    · refine guard.trans ?_
      refine .step (b := ⟨⟨.l10988a, c, q⟩, []⟩) ?_ (.step ?_ (.refl _))
      · change program.step _ _ = _
        simp only [Program.step, init, Transfer.next]
      · change program.step _ _ = _
        simp only [Program.step, rows, Transfer.next]
    · intro i hi
      exact (keptOut i hi).trans ((keptC i hi).trans (controls i hi))

end K256.Proofs.Verify.Core.Scalars.Inverse.Batch
