import K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch.Input
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR

private def selectCount (n : Word) : BitVec 32 :=
  let low := n.setWidth 32
  let mask := (((n - 62).setWidth 32 &&& ~~~low) >>> 31).setWidth 8
  ((low ^^^ (62 : BitVec 32)) &&& -mask.setWidth 32) ^^^ (62 : BitVec 32)

private theorem selectCount_eq (j : Nat) (hj : j < 10) :
    selectCount (BitVec.ofNat 64 (591 - roundsBefore j)) = BitVec.ofNat 32 (count j) := by
  have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨
      j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

private theorem loadInputs {b : Registers} {p : Ram} {sp : Word} {j : Nat} (hj : j < 10)
    (rsp : b[4] = ⟨64, base sp⟩)
    (remaining : b[2] = ⟨64, BitVec.ofNat 64 (591 - roundsBefore j)⟩)
    (window : Writable Extracted.programImage p (base sp) 360) :
    ∃ (c : Registers) (q : Ram), program.runBlock (dialect Extracted.programImage) ⟨.l1091e4, b, p⟩ =
      .jump ⟨.l109246, c, q⟩ ∧ c[4] = ⟨64, base sp⟩ ∧ c[5] = b[5] ∧
      c[2] = ⟨64, memLoad p (base sp + 120) 64⟩ ∧
      c[0] = ⟨64, (memLoad p (base sp + 152) 8).setWidth 64⟩ ∧
      c[6] = ⟨64, memLoad p (base sp + 168) 64⟩ ∧
      c[9] = ⟨64, BitVec.ofNat 64 (count j)⟩ ∧ Controls b c ∧
      RamWriteFrame p q (setupWrites sp) ∧
      memLoad q (base sp + 16) 8 = memLoad p (base sp + 200) 8 ∧
      memLoad q (base sp + 116) 32 = BitVec.ofNat 32 (count j) ∧
      memLoad q (base sp + 352) 64 = BitVec.ofNat 64 (591 - roundsBefore j) := by
  have spWord := congrArg (Value.get 64) rsp
  change b[4].get 64 = base sp at spWord
  have rem64 := congrArg (Value.get 64) remaining
  change b[2].get 64 = BitVec.ofNat 64 (591 - roundsBefore j) at rem64
  have wide : (BitVec.ofNat 32 (count j)).setWidth 64 = BitVec.ofNat 64 (count j) := by
    have := (count_spec hj).2.1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  have chosen := selectCount_eq j hj
  dsimp only [selectCount] at chosen
  have flag : (xorFlags (BitVec.ofNat 32 (count j))).ZF.getD false = false := by
    obtain ⟨positive, limit, _⟩ := count_spec hj
    simp only [xorFlags, Option.getD_some, Bool.eq_false_iff]
    intro he
    have he' := congrArg BitVec.toNat (LawfulBEq.eq_of_beq he)
    have hz : Nat.mod (count j) (2 ^ 32) = 0 := he'
    have modEq : Nat.mod (count j) (2 ^ 32) = count j := Nat.mod_eq_of_lt (by omega)
    rw [modEq] at hz
    exact (Nat.ne_of_gt positive) hz
  refine ⟨?c, ?q, ?run, ?post⟩
  case run =>
    generate_block [spWord, rem64]
    segment_words []
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l1091e4)
    simp only [chosen, wide, flag, Bool.false_eq_true, ↓reduceIte]
    rfl
  case post =>
    refine ⟨rsp, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · intro ⟨i, hi⟩ hh
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
      rcases hh with rfl | rfl | rfl | rfl <;> rfl
    · have bounds := window.readable.low
      simp only [setupWrites, work, List.singleton_append]
      slot_state region
    · segment_words []
    · segment_words []
    · segment_words []

private theorem initializeRows {b c : Registers} {p q : Ram} {sp : Word} {j : Nat}
    (window : Writable Extracted.programImage q (base sp) 360)
    (rsp : c[4] = ⟨64, base sp⟩) (delta : c[5] = ⟨64, (initialWords b p sp).delta⟩)
    (f : c[2] = ⟨64, memLoad p (base sp + 120) 64⟩)
    (signF : c[0] = ⟨64, (memLoad p (base sp + 152) 8).setWidth 64⟩)
    (g : c[6] = ⟨64, memLoad p (base sp + 168) 64⟩)
    (signG : memLoad q (base sp + 16) 8 = memLoad p (base sp + 200) 8)
    (counter : c[9] = ⟨64, BitVec.ofNat 64 (count j)⟩) :
    ∃ (out : Registers), program.runBlock (dialect Extracted.programImage) ⟨.l109246, c, q⟩ =
      .jump ⟨.l1092a0, out, memStore q (base sp + 8) (0 : Word)⟩ ∧
      Controls c out ∧ Inner out (memStore q (base sp + 8) (0 : Word)) sp
        (initialWords b p sp) (count j) := by
  have rspWord : c[4].get 64 = base sp := congrArg (Value.get 64) rsp
  have fWord : c[2].get 64 = memLoad p (base sp + 120) 64 := congrArg (Value.get 64) f
  have gWord : c[6].get 64 = memLoad p (base sp + 168) 64 := congrArg (Value.get 64) g
  have signWord : c[0].get 64 = (memLoad p (base sp + 152) 8).setWidth 64 :=
    congrArg (Value.get 64) signF
  refine ⟨?out, ?run, ?post⟩
  case run =>
    arithmetic_segment using code_l109246 [rspWord, fWord, gWord, signWord, signG]
  case post =>
    refine ⟨?_, ?_⟩
    · intro ⟨i, hi⟩ hh
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
      rcases hh with rfl | rfl | rfl | rfl <;> rfl
    · refine ⟨rsp, delta, ?_, ?_, rfl, rfl, ?_, rfl, counter⟩
      · lifted_word_eq [initialWords, lowWord]
      · lifted_word_eq [initialWords, lowWord]
      · segment_words []
        rfl

variable {a b : Registers} {m p : Ram} {sp : Word} {z : Fin modulus} {w : Vector Word 4}

theorem prepare (h : Entry a m sp z w) {j : Nat} (hj : j < 10) {d e : Int}
    (state : LoopState a m sp z (roundsBefore j) b p d e) :
    ∃ c q s, Reaches .l1091e4 b p .l1092a0 c q ∧ Controls b c ∧
      RamWriteFrame p q (setupWrites sp) ∧ Inner c q sp s (count j) ∧
      memLoad q (base sp + 116) 32 = BitVec.ofNat 32 (count j) ∧
      memLoad q (base sp + 352) 64 = BitVec.ofNat 64 (591 - roundsBefore j) ∧
      SafeGcd.LowBitsEq 63 (SafeGcd.Batch.state s) (Core.model z (roundsBefore j)) ∧
      SafeGcd.Batch.matrix s = SafeGcd.Matrix.identity := by
  have lo := h.low
  have hi := h.high
  have window : Writable Extracted.programImage p (base sp) 360 :=
    (h.stack.of_frame state.frame).sub (by unfold base; bv_omega) (by unfold base; bv_omega)
  obtain ⟨c, q, head, rsp, delta, f, signF, g, counter, kept, frame, signG, shift, remaining⟩ :=
    loadInputs hj state.rsp state.remaining window
  have delta' : c[5] = ⟨64, (initialWords b p sp).delta⟩ := by
    rw [delta]
    change b[5] = ⟨64, b[5].get 64⟩
    rw [state.delta]
    simp only [Value.get, BitVec.setWidth_eq]
  obtain ⟨out, tail, kept', inner⟩ :=
    initializeRows (window.of_frame frame) rsp delta' f signF g signG counter
  refine ⟨out, _, initialWords b p sp, ?_, fun i hi => (kept' i hi).trans (kept i hi),
    ?_, inner, ?_, ?_, initialWords_low state (Nat.min_le_right _ _), rfl⟩
  · refine .step (b := ⟨⟨.l109246, c, q⟩, []⟩) ?_ (.step ?_ (.refl _))
    · change program.step _ _ = _
      simp only [Program.step, head, Transfer.next]
    · change program.step _ _ = _
      simp only [Program.step, tail, Transfer.next]
  · simp only [setupWrites, work, List.singleton_append] at frame ⊢
    have bounds := window.readable.low
    slot_state region
  · segment_words [shift]
  · segment_words [remaining]

end K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch
