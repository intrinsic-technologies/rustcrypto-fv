import K256.Proofs.Ecdh.Multiply.Endomorphism.Words
import K256.Proofs.Generate.Generator.Multiply.Prepare.Frame
import K256.Proofs.Generate.LIR.Fn10e010.Frame
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Generate.Generator.Multiply.Prepare.Endomorphism
open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Field

local macro "coordinate_word " h:ident i:num : term =>
  `(by simpa only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
      BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using $h $i (by decide))

open Lean Elab Tactic K256.Proofs.Common.Field.Multiply

local elab "read_product_words " h:ident " products " prod:ident " accumulators " "[" stages:ident,* "]" : tactic => do
  let mut foldRules : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) := #[]
  for stage in stages.getElems do
    for (proj, suffix) in [(``Prod.fst, "Lo"), (``Prod.snd, "Hi")] do
      let name := mkIdent (stage.getId.appendAfter suffix)
      let part ← `(term| $(mkIdent proj):ident $stage)
      evalTactic (← `(tactic| have $name : $part = $part := rfl))
      evalTactic (← `(tactic| conv at $name =>
        rhs
        simp only [$stage:ident, $prod:ident, betaLimbs, wideMul, wideAdd, wideAddRev,
          ofWord, combine56, low52, high52, Fin.getElem_fin,
          (show (0 : Fin 5).val = 0 from rfl), (show (1 : Fin 5).val = 1 from rfl),
          (show (2 : Fin 5).val = 2 from rfl), (show (3 : Fin 5).val = 3 from rfl),
          (show (4 : Fin 5).val = 4 from rfl), Vector.getElem_mk, List.getElem_toArray,
          List.getElem_cons_zero, List.getElem_cons_succ,
          (show ∀ w : Word, w + 0 = w from BitVec.add_zero),
          (show ∀ w : Word, 0 + w = w from BitVec.zero_add)]))
      foldRules := foldRules.push (← `(Lean.Parser.Tactic.simpLemma| ← $name:ident))
  evalTactic (← `(tactic| (change WordsAt _ _ 64 _; lifted_word_reads []; all_goals
    (rw [$h:ident]; simp only [$foldRules,*]; all_goals rfl))))

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem runPeer {fr : Activation} {a : Registers} {m : Ram}
    (entry : Atom.All Extracted.programImage a m (Fn10e010.frameAt .l10e010 fr))
    (src : Readable m fr.rsi 120) (dst : Writable Extracted.programImage m fr.rdi 120)
    (aboveSrc : fr.rsp.toNat + 8 ≤ fr.rsi.toNat) (aboveDst : fr.rsp.toNat + 8 ≤ fr.rdi.toNat)
    (apart : fr.rsi.toNat + 120 ≤ fr.rdi.toNat ∨ fr.rdi.toNat + 120 ≤ fr.rsi.toNat)
    {x y z : Limbs} (wx : WordsAt m fr.rsi 64 x)
    (wy : WordsAt m (fr.rsi + 40) 64 y) (wz : WordsAt m (fr.rsi + 80) 64 z) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l10e010, a, m⟩, []⟩ out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧ Atom.All Extracted.programImage out.values out.store (Fn10e010.doneAt fr) ∧
      ParseSignature.ArgumentWidths out.values ∧
      RamWriteFrame m out.store [⟨fr.rsp.toNat - 128, 128⟩,⟨fr.rdi.toNat, 120⟩] ∧
      WordsAt out.store fr.rdi 64 (betaMulWords x) ∧ WordsAt out.store (fr.rdi + 40) 64 y ∧
      WordsAt out.store (fr.rdi + 80) 64 z := by
  simp only [Fn10e010.frameAt, Fn10e010.frameAtG0, Atom.All, Atom.Holds] at entry
  obtain ⟨sp, df, cx, dx, bx, bp, si, di, r8, r9, r12, r13, r14, r15, mx, ftw, fcw,
    retRead, ret, retLow, win, room, align, _⟩ := entry
  have sl := retRead.low
  have xl := src.low
  have dl := dst.readable.low
  have depth : 128 ≤ fr.rsp.toNat := by omega
  have v4 : a[4].get 64 = fr.rsp := congrArg (Value.get 64) sp
  have v3 : a[3].get 64 = fr.rbx := congrArg (Value.get 64) bx
  have v5 : a[5].get 64 = fr.rbp := congrArg (Value.get 64) bp
  have v6 : a[6].get 64 = fr.rsi := congrArg (Value.get 64) si
  have v7 : a[7].get 64 = fr.rdi := congrArg (Value.get 64) di
  have v12 : a[12].get 64 = fr.r12 := congrArg (Value.get 64) r12
  have v13 : a[13].get 64 = fr.r13 := congrArg (Value.get 64) r13
  have v14 : a[14].get 64 = fr.r14 := congrArg (Value.get 64) r14
  have v15 : a[15].get 64 = fr.r15 := congrArg (Value.get 64) r15
  have x0 : memLoad m fr.rsi 64 = x[0] := coordinate_word wx 0
  have x1 : memLoad m (fr.rsi + 8) 64 = x[1] := coordinate_word wx 1
  have x2 : memLoad m (fr.rsi + 16) 64 = x[2] := coordinate_word wx 2
  have x3 : memLoad m (fr.rsi + 24) 64 = x[3] := coordinate_word wx 3
  have x4 : memLoad m (fr.rsi + 32) 64 = x[4] := coordinate_word wx 4
  have x5 : memLoad m (fr.rsi + 40) 64 = y[0] := coordinate_word wy 0
  have x6 : memLoad m (fr.rsi + 48) 64 = y[1] := coordinate_word wy 1
  have x7 : memLoad m (fr.rsi + 56) 64 = y[2] := coordinate_word wy 2
  have x8 : memLoad m (fr.rsi + 64) 64 = y[3] := coordinate_word wy 3
  have x9 : memLoad m (fr.rsi + 72) 64 = y[4] := coordinate_word wy 4
  have x10 : memLoad m (fr.rsi + 80) 64 = z[0] := coordinate_word wz 0
  have x11 : memLoad m (fr.rsi + 88) 64 = z[1] := coordinate_word wz 1
  have x12 : memLoad m (fr.rsi + 96) 64 = z[2] := coordinate_word wz 2
  have x13 : memLoad m (fr.rsi + 104) 64 = z[3] := coordinate_word wz 3
  have x14 : memLoad m (fr.rsi + 112) 64 = z[4] := coordinate_word wz 4
  refine ⟨?out, Program.Exec.done ?run, ?tag, ?done_, ?widths, ?frame, ?words⟩
  case run =>
    unfold Program.step
    generate_block [v3, v4, v5, v6, v7, v12, v13, v14, v15, BitVec.add_zero,
      Lift.reduceSubOffset, Lift.reduceAddOffset, Lift.reduceAddNeg, Lift.reduceSubNeg,
      BitVec.reduceAdd, BitVec.reduceSub]
    segment_words [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
      ret, retLow, and_true]
    repeat' (refine Eq.trans (congrArg _ (ite_eq_left ?_)) ?_; slot_guard using code_l10e010)
    rfl
  case tag => rfl
  case done_ =>
    exact ⟨rfl, df, rfl, rfl, rfl, rfl, rfl, rfl, mx, ftw, fcw, trivial⟩
  case widths =>
    intro ⟨i, hi⟩ hm
    simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  case frame =>
    dsimp only
    repeat' refine RamWriteFrame.memStore ?_ _ ?_
    exact RamWriteFrame.refl _ _
    all_goals simp only [InRegions, InRegion, List.mem_cons, List.not_mem_nil, or_false,
      exists_eq_or_imp, exists_eq_left] <;> bv_omega
  case words =>
    dsimp only
    refine ⟨?_, ?_, ?_⟩
    · have resultEq : betaMulWords x = betaMulWords x := rfl
      conv at resultEq => rhs; unfold betaMulWords
      extract_lets prod c₈ c₃ d₃ c₄ d₄ c₅ d₅ r₀ c₆ d₆ c₁ r₁ c₇ d₇ c₂ r₂ r₃ at resultEq
      read_product_words resultEq products prod accumulators
        [c₈, c₃, d₃, c₄, d₄, c₅, d₅, r₀, c₆, d₆, c₁, r₁, c₇, d₇, c₂, r₂, r₃]
    · lifted_word_reads [] <;> rfl
    · lifted_word_reads [] <;> rfl

end K256.Proofs.Generate.Generator.Multiply.Prepare.Endomorphism
