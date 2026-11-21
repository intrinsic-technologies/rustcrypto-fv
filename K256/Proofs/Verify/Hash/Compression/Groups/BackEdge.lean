import K256.Proofs.Verify.Hash.Compression.Groups.Boundaries
import K256.Proofs.Verify.Hash.Compression.Interface
import K256.Proofs.Verify.LIR.Defs18

namespace K256.Proofs.Verify.Hash.Compression
open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  K256.Proofs.Sec1.Affine.Uncompressed
open Values

private theorem backEdgeBranch (code : CodeMap) (scope : CFG.Values Value 6585)
    (m : Ram) (arguments : Vector (Fin 6585) Reg.count) (next limit : BitVec 64)
    (test : scope[6584].truth = (next != limit)) :
    (Block.terminate (.condBr (Fin.last 6584) ⟨Label.l121930, arguments⟩
      ⟨Label.l1240c4, arguments⟩) : Block Lift.Op Label signature Reg.count 6585).eval
      (dialect code) scope m =
      .jump ⟨if next ≠ limit then .l121930 else .l1240c4, scope.select arguments, m⟩ := by
  simp only [Block.eval, Terminator.eval, dialect_truth, Edge.eval]
  have branch : (scope[6584].truth = true) ↔ next ≠ limit := by
    rw [test, bne_iff_ne]
  let jump (label : Label) : Transfer Value Ram Label signature Reg.count :=
    .jump ⟨label, scope.select arguments, m⟩
  change (if scope[6584].truth = true then jump .l121930 else jump .l1240c4) =
    jump (if next ≠ limit then .l121930 else .l1240c4)
  by_cases h : next ≠ limit
  · rw [ite_eq_left (branch.mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun taken => h (branch.mp taken)), ite_eq_right h]

theorem backEdge (code : CodeMap) (a : CFG.Values Value 6562) (entry : CFG.Values Value Reg.count)
    (m : Ram) (ctx : ValueContext) (s : Compression.Values) (limit : BitVec 64)
    (stack : Readable m ctx.stackPointer 336)
    (slots : StackMatches ctx.stackPointer s m)
    (limitWord : memLoad m (ctx.stackPointer + 200) 64 = limit)
    (sp : s.regs 4 = ctx.stackPointer) (ip : s.regs 6 = ctx.inputPointer)
    (regs : registersAgree a s registers166) (saved : preservedAt a entry) :
    ∃ out : CFG.Values Value Reg.count,
      b_l121930_166.eval (dialect code) a m =
        .jump ⟨if ctx.inputPointer + 64 ≠ limit then .l121930 else .l1240c4, out, m⟩ ∧
      out[4].get 64 = ctx.stackPointer ∧ out[6].get 64 = ctx.inputPointer + 64 ∧
      (∀ i : Fin 8, out[hashRegisters[i]].get 32 =
        ((run ctx group166 s).regs (BitVec.ofNat 5 hashRegisters[i].val)).setWidth 32) ∧
      preservedAt out entry := by
  simp only [registers166, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, _, r4, r5, r6, r7, _, r9, r10, r11, _, _, r14, _, _⟩ := regs
  have rsp := r4.trans sp
  have rsi := r6.trans ip
  refine ⟨?_, ?step, ?rsp, ?rsi, ?words, ?saved⟩
  case step =>
    arithmetic_prefix [BitVec.add_zero, rsp, rsi, limitWord]
    iterate 6
      refine Eq.trans (ite_eq_left ?_) ?_
      slot_guard using code_l121930_166
    refine backEdgeBranch _ _ _ _ _ _ ?_
    simp only [↓arithmeticRead, Value.truth_ofBool]
    segment_words [limitWord] <;> rfl
  case rsp =>
    simpa only [CFG.Values.getElem_select, Fin.getElem_fin, ↓arithmeticRead] using rsp
  case rsi =>
    simp only [CFG.Values.getElem_select, Fin.getElem_fin]
    simp only [↓arithmeticRead, cfg_eval]
  case words =>
    intro i
    have cases8 : ∀ j : Fin 8, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by decide
    rcases cases8 i with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp only [CFG.Values.getElem_select, Fin.getElem_fin]
      simp only [hashRegisters, ↓arithmeticRead, arithmeticIndex, group166, Values.Program.part51,
        Values.Program.part52, List.take, List.drop, List.cons_append, List.nil_append, run,
        Values.Op.eval, Source.read32, read32, writeReg, Binary.apply, BitVec.reduceEq,
        ↓reduceIte, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), cfg_eval]
    all_goals segment_words [← r0, ← r1, ← r2, ← r5, ← r7, ← r9, ← r10, ← r11, ← r14,
      ← (slots 280 (by decide) (by decide)), ← (slots 240 (by decide) (by decide)),
      ← (slots 256 (by decide) (by decide)), ← (slots 272 (by decide) (by decide)),
      ← (slots 188 (by decide) (by decide))]
    all_goals exact (BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)).symm
  case saved =>
    intro i hi ho hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with h | h | h | h <;> subst i <;>
      simp only [CFG.Values.getElem_select, Fin.getElem_fin, ↓arithmeticRead] <;>
      exact saved _ (by decide) (by decide) (by decide)

end K256.Proofs.Verify.Hash.Compression
