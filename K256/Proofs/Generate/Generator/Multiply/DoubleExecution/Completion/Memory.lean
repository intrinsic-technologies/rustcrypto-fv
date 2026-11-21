import K256.Proofs.Generate.Generator.Multiply.DoubleExecution.Replay.Layout

namespace K256.Proofs.Generate.Generator.Multiply.DoubleReplay

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Tactic
open Common.Point Common.Field Common.Point.DoubleWords.Replay
open K256.Proofs.Sec1.Affine.Uncompressed

theorem finishMemory {m : Ram} {p : PointWords} {yy zz : Limbs} {sp : Word} {count : BitVec 32}
    (mem : memory p yy zz sp count 3583 m) :
    let out := memStore (memStore m (sp + 0x168) (w1538 p yy zz sp)) (sp + 0x170) (w1536 p yy zz sp)
    WordsAt out (sp + 0x128) 64 (output p yy zz sp).x ∧
    WordsAt out (sp + 0x150) 64 (output p yy zz sp).y ∧
    WordsAt out (sp + 0x178) 64 (output p yy zz sp).z := by
  simp only [memory, memoryAtoms, Atom.All, Atom.Holds] at mem
  obtain ⟨win, x0, x1, x2, x3, x4, y0, y1, y2, z0, z1, z2, z3, z4, _⟩ := mem
  have low := win.readable.low
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  all_goals
    intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with
      rfl | rfl | rfl | rfl | rfl
    all_goals
      dsimp only [output]
      simp only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.add_assoc,
        BitVec.reduceAdd, BitVec.add_zero]
      segment_words [x0, x1, x2, x3, x4, y0, y1, y2, z0, z1, z2, z3, z4] <;> rfl

end K256.Proofs.Generate.Generator.Multiply.DoubleReplay
