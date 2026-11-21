import K256.Proofs.Generate.Generator.Multiply.Split.Multiplication.Reduction.Segment0
import K256.Proofs.Generate.Generator.Multiply.Split.Multiplication.Reduction.SegmentsLow
import K256.Proofs.Generate.Generator.Multiply.Split.Multiplication.Reduction.SegmentsHigh

namespace K256.Proofs.Generate.Generator.Multiply.Split.Reduction.Replay

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Tactic
  K256.Proofs.Common.Tactic.Replay K256.Proofs.Common.Point
  K256.Proofs.Sec1.Affine.Uncompressed

theorem allSegments {c : Registers} {fr : Activation} {w : Vector (BitVec 64) 8}
    (rsp : c[4] = ⟨64, fr.rsp - 120⟩) (rsi : c[6] = ⟨64, fr.rsi⟩)
    (constant : c[9] = ⟨64, 0x402da1732fc9bebf⟩)
    (lo : 129 ≤ fr.rsp.toNat) (hi : fr.rsp.toNat + 8 ≤ fr.rsi.toNat)
    (upper : fr.rsi.toNat + 64 ≤ 2^64) : Segment c fr w b_l11b5ba barrier := by
  refine BodySegment.trans (a := b_l11b5ba) (b := b_l11b5ba_1) (c := barrier)
    (code := Extracted.programImage) (graph := values c fr w) (regions := writeRegions fr)
    (memory := fun n m => Atom.All Extracted.programImage (Vector.replicate _ ⟨1, 0⟩) m (memoryAtoms fr w n))
    (segment0 (w := w) rsp rsi constant lo hi upper) ?_
  refine BodySegment.trans (a := b_l11b5ba_1) (b := b_l11b5ba_2) (c := barrier)
    (code := Extracted.programImage) (graph := values c fr w) (regions := writeRegions fr)
    (memory := fun n m => Atom.All Extracted.programImage (Vector.replicate _ ⟨1, 0⟩) m (memoryAtoms fr w n))
    (segment1 (w := w) rsi) ?_
  refine BodySegment.trans (a := b_l11b5ba_2) (b := b_l11b5ba_3) (c := barrier)
    (code := Extracted.programImage) (graph := values c fr w) (regions := writeRegions fr)
    (memory := fun n m => Atom.All Extracted.programImage (Vector.replicate _ ⟨1, 0⟩) m (memoryAtoms fr w n))
    (segment2 (w := w) rsi) ?_
  refine BodySegment.trans (a := b_l11b5ba_3) (b := b_l11b5ba_4) (c := barrier)
    (code := Extracted.programImage) (graph := values c fr w) (regions := writeRegions fr)
    (memory := fun n m => Atom.All Extracted.programImage (Vector.replicate _ ⟨1, 0⟩) m (memoryAtoms fr w n))
    (segment3 (w := w) rsp lo hi upper) ?_
  refine BodySegment.trans (a := b_l11b5ba_4) (b := b_l11b5ba_5) (c := barrier)
    (code := Extracted.programImage) (graph := values c fr w) (regions := writeRegions fr)
    (memory := fun n m => Atom.All Extracted.programImage (Vector.replicate _ ⟨1, 0⟩) m (memoryAtoms fr w n))
    (segment4 (w := w) rsp lo hi upper) ?_
  refine BodySegment.trans (a := b_l11b5ba_5) (b := b_l11b5ba_6) (c := barrier)
    (code := Extracted.programImage) (graph := values c fr w) (regions := writeRegions fr)
    (memory := fun n m => Atom.All Extracted.programImage (Vector.replicate _ ⟨1, 0⟩) m (memoryAtoms fr w n))
    (segment5 (w := w) rsp rsi constant lo hi upper) ?_
  refine BodySegment.trans (a := b_l11b5ba_6) (b := b_l11b5ba_7) (c := barrier)
    (code := Extracted.programImage) (graph := values c fr w) (regions := writeRegions fr)
    (memory := fun n m => Atom.All Extracted.programImage (Vector.replicate _ ⟨1, 0⟩) m (memoryAtoms fr w n))
    (segment6 (w := w) rsp rsi constant lo hi upper) ?_
  refine BodySegment.trans (a := b_l11b5ba_7) (b := b_l11b5ba_8) (c := barrier)
    (code := Extracted.programImage) (graph := values c fr w) (regions := writeRegions fr)
    (memory := fun n m => Atom.All Extracted.programImage (Vector.replicate _ ⟨1, 0⟩) m (memoryAtoms fr w n))
    (segment7 (w := w) rsp rsi constant lo hi upper) ?_
  refine BodySegment.trans (a := b_l11b5ba_8) (b := b_l11b5ba_9) (c := barrier)
    (code := Extracted.programImage) (graph := values c fr w) (regions := writeRegions fr)
    (memory := fun n m => Atom.All Extracted.programImage (Vector.replicate _ ⟨1, 0⟩) m (memoryAtoms fr w n))
    (segment8 (w := w) rsp rsi constant lo hi upper) ?_
  exact segment9 rsp rsi constant lo hi upper

theorem replayBarrier {c b : Registers} {fr : Activation} {w : Vector (BitVec 64) 8} {m n : Ram}
    (segments : Segment c fr w b_l11b5ba barrier)
    (stack : Writable Extracted.programImage m (fr.rsp - 129) 129)
    (input : Readable m fr.rsi 64) (words : WordsAt m fr.rsi 64 w)
    (slot₂ : memLoad m (fr.rsp - 72) 64 = 0xfffffffffffffffe)
    (slot₃ : memLoad m (fr.rsp - 96) 64 = 0xffffffffffffffff)
    (slot₁ : memLoad m (fr.rsp - 80) 64 = 0xbaaedce6af48a03b)
    (run : program.runBlock (dialect Extracted.programImage) ⟨.l11b5ba,c,m⟩ =
       .call ⟨.l127d50, b,n⟩ (callFrame .l11b864 0x11b864)) :
    ∃ last : Values Value 483, ∃ final : Ram,
      ValuesMatch (values c fr w) last ∧
      Atom.All Extracted.programImage (Vector.replicate _ ⟨1, 0⟩) final (memoryAtoms fr w 483) ∧
      barrier.eval (dialect Extracted.programImage) last final =
        .call ⟨.l127d50,b,n⟩ (callFrame .l11b864 0x11b864) := by
  have hv : ValuesMatch (values c fr w) c := by
    intro i
    simp only [values, dite_eq_left i.isLt, Fin.getElem_fin]
  have hm : Atom.All Extracted.programImage (Vector.replicate _ ⟨1, 0⟩) m (memoryAtoms fr w 53) := by
    simp only [memoryAtoms, Atom.All, Atom.Holds]
    refine ⟨stack,input,?_,words 1 (by decide),words 2 (by decide),words 3 (by decide),
      words 4 (by decide),words 5 (by decide),words 6 (by decide),words 7 (by decide),
      slot₃,slot₁,slot₂,trivial⟩
    simpa only [wordAddr, Nat.mul_zero, BitVec.add_zero] using words 0 (by decide)
  obtain ⟨last,final,eval,lastValues,lastMemory,_⟩ := segments hv hm
  exact ⟨last, final, lastValues, lastMemory, eval.symm.trans run⟩

end K256.Proofs.Generate.Generator.Multiply.Split.Reduction.Replay
