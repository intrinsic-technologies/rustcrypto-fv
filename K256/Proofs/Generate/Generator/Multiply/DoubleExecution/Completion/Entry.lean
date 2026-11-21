import K256.Proofs.Generate.Generator.Multiply.DoubleExecution.Replay.Layout
import K256.Proofs.Generate.Generator.Multiply.DoubleExecution.SquareInterface

namespace K256.Proofs.Generate.Generator.Multiply.DoubleReplay

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Tactic
open Common.Point Common.Field Common.Point.DoubleWords.Replay

private theorem read_at {m : Ram} {sp : Word} {w : Limbs} {off : Nat}
    (h : WordsAt m (sp + BitVec.ofNat 64 off) 64 w) (i : Fin 5) :
    memLoad m (sp + BitVec.ofNat 64 (off + 8 * i.val)) 64 = w[i] := by
  simpa only [wordAddr, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.reduceDiv, Fin.getElem_fin] using h i i.isLt

theorem entryMemory {m : Ram} {sp : Word} {p : PointWords} {count : BitVec 32}
    (win : Writable Extracted.programImage m sp 0x878)
    (wx : WordsAt m (sp + 0x128) 64 p.x) (wy : WordsAt m (sp + 0x150) 64 p.y)
    (wz : WordsAt m (sp + 0x178) 64 p.z)
    (copies : ∀ i : Fin 5, memLoad m (sp + squareCopies[i]) 64 = (squareWords p.y)[i])
    (zs : WordsAt m (sp + 0x490) 64 (squareWords p.z))
    (counter : memLoad m (sp + 0x1bc) 32 = count)
    (mask : memLoad m (sp + 0x1c8) 64 = 0xfffffffffff8) :
    memory p (squareWords p.y) (squareWords p.z) sp count 53 m := by
  refine ⟨win, copies 3, copies 4, copies 1, copies 2, copies 0,
    read_at wx 0, read_at wx 1, read_at wx 2, read_at wx 3, read_at wx 4,
    read_at wy 0, read_at wy 1, read_at wy 2, read_at wy 3, read_at wy 4,
    read_at wz 0, read_at wz 1, read_at wz 2, read_at wz 3, read_at wz 4, counter, mask,
    read_at zs 0, read_at zs 1, read_at zs 2, read_at zs 3, read_at zs 4, trivial⟩

end K256.Proofs.Generate.Generator.Multiply.DoubleReplay
