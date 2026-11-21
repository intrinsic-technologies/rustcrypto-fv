import K256.Proofs.Generate.Generator.Multiply.DoubleExecution.Completion.Iteration
import K256.Proofs.Generate.Generator.Multiply.DoubleExecution.Segments.A
import K256.Proofs.Generate.Generator.Multiply.DoubleExecution.Segments.B
import K256.Proofs.Generate.Generator.Multiply.DoubleExecution.Squares

namespace K256.Proofs.Generate.Generator.Multiply

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

theorem fourDoubles {fr : Activation} {a : Registers} {m : Ram} {p : Projective}
    (atoms : Atom.All Extracted.programImage a m (Fn11c880.frameAt .l11d810 fr))
    (widths : ParseSignature.ArgumentWidths a)
    (savedWidths : SavedWidths a)
    (rounds : a[1].get 64 = 4) (mask : a[5].get 64 = 0x1000003d10)
    (temp : a[12].get 64 = fr.rsp - 0xcb8 + 0x490)
    (savedMask : memLoad m (fr.rsp - 0xcb8 + 0x1c8) 64 = 0xfffffffffff8)
    (acc : p.Stored m (fr.rsp - 0xb90)) :
    ∃ b n, Reaches .l11d810 a m .l11f5e5 b n ∧
      Atom.All Extracted.programImage b n (Fn11c880.frameAt .l11f5e5 fr) ∧
      ParseSignature.ArgumentWidths b ∧ SavedWidths b ∧ p.double.double.double.double.Stored n (fr.rsp - 0xb90) ∧
      RamWriteFrame m n (doubleWrites (fr.rsp - 0xcb8)) := by
  have arithmetic : DoubleArithmetic := doubleArithmetic_of_segments fun rsp rbp =>
    @Common.Point.BodySegment.trans _ _ _ _ _ _ _ _ _ _
      (DoubleReplay.segmentsA rsp rbp) (DoubleReplay.segmentsB rsp rbp)
  have state : DoublesState fr p 4 a m :=
    ⟨atoms, widths, savedWidths, rounds, mask, temp, savedMask, acc⟩
  obtain ⟨b, n, run, final, frame⟩ :=
    repeatDoubles (doubleStep_of_arithmetic prepareSquares arithmetic) (by decide) state
  exact ⟨b, n, run, final.atoms, final.widths, final.savedWidths, final.acc, frame⟩

end K256.Proofs.Generate.Generator.Multiply
