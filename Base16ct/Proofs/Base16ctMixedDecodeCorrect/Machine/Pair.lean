import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Pair.High
import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Pair.Low

namespace Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine

open Base16ct.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs

theorem pair_advances [Bindings] {s : RamState} {boundary : ReturnBoundary} {hi lo : UInt8}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hOutside : OutsideMixed boundary.rip) (hRip : s.RIP = 0x1001f0)
    (hHighReadable : MemReadable s ((Operand.reg 7 : Operand 64).read s +
      (Operand.reg 0 : Operand 64).read s * 2) 1)
    (hHighByte : (Operand.mem ((Operand.reg 7 : Operand 64).read s +
      (Operand.reg 0 : Operand 64).read s * 2) : Operand 8).read s = hi.toBitVec)
    (hLowReadable : MemReadable s ((Operand.reg 7 : Operand 64).read s +
      (Operand.reg 0 : Operand 64).read s * 2 + 1) 1)
    (hLowByte : (Operand.mem ((Operand.reg 7 : Operand 64).read s +
      (Operand.reg 0 : Operand 64).read s * 2 + 1) : Operand 8).read s = lo.toBitVec) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = 0x1002d8 ∧
      (Operand.reg 3 : Operand 64).read t = (pairWord hi lo).zeroExtend 64 ∧
      AgreesExcept [.reg 5, .reg 14, .reg 8, .reg 10, .reg 11, .reg 3, .flags, .rip] s t := by
  obtain ⟨highFuel, u, hHighAdvance, hReadyU, hCodeU, hRipU, hHighU, hFrameU⟩ :=
    high_pair_advances hReady hCode hOutside hRip hHighReadable hHighByte
  have hRdi := hFrameU.read (n := 64) (r := 7) (by simp)
  have hRax := hFrameU.read (n := 64) (r := 0) (by simp)
  have hMemory : u.external = s.external :=
    hFrameU.external (by simp [Component.Covers])
  have hReadU : MemReadable u ((Operand.reg 7 : Operand 64).read u +
      (Operand.reg 0 : Operand 64).read u * 2 + 1) 1 := by
    rw [hRdi, hRax]
    exact hLowReadable.of_external_eq hMemory
  have hByteU : (Operand.mem ((Operand.reg 7 : Operand 64).read u +
      (Operand.reg 0 : Operand 64).read u * 2 + 1) : Operand 8).read u = lo.toBitVec := by
    rw [hRdi, hRax]
    simpa only [Operand.read, hMemory] using hLowByte
  obtain ⟨lowFuel, t, hLowAdvance, hReadyT, hCodeT, hRipT, hPairT, hFrameT⟩ :=
    low_pair_advances hReadyU hCodeU hOutside hRipU hReadU hByteU hHighU
  exact ⟨highFuel + lowFuel, t, hHighAdvance.trans hLowAdvance, hReadyT, hCodeT,
    hRipT, hPairT, (hFrameU.trans hFrameT).mono (by simp)⟩

end Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine
