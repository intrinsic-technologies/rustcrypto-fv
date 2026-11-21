import Md5.Proofs.Block.Rounds.Machine

namespace Md5.Proofs.Block

open Md5.Spec Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs

theorem compression_rounds [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {stack input : BitVec 64} {buffer : Standards.RFC.MD5.Buffer} {words : Vector (BitVec 32) 16}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hEntry : s.RIP = 0x101be0) (hData : LoopData stack input buffer words s)
    (hBoundary : OutsideCompression boundary.rip) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ t.RIP = 0x102427 ∧
      LoopData stack input (Standards.RFC.MD5.processBlock buffer words) words t ∧
      AgreesExcept (loopComponents stack) s t := by
  have hInitial : Rounds.Invariant0 buffer words buffer
      (Rounds.readMachineWord stack input s) := by
    exact ⟨rfl, rfl, rfl, rfl, hData.registers.2.2.2, hData.registers.1,
      hData.registers.2.2.1, hData.registers.2.1,
      hData.inputWords 0, hData.inputWords 1, hData.inputWords 2, hData.inputWords 3,
      hData.inputWords 4, hData.inputWords 5, hData.inputWords 6, hData.inputWords 7,
      hData.inputWords 8, hData.inputWords 9, hData.inputWords 10, hData.inputWords 11,
      hData.inputWords 12, hData.inputWords 13, hData.inputWords 14, hData.inputWords 15⟩
  have hRun := Rounds.machine_rounds
  unfold Rounds.RunWords at hRun
  obtain ⟨fuel, t, finalBuffer, hAdvance, hReady', hCode', hExit, hData', hModel, hFrame⟩ :=
    hRun hReady hCode hEntry hData hBoundary
      (Rounds.MachineWords.self stack input s)
  have hOutput := Rounds.wordProgram_processBlock buffer words _ hInitial
  have hRegisters : LoopRegisters (Standards.RFC.MD5.processBlock buffer words) t := by
    rw [← hOutput]
    exact ⟨hModel (.reg 1) (by decide), hModel (.reg 8) (by decide),
      hModel (.reg 2) (by decide), hModel (.reg 0) (by decide)⟩
  exact ⟨fuel, t, hAdvance, hReady', hCode', hExit,
    ⟨hRegisters, hData'.stackPointer, hData'.inputPointer, hData'.frame, hData'.readable,
      hData'.inputWords, hData'.apart, hData'.code⟩, hFrame⟩

end Md5.Proofs.Block
