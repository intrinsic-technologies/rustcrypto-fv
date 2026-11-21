import Md5.Proofs.Block.Rounds.Frame
import Md5.Proofs.Block.Rounds.Run
import Md5.Proofs.Block.Rounds.Model

namespace Md5.Proofs.Block.Rounds

open Md5.Spec Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs

structure InstructionExecution [Bindings] (start finish : BitVec 64)
    (effect : RamState → Effect) where
  pre : RamState → Prop
  code : CodeMap
  step : StepEffect pre code effect
  present : ∀ {s}, CodeIn Extracted.programImage s → CodeIn code s
  enabled : ∀ {s stack input buffer words}, LoopData stack input buffer words s →
    s.RIP = start → pre s
  next : ∀ s, (effect s).rip = finish
  low : 0x101ba0 ≤ finish.toNat
  high : finish.toNat < 0x102459

variable [Bindings] {start finish : BitVec 64} {effect : RamState → Effect}
  {instruction : WordInstruction}

theorem InstructionExecution.run (h : InstructionExecution start finish effect)
    (hFrame : ∀ {s t stack input buffer words}, LoopData stack input buffer words s →
      (effect s).Holds s t → AgreesExcept (loopComponents stack) s t)
    (hModel : ∀ {s t stack input buffer words model}, LoopData stack input buffer words s →
      (effect s).Holds s t → MachineWords stack input s model →
      MachineWords stack input t (instruction.execute model)) :
    RunWords start finish [instruction] := by
  unfold RunWords
  intro s boundary stack input buffer words model hReady hCode hEntry hData hBoundary hm
  obtain ⟨t, hAdvance, hReady', he⟩ := h.step.advances hReady (h.present hCode)
    (h.enabled hData hEntry) (by
      rw [h.next]
      exact outsideCompression_ne hBoundary h.low h.high)
  have ha := hFrame hData he
  refine ⟨1, t, _, hAdvance, hReady', hData.codeIn_of_agrees ha hCode,
    he.rip.trans (h.next s), hData.of_agrees ha, ?_, ha⟩
  simpa only [executeWords_cons, executeWords_nil] using hModel hData he hm

theorem InstructionExecution.run_reg (h : InstructionExecution start finish effect)
    {dst : Nat} {value : RamState → BitVec 64}
    (hWrite : ∀ s, (effect s).writes = [⟨.reg (BitVec.ofNat 5 dst), value s⟩])
    (hBound : dst < 16) (hSp : dst ≠ 4) (hSi : dst ≠ 6) (hValid : instruction.valid)
    (hAction : ∀ {s stack input buffer words}, LoopData stack input buffer words s →
      instruction.execute (readMachineWord stack input s) =
        (readMachineWord stack input s).write (.reg dst) ((value s).setWidth 32)) :
    RunWords start finish [instruction] := by
  apply h.run
  · intro s t stack input buffer words _ he
    exact effect_agrees_loop_reg he (hWrite s) hBound hSp hSi
  · intro s t stack input buffer words model hd he hm
    exact hm.of_reg_effect he (hWrite s) hBound hValid (hAction hd)

theorem InstructionExecution.run_stack32 (h : InstructionExecution start finish effect)
    {dst : Nat} {value : RamState → BitVec 32}
    (hWrite : ∀ {s stack input buffer words}, LoopData stack input buffer words s →
      (effect s).writes = [⟨.mem (stack + BitVec.ofNat 64 dst), value s⟩])
    (hDst : dst ∈ scratchOffsets)
    (hBound : dst + 4 ≤ 96 ∨ 112 ≤ dst ∧ dst + 4 ≤ 136) (hValid : instruction.valid)
    (hAction : ∀ {s stack input buffer words}, LoopData stack input buffer words s →
      instruction.execute (readMachineWord stack input s) =
        (readMachineWord stack input s).write (.stack dst) (value s)) :
    RunWords start finish [instruction] := by
  apply h.run
  · intro s t stack input buffer words hd he
    exact effect_agrees_loop_stack he (hWrite hd) hBound
  · intro s t stack input buffer words model hd he hm
    exact hm.of_stack32_effect he (hWrite hd) hDst hd.apart hValid (hAction hd)

theorem InstructionExecution.run_stack64 (h : InstructionExecution start finish effect)
    {dst : Nat} {value : RamState → BitVec 64}
    (hWrite : ∀ {s stack input buffer words}, LoopData stack input buffer words s →
      (effect s).writes = [⟨.mem (stack + BitVec.ofNat 64 dst), value s⟩])
    (hDst : dst ∈ scratchWideOffsets)
    (hBound : dst + 8 ≤ 96 ∨ 112 ≤ dst ∧ dst + 8 ≤ 136) (hValid : instruction.valid)
    (hAction : ∀ {s stack input buffer words}, LoopData stack input buffer words s →
      instruction.execute (readMachineWord stack input s) =
        (readMachineWord stack input s).write (.stack dst) ((value s).setWidth 32)) :
    RunWords start finish [instruction] := by
  apply h.run
  · intro s t stack input buffer words hd he
    exact effect_agrees_loop_stack he (hWrite hd) hBound
  · intro s t stack input buffer words model hd he hm
    exact hm.of_stack64_effect he (hWrite hd) hDst hd.apart hValid (hAction hd)

end Md5.Proofs.Block.Rounds
