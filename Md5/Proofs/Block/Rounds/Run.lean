import Md5.Proofs.Block.Rounds.Interface
import Md5.Proofs.Block.Rounds.Program
import Md5.Proofs.Block.Rounds.Projection

namespace Md5.Proofs.Block.Rounds

open Md5.Spec Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs

def RunWords [Bindings] (start finish : BitVec 64) (instructions : List WordInstruction) :
    Prop :=
  ∀ {s : RamState} {boundary : ReturnBoundary} {stack input : BitVec 64}
    {buffer : Standards.RFC.MD5.Buffer} {words : Vector (BitVec 32) 16} {model : WordState},
    ReadyToStep s → CodeIn Extracted.programImage s → s.RIP = start →
    LoopData stack input buffer words s → OutsideCompression boundary.rip →
    MachineWords stack input s model →
    ∃ fuel t buffer', Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ t.RIP = finish ∧
      LoopData stack input buffer' words t ∧
      MachineWords stack input t (executeWords instructions model) ∧
      AgreesExcept (loopComponents stack) s t

theorem RunWords.seq [Bindings] {start middle finish : BitVec 64}
    {first second : List WordInstruction} (hFirst : RunWords start middle first)
    (hSecond : RunWords middle finish second) :
    RunWords start finish (first ++ second) := by
  intro s boundary stack input buffer words model hReady hCode hEntry hData hBoundary hModel
  obtain ⟨n, t, middleBuffer, hAdvance, hReady', hCode', hMiddle, hData', hModel', hFrame⟩ :=
    hFirst hReady hCode hEntry hData hBoundary hModel
  obtain ⟨m, u, finalBuffer, hAdvance', hReady'', hCode'', hFinish, hData'', hModel'', hFrame'⟩ :=
    hSecond hReady' hCode' hMiddle hData' hBoundary hModel'
  refine ⟨n + m, u, finalBuffer, hAdvance.trans hAdvance', hReady'', hCode'', hFinish,
    hData'', ?_, ?_⟩
  · simpa only [executeWords_append] using hModel''
  · exact (hFrame.trans hFrame').mono (by
      intro c hc
      simpa only [List.mem_append, or_self] using hc)

theorem RunWords.congr [Bindings] {start finish : BitVec 64}
    {first second : List WordInstruction} (h : RunWords start finish first)
    (he : first = second) : RunWords start finish second := he ▸ h

attribute [irreducible] RunWords

end Md5.Proofs.Block.Rounds
