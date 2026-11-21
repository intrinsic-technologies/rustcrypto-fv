import Md5.Proofs.Buffered.DigestPrepare.Initialize.Execution
import Md5.Proofs.Buffered.DigestPrepare.Initialize.Postcondition

namespace Md5.Proofs.Buffered.DigestPrepare

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem «initialize» [bindings : Bindings] {initial : RamState} {input : ByteArray}
    (hReady : ReadyToStep initial) (hCode : CodeIn Extracted.programImage initial)
    (hCall : Digest.ValidCall bindings initial input) :
    ∃ fuel s, Advances (returnBoundary initial) fuel initial s ∧
      Initialized initial (returnBoundary initial) input s := by
  have hFrame : Streaming.PrologueFrame 0x100010 Digest.minStackBytes initial :=
    ⟨hCall.atEntryPoint, hCall.stackAvailable, (hCall.stackSeparation.2 _ (by simp)).2⟩
  have hb := nearReturn64Boundary_eq initial hReady.dataReady hReady.cpu.ss
    (stack_return_readable hCall.stackAvailable)
  obtain ⟨boundary, hb', _, hOutside⟩ := hCall.returnAddress
  have hEq : boundary = returnBoundary initial := Except.ok.inj (hb'.symm.trans hb)
  subst boundary
  obtain ⟨fuel, s, hRun, hs, hc, he⟩ :=
    Initialize.execute (returnBoundary initial) hReady hCode hFrame hOutside
  exact ⟨fuel, s, hRun, Initialize.postcondition hCall hFrame hOutside hs hc he⟩

end Md5.Proofs.Buffered.DigestPrepare
