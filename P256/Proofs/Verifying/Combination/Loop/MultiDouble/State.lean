import P256.Proofs.Verifying.Combination.Loop.MultiRoundState
import P256.Proofs.Verifying.Combination.PointMemory
import P256.Proofs.Verifying.Combination.PointCall

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

theorem scratch_result [Bindings] {s t w : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64} {p q point scratch : Projective} {u v k : Nat}
    {ip ret : BitVec 64} (pre : MultiPre s boundary tables digits)
    (state : RoundState s t tables digits p q u v k point ip)
    (result : PointCallResult s t w boundary ret 144 scratch) :
    RoundState s w tables digits p q u v k point ret := by
  refine ⟨⟨state.toMemory.of_frame pre result.toFrameState,
    (result.registers .rbx (by simp)).trans state.count, state.positive, state.bounded,
    (result.registers .r15 (by simp)).trans state.scratch, ?_, ?_, ?_, ?_⟩,
    result.rip, (result.registers .r13 (by simp)).trans state.cursor, ?_⟩
  · exact state.value.of_bytes_eq
      (result.bytes 336 96 (by decide) (by decide) (Or.inr (by decide)))
  · exact (result.read (offset := 400) (n := 64) (by decide) (by decide)
      (Or.inr (by decide))).trans state.total
  · exact (result.read (offset := 384) (n := 64) (by decide) (by decide)
      (Or.inr (by decide))).trans state.tableBase
  · exact (result.read (offset := 392) (n := 64) (by decide) (by decide)
      (Or.inr (by decide))).trans state.output
  · intro h
    rw [result.registers .r14 (by simp)] at h
    exact state.identity h

end P256.Proofs.Verifying.Combination.Loop.Multi
