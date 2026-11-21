import P256.Proofs.Sec1.Decompress.Select.Candidate
import P256.Proofs.Sec1.Decompress.Select.Sign.Correct

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decompress
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem select_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {odd : Bool} (pre : Pre s boundary bytes odd)
    (state : RootState s t (Standards.SECG.ECC.Encoding.octetsToNat bytes) odd) :
    ∃ fuel u, Advances boundary fuel t u ∧
      SelectedState s u (Standards.SECG.ECC.Encoding.octetsToNat bytes) odd := by
  obtain ⟨n, u, run, candidate⟩ := Select.candidate_correct pre.toCalleePre state
  obtain ⟨m, v, advance, selected⟩ := Select.Sign.correct pre.toCalleePre candidate
  exact ⟨n+m, v, run.trans advance, selected⟩

end P256.Proofs.Sec1.Decompress
