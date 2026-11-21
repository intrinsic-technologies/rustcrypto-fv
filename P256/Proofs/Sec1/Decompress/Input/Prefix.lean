import P256.Proofs.Sec1.Decompress.Input.CanonicalState

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decompress.Input

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Standards.SECG.ECC

theorem prefix_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {odd : Bool} (pre : Pre s boundary bytes odd) :
    ∃ fuel t, Advances boundary fuel s t ∧
      CanonicalState s t (Encoding.octetsToNat bytes) odd := by
  obtain ⟨n, u, runU, stateU⟩ := decode pre
  obtain ⟨m, v, runV, stateV⟩ := store pre stateU
  obtain ⟨k, t, runT, stateT⟩ := canonical_state pre stateV
  exact ⟨n+m+k, t, (runU.trans runV).trans runT, stateT⟩

end P256.Proofs.Sec1.Decompress.Input
