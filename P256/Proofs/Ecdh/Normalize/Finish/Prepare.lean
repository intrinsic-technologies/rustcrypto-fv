import P256.Proofs.Ecdh.Normalize.Finish.Prepare.Result

set_option autoImplicit false

namespace P256.Proofs.Ecdh.Normalize.Finish

open P256.Spec.Operations Standards.SECG.ECC
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Program

theorem prepare [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {point : Projective} (pre : CalleePre s boundary 0x100000 32 32 3464)
    (state : Coordinates s t boundary point) : ∃ u, Prepared s u boundary point := by
  obtain ⟨u, saved⟩ := save_coordinates pre state
  exact prepare_saved pre saved

end P256.Proofs.Ecdh.Normalize.Finish
