import P256.Proofs.Sec1.Affine.Compact.Normalize.Original
import P256.Proofs.Sec1.Affine.Compact.Normalize.Negate
import P256.Proofs.Sec1.Affine.Compact.Normalize.PrepareDecode
import P256.Proofs.Sec1.Affine.Compact.Normalize.Decode
import P256.Proofs.Sec1.Affine.Compact.Normalize.Minimum

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compact

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Standards.SECG.ECC

theorem normalize [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    {point : Option Curve.Point} (pre : AffineDecodePre s boundary bytes)
    (state : Flags.Flagged s t point) :
    ∃ fuel u, Advances boundary fuel t u ∧ Finish.Prepared s u point := by
  obtain ⟨n,a,runA,stateA⟩ := Normalize.prepare_original pre state
  obtain ⟨m,b,runB,stateB⟩ := Normalize.negate pre stateA
  obtain ⟨k,c,runC,stateC⟩ := Normalize.prepare_decode pre stateB
  obtain ⟨j,d,runD,stateD⟩ := Normalize.decode_coordinates pre stateC
  obtain ⟨l,u,runU,stateU⟩ := Normalize.select_minimum pre stateD
  exact ⟨n+m+k+j+l,u,(((runA.trans runB).trans runC).trans runD).trans runU,stateU⟩

end P256.Proofs.Sec1.Affine.Compact
