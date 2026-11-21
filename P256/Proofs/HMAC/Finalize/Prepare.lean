import P256.Proofs.HMAC.Finalize.Prepare.Setup
import P256.Proofs.HMAC.Finalize.Prepare.Outer
import P256.Proofs.HMAC.Finalize.Prepare.InnerSetup
import P256.Proofs.HMAC.Finalize.Prepare.Inner

open P256.Proofs.Program
open P256.Proofs.Program.ScalarFrame (workRegion)

set_option autoImplicit false

namespace P256.Proofs.HMAC.Finalize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem prepare [Bindings] {initial : RamState} {boundary : ReturnBoundary}
    {key input : ByteArray} (pre : HmacFinalizePre initial boundary key input) :
    ∃ fuel t, Advances boundary fuel initial t ∧ Prepared initial t key input ∧
      t.RIP = paddingStart false := by
  obtain ⟨setupFuel, a, setupRun, setup⟩ := Prepare.setup pre
  obtain ⟨outerFuel, b, outerRun, outer⟩ := Prepare.outer_compress pre.toHashCalleePre setup
  obtain ⟨innerFuel, c, innerRun, inner⟩ := Prepare.inner_setup pre.toHashCalleePre outer
  obtain ⟨t, copyRun, prepared, rip⟩ := Prepare.copy_inner pre.toHashCalleePre inner
  exact ⟨setupFuel + outerFuel + innerFuel + 13, t,
    ((setupRun.trans outerRun).trans innerRun).trans copyRun, prepared, rip⟩

end P256.Proofs.HMAC.Finalize
