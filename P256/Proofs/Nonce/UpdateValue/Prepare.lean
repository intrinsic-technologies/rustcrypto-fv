import P256.Proofs.Nonce.UpdateValue.Prepare.Key
import P256.Proofs.Nonce.UpdateValue.Prepare.InnerPad
import P256.Proofs.Nonce.UpdateValue.Prepare.CompressionInitialize
import P256.Proofs.Nonce.UpdateValue.Prepare.Compress
import P256.Proofs.Nonce.UpdateValue.Prepare.OuterPad
import P256.Proofs.Nonce.UpdateValue.Prepare.Assemble

set_option autoImplicit false

namespace P256.Proofs.Nonce.UpdateValue

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem prepare [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {state : State} (pre : UpdateValuePre initial boundary state)
    (saved : Saved initial s state) :
    ∃ fuel t, Advances boundary fuel s t ∧ Prepared initial t state := by
  obtain ⟨keyFuel, t, keyRun, keyed⟩ := Prepare.key pre saved
  obtain ⟨innerFuel, u, innerRun, inner⟩ := Prepare.inner_pad pre keyed
  obtain ⟨initFuel, v, initRun, initialized⟩ := Prepare.initialize_compression pre inner
  obtain ⟨compressFuel, w, compressRun, compressed⟩ := Prepare.compress pre initialized
  obtain ⟨outerFuel, x, outerRun, outer⟩ := Prepare.outer_pad pre compressed
  obtain ⟨assembleFuel, y, assembleRun, assembled⟩ := Prepare.assemble pre outer
  exact ⟨keyFuel + innerFuel + initFuel + compressFuel + outerFuel + assembleFuel, y,
    ((((keyRun.trans innerRun).trans initRun).trans compressRun).trans outerRun).trans assembleRun,
    assembled⟩

end P256.Proofs.Nonce.UpdateValue
