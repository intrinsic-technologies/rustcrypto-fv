import P256.Proofs.Nonce.Update.Entry
import P256.Proofs.Nonce.Update.Prepare.Key
import P256.Proofs.Nonce.Update.Prepare.InnerPad
import P256.Proofs.Nonce.Update.Prepare.CompressionInitialize
import P256.Proofs.Nonce.Update.Prepare.Compress
import P256.Proofs.Nonce.Update.Prepare.OuterPad
import P256.Proofs.Nonce.Update.Prepare.Assemble

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem prepare [Bindings] {initial : RamState} {boundary : ReturnBoundary}
    {state : State} (pre : DrbgCalleePre initial boundary 0x109f30 1856 state) :
    ∃ fuel t, Advances boundary fuel initial t ∧ Prepared initial t state := by
  obtain ⟨s, entryRun, saved⟩ := entry pre
  obtain ⟨_, t, keyRun, keyed⟩ := Prepare.key pre saved
  obtain ⟨_, u, padRun, padded⟩ := Prepare.inner_pad pre keyed
  obtain ⟨_, v, setupRun, setup⟩ := Prepare.initialize_compression pre padded
  obtain ⟨_, w, compressRun, compressed⟩ := Prepare.compress pre setup
  obtain ⟨_, x, outerRun, outer⟩ := Prepare.outer_pad pre compressed
  obtain ⟨_, y, assembleRun, prepared⟩ := Prepare.assemble pre outer
  exact ⟨_, y, (((((entryRun.trans keyRun).trans padRun).trans setupRun).trans
    compressRun).trans outerRun).trans assembleRun, prepared⟩

end P256.Proofs.Nonce.Update
