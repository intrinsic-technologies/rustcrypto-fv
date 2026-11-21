import P256.Proofs.Nonce.Update.Seeded.Prepare.Key
import P256.Proofs.Nonce.Update.Seeded.Prepare.Pad
import P256.Proofs.Nonce.Update.Seeded.Prepare.CompressionInitialize
import P256.Proofs.Nonce.Update.Seeded.Prepare.Compress
import P256.Proofs.Nonce.Update.Seeded.Prepare.Assemble.Inner
import P256.Proofs.Nonce.Update.Seeded.Prepare.Assemble.Outer
import P256.Proofs.Nonce.Update.Seeded.Prepare.Assemble.Copy

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Seeded

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem prepare [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {original state : State} {secret reduced : ByteArray}
    (pre : UpdateSeededPre initial boundary original secret reduced)
    (entered : Entered initial s state) :
    ∃ fuel t, Advances boundary fuel s t ∧ Prepared initial t state := by
  obtain ⟨_, s₁, h₁, keyed⟩ := Prepare.key pre.toDrbgCalleePre entered
  obtain ⟨_, s₂, h₂, padded⟩ := Prepare.inner_pad pre.toDrbgCalleePre keyed
  obtain ⟨_, s₃, h₃, setup⟩ := Prepare.initialize_compression pre.toDrbgCalleePre padded
  obtain ⟨_, s₄, h₄, compressed⟩ := Prepare.compress pre.toDrbgCalleePre setup
  obtain ⟨_, s₅, h₅, outer⟩ := Prepare.outer_pad pre.toDrbgCalleePre compressed
  obtain ⟨_, s₆, h₆, inner⟩ := Prepare.Assemble.copy_inner pre.toDrbgCalleePre outer
  obtain ⟨_, s₇, h₇, copied⟩ := Prepare.Assemble.copy_outer pre.toDrbgCalleePre inner
  obtain ⟨_, s₈, h₈, prepared⟩ := Prepare.Assemble.copy_hmac pre.toDrbgCalleePre copied
  exact ⟨_, s₈, ((((((h₁.trans h₂).trans h₃).trans h₄).trans h₅).trans h₆).trans h₇).trans h₈,
    prepared⟩

end P256.Proofs.Nonce.Update.Seeded
