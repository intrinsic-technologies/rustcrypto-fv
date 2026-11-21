import P256.Proofs.Nonce.Update.Seeded.Prepare.KeyReturn
import P256.Proofs.Nonce.Update.Seeded.Prepare.Memory
import P256.Proofs.Nonce.Update.Seeded.Prepare.KeySetup

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Seeded.Prepare

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

variable [Bindings] {initial s : RamState} {boundary : ReturnBoundary} {original state : State}

theorem key_setup (_pre : DrbgCalleePre initial boundary 0x109f30 1856 original)
    (entered : Entered initial s state) :
    ∃ fuel t, Advances boundary fuel s t ∧ KeyReady initial t state := by
  exact ⟨0,s,.refl _,⟨entered.toFrameState,entered.drbg,entered.drbgPointer,
    entered.savedPointer,entered.savedValue,entered.descriptors,entered.savedEnd⟩,entered.rip⟩

theorem key_call (pre : DrbgCalleePre initial boundary 0x109f30 1856 original)
    (current : KeyReady initial s state) :
    ∃ fuel t, Advances boundary fuel s t ∧ Keyed initial t state := by
  obtain ⟨fuel,t,run,ready,holds⟩ := key_call_entry pre current
  exact ⟨fuel,t,run,key_return pre current ready holds⟩

theorem key (pre : DrbgCalleePre initial boundary 0x109f30 1856 original)
    (entered : Entered initial s state) :
    ∃ fuel t, Advances boundary fuel s t ∧ Keyed initial t state := by
  obtain ⟨_, u, setupRun, setup⟩ := key_setup pre entered
  obtain ⟨_, t, keyRun, keyed⟩ := key_call pre setup
  exact ⟨_, t, setupRun.trans keyRun, keyed⟩

end P256.Proofs.Nonce.Update.Seeded.Prepare
