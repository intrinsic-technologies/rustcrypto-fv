import P256.Proofs.Nonce.Initialize.Seed.UpdateResult

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Seed

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem update_call [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {value secret : Nat}
    (pre : Nonce.InitializePre initial boundary orderAddress)
    (state : UpdateReady initial s boundary orderAddress value)
    (key : (registerRegion initial .rsi 32).HasBytes initial.external
      (Standards.RFC.DeterministicSigning.Nonce.intToOctets Operations.domain.n secret)) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧
      (callEffect (fun _ => 0x109f30) 0x107c1a s).Holds s t ∧
      UpdateSeededPre t boundary ⟨⟨Array.replicate 32 0⟩, ⟨Array.replicate 32 1⟩⟩
        (Standards.RFC.DeterministicSigning.Nonce.intToOctets Operations.domain.n secret)
        (Standards.RFC.DeterministicSigning.Nonce.intToOctets Operations.domain.n value) := by
  obtain ⟨t, run, ready, effect⟩ := ScalarFrame.scalar_call pre.toCalleePre
    (by decide) (by decide) state.stage.toFrameState 0x7c15 0x2316
    (by decide) (by decide +kernel) (by decide +kernel)
    (inProgram_of_textOffset 0x9f30 (by decide)) state.rip
  change (callEffect (fun _ => 0x109f30) 0x107c1a s).Holds s t at effect
  exact ⟨t, run, ready, effect, update_pre pre state key run ready effect⟩

end P256.Proofs.Nonce.Initialize.Seed
