import P256.Proofs.HMAC.Pad.Loop

set_option autoImplicit false

namespace P256.Proofs.HMAC.Pad

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem keyPad_correct [Bindings] {loop : Loop} {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (outside : ¬ InProgram boundary.rip)
    (pre : Pre loop s) (key : ByteArray) (old : UInt8)
    (input : (MemoryRegion.mk (buffer loop s).toNat 64).HasBytes s.external
      (HMAC.keyPad key old)) :
    ∃ t, Advances boundary 112 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧ Post loop s t ∧
      (MemoryRegion.mk (buffer loop s).toNat 64).HasBytes t.external
        (HMAC.keyPad key (old ^^^ loop.mask)) := by
  obtain ⟨t, execution, readyT, loadedT, post⟩ := loop_correct ready loaded outside pre
  exact ⟨t, execution, readyT, loadedT, post, post.keyPad key old input⟩

end P256.Proofs.HMAC.Pad
