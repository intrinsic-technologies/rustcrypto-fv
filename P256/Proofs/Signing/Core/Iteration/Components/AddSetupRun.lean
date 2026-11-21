import P256.Proofs.Signing.Core.Iteration.Components.AddSetup
import P256.Proofs.Signing.Core.Iteration.Memory

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Components.AddSetup

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open SecretKeyFromBytes.Scalar (Nat256At)


theorem run [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (hp : SignPre s boundary) (frame : Frame s t) (rip : t.RIP = 0x10d2c2) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ (effect t).Holds t u := by
  obtain ⟨n,u,run,ready,_,effect⟩ := block boundary
    (fun i hi => by
      have addr : (0x10d2c2 : BitVec 64)+BitVec.ofNat 64 i =
          Extracted.textAddress+BitVec.ofNat 64 (0xd2c2+i) := by
        rw [BitVec.ofNat_add,← BitVec.add_assoc]
        rfl
      rw [addr]
      exact boundary_ne_program hp.outerBoundary (inProgram_of_textOffset _ (by omega)))
    t (readyToStep frame.machine frame.bindingsSupported)
    (programText_slice (programLoaded_codeIn frame.loaded) 0xd2c2 bytes
      (by decide) (by decide +kernel)) rip
  exact ⟨n,u,run,after_registers frame ready effect.agrees
    (by simp [AddSetup.effect,Effect.components,Component.Covers])
    (by simp [AddSetup.effect,Effect.components]) (by simp [AddSetup.effect,Effect.components])
    (by simp [AddSetup.effect,Effect.components]) (by simp [AddSetup.effect,Effect.components]),effect⟩

end P256.Proofs.Signing.Core.Iteration.Components.AddSetup
