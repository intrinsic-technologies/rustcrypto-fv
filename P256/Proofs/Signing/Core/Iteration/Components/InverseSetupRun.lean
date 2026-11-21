import P256.Proofs.Signing.Core.Iteration.Components.InverseSetup
import P256.Proofs.Signing.Core.Iteration.Memory

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Components.InverseSetup

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open SecretKeyFromBytes.Scalar (Nat256At)


theorem run [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (hp : SignPre s boundary) (frame : Frame s t) (rip : t.RIP = 0x10d2d5) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ (effect t).Holds t u := by
  obtain ⟨n,u,run,ready,_,effect⟩ := block boundary
    (fun i hi => by
      have addr : (0x10d2d5 : BitVec 64)+BitVec.ofNat 64 i =
          Extracted.textAddress+BitVec.ofNat 64 (0xd2d5+i) := by
        rw [BitVec.ofNat_add,← BitVec.add_assoc]
        rfl
      rw [addr]
      exact boundary_ne_program hp.outerBoundary (inProgram_of_textOffset _ (by omega)))
    t (readyToStep frame.machine frame.bindingsSupported)
    (programText_slice (programLoaded_codeIn frame.loaded) 0xd2d5 bytes
      (by decide) (by decide +kernel)) rip
  exact ⟨n,u,run,after_registers frame ready effect.agrees
    (by simp [InverseSetup.effect,Effect.components,Component.Covers])
    (by simp [InverseSetup.effect,Effect.components]) (by simp [InverseSetup.effect,Effect.components])
    (by simp [InverseSetup.effect,Effect.components]) (by simp [InverseSetup.effect,Effect.components]),effect⟩

end P256.Proofs.Signing.Core.Iteration.Components.InverseSetup
