import Sha2.Proofs.Wrapper.Hash.Serialize.Payload

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Hash

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

variable {v : Variant}

 theorem serialize [Bindings] {initial s : RamState} {inputs : Array Input} {message : ByteArray}
    (ctx : Context initial inputs v) (input : Compressed initial s message v) :
    ∃ t, Preserved initial t v ∧ t.RIP = v.pc v.epilogueOffset ∧
      (outputRegion v.routine initial).HasBytes t.external (v.hash message) := by
  obtain ⟨fuel, t, execution, ready, _, effect⟩ := Serialize.run (returnBoundary initial)
    (validCall_returnBoundary ctx.machine ctx.call).2.2 v s
    (supportedMachine_readyToStep input.machine) (Serialize.code input.loaded v)
    (Serialize.pre ctx input)
  have frame := Serialize.frame input.toPreserved effect
  have preserved := Serialize.preserved ctx input.toPreserved execution ready frame
  exact ⟨t, preserved, effect.rip, Serialize.payload ctx input preserved.toState effect⟩

end Sha2.Proofs.Wrapper.Hash
