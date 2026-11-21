import Hkdf.Proofs.Common.SHA256.Compression.Safety.Steps
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Memory
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Positions
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part52

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Safety

open Hkdf.Spec Hkdf.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs

set_option maxRecDepth 4096 in
theorem part52 [Bindings] {initial : RamState} {hash : Array UInt32} {block : ByteArray}
    (pre : BlockPre initial hash block) :
    Certificate initial Decoded.part52 before52 after52 positions52 := by
  unfold Decoded.part52 before52 after52 positions52
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 48530 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1097099 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 188) 4
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 188 4 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by decide⟩
  exact .nil _

end Hkdf.Proofs.Common.SHA256.Compression.Safety
