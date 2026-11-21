import P256.Proofs.SHA256.Compression.Safety.Steps
import P256.Proofs.SHA256.Compression.Safety.Memory
import P256.Proofs.SHA256.Compression.Safety.Positions
import P256.Proofs.SHA256.Compression.Decoded.Part52

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Safety

open P256.Proofs.Common.SHA256.Compression

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

set_option maxRecDepth 4096 in
theorem part52 [Bindings] {initial : RamState} {hash : Array UInt32} {block : ByteArray}
    (pre : BlockPre initial hash block) :
    Certificate initial Decoded.part52 before52 after52 positions52 := by
  unfold Decoded.part52 before52 after52 positions52
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 98658 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1147227 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 188) 4
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 188 4 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by decide⟩
  exact .nil _

end P256.Proofs.SHA256.Compression.Safety
