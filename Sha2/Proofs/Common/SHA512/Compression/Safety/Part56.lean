import Sha2.Proofs.Wrapper.Call
import Sha2.Proofs.Common.SHA512.Compression.Safety.Steps
import Sha2.Proofs.Common.SHA512.Compression.Safety.Memory
import Sha2.Proofs.Common.SHA512.Compression.Safety.Positions
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part56

set_option autoImplicit false
namespace Sha2.Proofs.Common.SHA512.Compression.Safety
open Sha2.Spec Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
set_option maxRecDepth 4096 in
 theorem part56 [Bindings] {initial : RamState} {hash : Array UInt64} {block : ByteArray}
    (pre : BlockPre initial hash block):
    Certificate initial Decoded.part56 before56 after56 positions56 := by
  unfold Decoded.part56 before56 after56 positions56
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71655 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 3 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71658 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71666 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      change model.RIP = 1120234 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 320) 8
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 320 8 (by decide)⟩

    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 8 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71674 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      change model.RIP = 1120242 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 336) 8
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 336 8 (by decide)⟩

    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  apply Certificate.cons
  · refine StepCertificate.of_register pre 13 ?_ (fun _ => rfl)
      (by simpa [positionOfNoRsi] using text_inside 71682 (by decide)) (by simp [blockComponents]) (by decide)
      (fun h => h) ?_
    · intro model state
      change model.RIP = 1120250 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 352) 8
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 352 8 (by decide)⟩

    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      cases hr
  exact .nil _
end Sha2.Proofs.Common.SHA512.Compression.Safety
