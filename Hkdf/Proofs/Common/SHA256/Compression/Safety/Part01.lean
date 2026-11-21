import Hkdf.Proofs.Common.SHA256.Compression.Safety.Steps
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Memory
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Positions
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part01

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Safety

open Hkdf.Spec Hkdf.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs

set_option maxRecDepth 4096 in
theorem part01 [Bindings] {initial : RamState} {hash : Array UInt32} {block : ByteArray}
    (pre : BlockPre initial hash block) :
    Certificate initial Decoded.part01 before01 after01 positions01 := by
  unfold Decoded.part01 before01 after01 positions01
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 38621 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl) (text_inside 38623 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 38625 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 38628 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 38631 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 38634 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 38636 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 38638 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 64 256 ?_ (fun _ => rfl) (text_inside 38646 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      change model.RIP = 1087214 ∧ MemWritable initial ((Operand.reg 4 : Operand 64).read model + 256) 8 ∧ RangeApart ((Operand.reg 4 : Operand 64).read model + 256) 8 1087214 8
      rw [state.rsp]
      exact ⟨state.rip, frame_writable8 pre 256 (by decide) (by decide), frame_apart pre.stack 256 8 222 8 (by decide) (by decide)⟩
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro _
      rw [state.rsp]
      exact saved_load_store state rfl 256 _ (by decide) (by unfold OffsetsApart; decide)
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 38649 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 38651 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 38654 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl) (text_inside 38656 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl) (text_inside 38662 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 38664 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 38667 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 8 ?_ (fun _ => rfl) (text_inside 38670 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 8 ?_ (fun _ => rfl) (text_inside 38674 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 8 ?_ (fun _ => rfl) (text_inside 38677 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl) (text_inside 38680 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl) (text_inside 38684 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl) (text_inside 38687 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 8 ?_ (fun _ => rfl) (text_inside 38690 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 8 ?_ (fun _ => rfl) (text_inside 38693 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 38695 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 38698 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 64 248 ?_ (fun _ => rfl) (text_inside 38706 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      change model.RIP = 1087274 ∧ MemWritable initial ((Operand.reg 4 : Operand 64).read model + 248) 8 ∧ RangeApart ((Operand.reg 4 : Operand 64).read model + 248) 8 1087274 8
      rw [state.rsp]
      exact ⟨state.rip, frame_writable8 pre 248 (by decide) (by decide), frame_apart pre.stack 248 8 282 8 (by decide) (by decide)⟩
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro _
      rw [state.rsp]
      exact saved_load_store state rfl 248 _ (by decide) (by unfold OffsetsApart; decide)
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 38708 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 38711 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 38714 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 38716 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 8 ?_ (fun _ => rfl) (text_inside 38720 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 8 ?_ (fun _ => rfl) (text_inside 38727 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 38730 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 38733 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl) (text_inside 38736 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl) (text_inside 38739 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl) (text_inside 38741 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 38744 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 38747 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 38749 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl) (text_inside 38754 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1087325 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 24) 8
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 24 8 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 7 := List.mem_singleton.mp hr
      subst r
      apply Or.inl
      refine ⟨rfl, ?_⟩
      change (Operand.mem ((Operand.reg 4 : Operand 64).read model + 24) : Operand 64).read model = initial.regValue .rsi
      rw [state.rsp]
      exact state.saved rfl
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl) (text_inside 38758 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1087330 ∧ MemReadable initial ((Operand.reg 7 : Operand 64).read model + 8) 4
      rw [state.pointers 7 (by decide)]
      exact ⟨state.rip, Hkdf.Proofs.Common.Memory.memReadable_sub pre.inputReadable 8 4 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 7 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by decide⟩
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl) (text_inside 38761 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 7 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by decide⟩
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 64 104 ?_ (fun _ => rfl) (text_inside 38766 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      change model.RIP = 1087337 ∧ MemWritable initial ((Operand.reg 4 : Operand 64).read model + 104) 8 ∧ RangeApart ((Operand.reg 4 : Operand 64).read model + 104) 8 1087337 5
      rw [state.rsp]
      exact ⟨state.rip, frame_writable8 pre 104 (by decide) (by decide), frame_apart pre.stack 104 8 345 5 (by decide) (by decide)⟩
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro _
      rw [state.rsp]
      exact saved_load_store state rfl 104 _ (by decide) (by unfold OffsetsApart; decide)
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl) (text_inside 38769 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl) (text_inside 38771 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl) (text_inside 38774 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl) (text_inside 38777 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl) (text_inside 38780 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl) (text_inside 38783 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 64 240 ?_ (fun _ => rfl) (text_inside 38791 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      change model.RIP = 1087359 ∧ MemWritable initial ((Operand.reg 4 : Operand 64).read model + 240) 8 ∧ RangeApart ((Operand.reg 4 : Operand 64).read model + 240) 8 1087359 8
      rw [state.rsp]
      exact ⟨state.rip, frame_writable8 pre 240 (by decide) (by decide), frame_apart pre.stack 240 8 367 8 (by decide) (by decide)⟩
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro _
      rw [state.rsp]
      exact saved_load_store state rfl 240 _ (by decide) (by unfold OffsetsApart; decide)
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl) (text_inside 38794 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl) (text_inside 38797 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl) (text_inside 38800 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl) (text_inside 38804 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 10 ?_ (fun _ => rfl) (text_inside 38807 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 10 ?_ (fun _ => rfl) (text_inside 38811 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl) (text_inside 38815 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl) (text_inside 38817 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl) (text_inside 38823 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 38826 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 3 ?_ (fun _ => rfl) (text_inside 38828 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 3 ?_ (fun _ => rfl) (text_inside 38831 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  exact .nil _

end Hkdf.Proofs.Common.SHA256.Compression.Safety
