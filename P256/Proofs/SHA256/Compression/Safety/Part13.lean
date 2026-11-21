import P256.Proofs.SHA256.Compression.Safety.Steps
import P256.Proofs.SHA256.Compression.Safety.Memory
import P256.Proofs.SHA256.Compression.Safety.Positions
import P256.Proofs.SHA256.Compression.Decoded.Part13

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Safety

open P256.Proofs.Common.SHA256.Compression

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

set_option maxRecDepth 4096 in
theorem part13 [Bindings] {initial : RamState} {hash : Array UInt32} {block : ByteArray}
    (pre : BlockPre initial hash block) :
    Certificate initial Decoded.part13 before13 after13 positions13 := by
  unfold Decoded.part13 before13 after13 positions13
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 91083 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 91086 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 91088 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 91091 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 91094 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 91096 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 8 ?_ (fun _ => rfl) (text_inside 91101 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1139672 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 80) 8
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 80 8 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 91104 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 91107 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl) (text_inside 91110 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl) (text_inside 91113 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl) (text_inside 91115 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 91118 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 91121 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 91123 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl) (text_inside 91125 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 91129 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1139701 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 40) 4
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 40 4 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 32 168 ?_ (fun _ => rfl) (text_inside 91136 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      change model.RIP = 1139705 ∧ MemWritable initial ((Operand.reg 4 : Operand 64).read model + 168) 4 ∧ RangeApart ((Operand.reg 4 : Operand 64).read model + 168) 4 1139705 7
      rw [state.rsp]
      exact ⟨state.rip, frame_writable4 pre.stack 168 (by decide) (by decide), frame_apart pre.stack 168 4 2585 7 (by decide) (by decide)⟩
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro _
      rw [state.rsp]
      exact saved_load_store state rfl 168 _ (by decide) (by unfold OffsetsApart; decide)
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 32 172 ?_ (fun _ => rfl) (text_inside 91143 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      change model.RIP = 1139712 ∧ MemWritable initial ((Operand.reg 4 : Operand 64).read model + 172) 4 ∧ RangeApart ((Operand.reg 4 : Operand 64).read model + 172) 4 1139712 7
      rw [state.rsp]
      exact ⟨state.rip, frame_writable4 pre.stack 172 (by decide) (by decide), frame_apart pre.stack 172 4 2592 7 (by decide) (by decide)⟩
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro _
      rw [state.rsp]
      exact saved_load_store state rfl 172 _ (by decide) (by unfold OffsetsApart; decide)
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 32 176 ?_ (fun _ => rfl) (text_inside 91150 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      change model.RIP = 1139719 ∧ MemWritable initial ((Operand.reg 4 : Operand 64).read model + 176) 4 ∧ RangeApart ((Operand.reg 4 : Operand 64).read model + 176) 4 1139719 7
      rw [state.rsp]
      exact ⟨state.rip, frame_writable4 pre.stack 176 (by decide) (by decide), frame_apart pre.stack 176 4 2599 7 (by decide) (by decide)⟩
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro _
      rw [state.rsp]
      exact saved_load_store state rfl 176 _ (by decide) (by unfold OffsetsApart; decide)
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 91153 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 32 40 ?_ (fun _ => rfl) (text_inside 91157 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      change model.RIP = 1139729 ∧ MemWritable initial ((Operand.reg 4 : Operand 64).read model + 40) 4 ∧ RangeApart ((Operand.reg 4 : Operand 64).read model + 40) 4 1139729 4
      rw [state.rsp]
      exact ⟨state.rip, frame_writable4 pre.stack 40 (by decide) (by decide), frame_apart pre.stack 40 4 2609 4 (by decide) (by decide)⟩
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro _
      rw [state.rsp]
      exact saved_load_store state rfl 40 _ (by decide) (by unfold OffsetsApart; decide)
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl) (text_inside 91160 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 32 140 ?_ (fun _ => rfl) (text_inside 91167 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      change model.RIP = 1139736 ∧ MemWritable initial ((Operand.reg 4 : Operand 64).read model + 140) 4 ∧ RangeApart ((Operand.reg 4 : Operand 64).read model + 140) 4 1139736 7
      rw [state.rsp]
      exact ⟨state.rip, frame_writable4 pre.stack 140 (by decide) (by decide), frame_apart pre.stack 140 4 2616 7 (by decide) (by decide)⟩
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro _
      rw [state.rsp]
      exact saved_load_store state rfl 140 _ (by decide) (by unfold OffsetsApart; decide)
  apply Certificate.cons
  · refine StepCertificate.of_register pre 13 ?_ (fun _ => rfl) (text_inside 91171 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 13 ?_ (fun _ => rfl) (text_inside 91174 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 91178 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1139750 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 64) 4
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 64 4 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 32 144 ?_ (fun _ => rfl) (text_inside 91185 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      change model.RIP = 1139754 ∧ MemWritable initial ((Operand.reg 4 : Operand 64).read model + 144) 4 ∧ RangeApart ((Operand.reg 4 : Operand 64).read model + 144) 4 1139754 7
      rw [state.rsp]
      exact ⟨state.rip, frame_writable4 pre.stack 144 (by decide) (by decide), frame_apart pre.stack 144 4 2634 7 (by decide) (by decide)⟩
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro _
      rw [state.rsp]
      exact saved_load_store state rfl 144 _ (by decide) (by unfold OffsetsApart; decide)
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 32 148 ?_ (fun _ => rfl) (text_inside 91192 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      change model.RIP = 1139761 ∧ MemWritable initial ((Operand.reg 4 : Operand 64).read model + 148) 4 ∧ RangeApart ((Operand.reg 4 : Operand 64).read model + 148) 4 1139761 7
      rw [state.rsp]
      exact ⟨state.rip, frame_writable4 pre.stack 148 (by decide) (by decide), frame_apart pre.stack 148 4 2641 7 (by decide) (by decide)⟩
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro _
      rw [state.rsp]
      exact saved_load_store state rfl 148 _ (by decide) (by unfold OffsetsApart; decide)
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 32 152 ?_ (fun _ => rfl) (text_inside 91199 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      change model.RIP = 1139768 ∧ MemWritable initial ((Operand.reg 4 : Operand 64).read model + 152) 4 ∧ RangeApart ((Operand.reg 4 : Operand 64).read model + 152) 4 1139768 7
      rw [state.rsp]
      exact ⟨state.rip, frame_writable4 pre.stack 152 (by decide) (by decide), frame_apart pre.stack 152 4 2648 7 (by decide) (by decide)⟩
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro _
      rw [state.rsp]
      exact saved_load_store state rfl 152 _ (by decide) (by unfold OffsetsApart; decide)
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 91202 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 91205 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 32 64 ?_ (fun _ => rfl) (text_inside 91209 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      change model.RIP = 1139781 ∧ MemWritable initial ((Operand.reg 4 : Operand 64).read model + 64) 4 ∧ RangeApart ((Operand.reg 4 : Operand 64).read model + 64) 4 1139781 4
      rw [state.rsp]
      exact ⟨state.rip, frame_writable4 pre.stack 64 (by decide) (by decide), frame_apart pre.stack 64 4 2661 4 (by decide) (by decide)⟩
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro _
      rw [state.rsp]
      exact saved_load_store state rfl 64 _ (by decide) (by unfold OffsetsApart; decide)
  apply Certificate.cons
  · refine StepCertificate.of_register pre 13 ?_ (fun _ => rfl) (text_inside 91212 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 32 4 ?_ (fun _ => rfl) (text_inside 91217 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      change model.RIP = 1139788 ∧ MemWritable initial ((Operand.reg 4 : Operand 64).read model + 4) 4 ∧ RangeApart ((Operand.reg 4 : Operand 64).read model + 4) 4 1139788 5
      rw [state.rsp]
      exact ⟨state.rip, frame_writable4 pre.stack 4 (by decide) (by decide), frame_apart pre.stack 4 4 2668 5 (by decide) (by decide)⟩
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro _
      rw [state.rsp]
      exact saved_load_store state rfl 4 _ (by decide) (by unfold OffsetsApart; decide)
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 91220 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 91222 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl) (text_inside 91227 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1139798 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 36) 4
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 36 4 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 91230 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 12 ?_ (fun _ => rfl) (text_inside 91233 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 10 ?_ (fun _ => rfl) (text_inside 91236 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 91238 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl) (text_inside 91241 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 5 ?_ (fun _ => rfl) (text_inside 91244 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 91246 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 32 36 ?_ (fun _ => rfl) (text_inside 91250 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      change model.RIP = 1139822 ∧ MemWritable initial ((Operand.reg 4 : Operand 64).read model + 36) 4 ∧ RangeApart ((Operand.reg 4 : Operand 64).read model + 36) 4 1139822 4
      rw [state.rsp]
      exact ⟨state.rip, frame_writable4 pre.stack 36 (by decide) (by decide), frame_apart pre.stack 36 4 2702 4 (by decide) (by decide)⟩
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro _
      rw [state.rsp]
      exact saved_load_store state rfl 36 _ (by decide) (by unfold OffsetsApart; decide)
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 91253 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 91255 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 91258 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1139831 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 0) 4
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 0 4 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 3 ?_ (fun _ => rfl) (text_inside 91260 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 64 72 ?_ (fun _ => rfl) (text_inside 91265 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      change model.RIP = 1139836 ∧ MemWritable initial ((Operand.reg 4 : Operand 64).read model + 72) 8 ∧ RangeApart ((Operand.reg 4 : Operand 64).read model + 72) 8 1139836 5
      rw [state.rsp]
      exact ⟨state.rip, frame_writable8 pre 72 (by decide) (by decide), frame_apart pre.stack 72 8 2716 5 (by decide) (by decide)⟩
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro _
      rw [state.rsp]
      exact saved_load_store state rfl 72 _ (by decide) (by unfold OffsetsApart; decide)
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 91267 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 32 16 ?_ (fun _ => rfl) (text_inside 91271 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      change model.RIP = 1139843 ∧ MemWritable initial ((Operand.reg 4 : Operand 64).read model + 16) 4 ∧ RangeApart ((Operand.reg 4 : Operand 64).read model + 16) 4 1139843 4
      rw [state.rsp]
      exact ⟨state.rip, frame_writable4 pre.stack 16 (by decide) (by decide), frame_apart pre.stack 16 4 2723 4 (by decide) (by decide)⟩
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro _
      rw [state.rsp]
      exact saved_load_store state rfl 16 _ (by decide) (by unfold OffsetsApart; decide)
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 91274 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 91277 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 91281 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1139853 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 52) 4
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 52 4 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 3 ?_ (fun _ => rfl) (text_inside 91286 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1139857 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 104) 8
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 104 8 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 3 ?_ (fun _ => rfl) (text_inside 91288 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 91290 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 32 100 ?_ (fun _ => rfl) (text_inside 91294 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      change model.RIP = 1139866 ∧ MemWritable initial ((Operand.reg 4 : Operand 64).read model + 100) 4 ∧ RangeApart ((Operand.reg 4 : Operand 64).read model + 100) 4 1139866 4
      rw [state.rsp]
      exact ⟨state.rip, frame_writable4 pre.stack 100 (by decide) (by decide), frame_apart pre.stack 100 4 2746 4 (by decide) (by decide)⟩
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro _
      rw [state.rsp]
      exact saved_load_store state rfl 100 _ (by decide) (by unfold OffsetsApart; decide)
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 91297 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 91300 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl) (text_inside 91305 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1139876 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 12) 4
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 12 4 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 91308 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  exact .nil _

end P256.Proofs.SHA256.Compression.Safety
