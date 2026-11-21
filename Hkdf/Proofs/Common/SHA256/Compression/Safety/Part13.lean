import Hkdf.Proofs.Common.SHA256.Compression.Safety.Steps
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Memory
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Positions
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part13

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Safety

open Hkdf.Spec Hkdf.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs

set_option maxRecDepth 4096 in
theorem part13 [Bindings] {initial : RamState} {hash : Array UInt32} {block : ByteArray}
    (pre : BlockPre initial hash block) :
    Certificate initial Decoded.part13 before13 after13 positions13 := by
  unfold Decoded.part13 before13 after13 positions13
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 40955 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 40958 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 40960 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 40963 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 40966 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 40968 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 8 ?_ (fun _ => rfl) (text_inside 40973 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1089544 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 80) 8
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 80 8 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 40976 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 40979 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl) (text_inside 40982 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl) (text_inside 40985 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl) (text_inside 40987 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 40990 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 40993 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 40995 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl) (text_inside 40997 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 41001 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1089573 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 40) 4
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 40 4 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 32 168 ?_ (fun _ => rfl) (text_inside 41008 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      change model.RIP = 1089577 ∧ MemWritable initial ((Operand.reg 4 : Operand 64).read model + 168) 4 ∧ RangeApart ((Operand.reg 4 : Operand 64).read model + 168) 4 1089577 7
      rw [state.rsp]
      exact ⟨state.rip, frame_writable4 pre.stack 168 (by decide) (by decide), frame_apart pre.stack 168 4 2585 7 (by decide) (by decide)⟩
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro _
      rw [state.rsp]
      exact saved_load_store state rfl 168 _ (by decide) (by unfold OffsetsApart; decide)
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 32 172 ?_ (fun _ => rfl) (text_inside 41015 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      change model.RIP = 1089584 ∧ MemWritable initial ((Operand.reg 4 : Operand 64).read model + 172) 4 ∧ RangeApart ((Operand.reg 4 : Operand 64).read model + 172) 4 1089584 7
      rw [state.rsp]
      exact ⟨state.rip, frame_writable4 pre.stack 172 (by decide) (by decide), frame_apart pre.stack 172 4 2592 7 (by decide) (by decide)⟩
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro _
      rw [state.rsp]
      exact saved_load_store state rfl 172 _ (by decide) (by unfold OffsetsApart; decide)
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 32 176 ?_ (fun _ => rfl) (text_inside 41022 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      change model.RIP = 1089591 ∧ MemWritable initial ((Operand.reg 4 : Operand 64).read model + 176) 4 ∧ RangeApart ((Operand.reg 4 : Operand 64).read model + 176) 4 1089591 7
      rw [state.rsp]
      exact ⟨state.rip, frame_writable4 pre.stack 176 (by decide) (by decide), frame_apart pre.stack 176 4 2599 7 (by decide) (by decide)⟩
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro _
      rw [state.rsp]
      exact saved_load_store state rfl 176 _ (by decide) (by unfold OffsetsApart; decide)
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 41025 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 32 40 ?_ (fun _ => rfl) (text_inside 41029 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      change model.RIP = 1089601 ∧ MemWritable initial ((Operand.reg 4 : Operand 64).read model + 40) 4 ∧ RangeApart ((Operand.reg 4 : Operand 64).read model + 40) 4 1089601 4
      rw [state.rsp]
      exact ⟨state.rip, frame_writable4 pre.stack 40 (by decide) (by decide), frame_apart pre.stack 40 4 2609 4 (by decide) (by decide)⟩
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro _
      rw [state.rsp]
      exact saved_load_store state rfl 40 _ (by decide) (by unfold OffsetsApart; decide)
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl) (text_inside 41032 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 32 140 ?_ (fun _ => rfl) (text_inside 41039 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      change model.RIP = 1089608 ∧ MemWritable initial ((Operand.reg 4 : Operand 64).read model + 140) 4 ∧ RangeApart ((Operand.reg 4 : Operand 64).read model + 140) 4 1089608 7
      rw [state.rsp]
      exact ⟨state.rip, frame_writable4 pre.stack 140 (by decide) (by decide), frame_apart pre.stack 140 4 2616 7 (by decide) (by decide)⟩
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro _
      rw [state.rsp]
      exact saved_load_store state rfl 140 _ (by decide) (by unfold OffsetsApart; decide)
  apply Certificate.cons
  · refine StepCertificate.of_register pre 13 ?_ (fun _ => rfl) (text_inside 41043 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 13 ?_ (fun _ => rfl) (text_inside 41046 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 41050 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1089622 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 64) 4
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 64 4 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 32 144 ?_ (fun _ => rfl) (text_inside 41057 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      change model.RIP = 1089626 ∧ MemWritable initial ((Operand.reg 4 : Operand 64).read model + 144) 4 ∧ RangeApart ((Operand.reg 4 : Operand 64).read model + 144) 4 1089626 7
      rw [state.rsp]
      exact ⟨state.rip, frame_writable4 pre.stack 144 (by decide) (by decide), frame_apart pre.stack 144 4 2634 7 (by decide) (by decide)⟩
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro _
      rw [state.rsp]
      exact saved_load_store state rfl 144 _ (by decide) (by unfold OffsetsApart; decide)
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 32 148 ?_ (fun _ => rfl) (text_inside 41064 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      change model.RIP = 1089633 ∧ MemWritable initial ((Operand.reg 4 : Operand 64).read model + 148) 4 ∧ RangeApart ((Operand.reg 4 : Operand 64).read model + 148) 4 1089633 7
      rw [state.rsp]
      exact ⟨state.rip, frame_writable4 pre.stack 148 (by decide) (by decide), frame_apart pre.stack 148 4 2641 7 (by decide) (by decide)⟩
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro _
      rw [state.rsp]
      exact saved_load_store state rfl 148 _ (by decide) (by unfold OffsetsApart; decide)
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 32 152 ?_ (fun _ => rfl) (text_inside 41071 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      change model.RIP = 1089640 ∧ MemWritable initial ((Operand.reg 4 : Operand 64).read model + 152) 4 ∧ RangeApart ((Operand.reg 4 : Operand 64).read model + 152) 4 1089640 7
      rw [state.rsp]
      exact ⟨state.rip, frame_writable4 pre.stack 152 (by decide) (by decide), frame_apart pre.stack 152 4 2648 7 (by decide) (by decide)⟩
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro _
      rw [state.rsp]
      exact saved_load_store state rfl 152 _ (by decide) (by unfold OffsetsApart; decide)
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 41074 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 41077 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 32 64 ?_ (fun _ => rfl) (text_inside 41081 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      change model.RIP = 1089653 ∧ MemWritable initial ((Operand.reg 4 : Operand 64).read model + 64) 4 ∧ RangeApart ((Operand.reg 4 : Operand 64).read model + 64) 4 1089653 4
      rw [state.rsp]
      exact ⟨state.rip, frame_writable4 pre.stack 64 (by decide) (by decide), frame_apart pre.stack 64 4 2661 4 (by decide) (by decide)⟩
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro _
      rw [state.rsp]
      exact saved_load_store state rfl 64 _ (by decide) (by unfold OffsetsApart; decide)
  apply Certificate.cons
  · refine StepCertificate.of_register pre 13 ?_ (fun _ => rfl) (text_inside 41084 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 32 4 ?_ (fun _ => rfl) (text_inside 41089 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      change model.RIP = 1089660 ∧ MemWritable initial ((Operand.reg 4 : Operand 64).read model + 4) 4 ∧ RangeApart ((Operand.reg 4 : Operand 64).read model + 4) 4 1089660 5
      rw [state.rsp]
      exact ⟨state.rip, frame_writable4 pre.stack 4 (by decide) (by decide), frame_apart pre.stack 4 4 2668 5 (by decide) (by decide)⟩
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro _
      rw [state.rsp]
      exact saved_load_store state rfl 4 _ (by decide) (by unfold OffsetsApart; decide)
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 41092 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 41094 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl) (text_inside 41099 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1089670 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 36) 4
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 36 4 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 41102 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 12 ?_ (fun _ => rfl) (text_inside 41105 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 10 ?_ (fun _ => rfl) (text_inside 41108 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 41110 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl) (text_inside 41113 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 5 ?_ (fun _ => rfl) (text_inside 41116 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 41118 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 32 36 ?_ (fun _ => rfl) (text_inside 41122 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      change model.RIP = 1089694 ∧ MemWritable initial ((Operand.reg 4 : Operand 64).read model + 36) 4 ∧ RangeApart ((Operand.reg 4 : Operand 64).read model + 36) 4 1089694 4
      rw [state.rsp]
      exact ⟨state.rip, frame_writable4 pre.stack 36 (by decide) (by decide), frame_apart pre.stack 36 4 2702 4 (by decide) (by decide)⟩
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro _
      rw [state.rsp]
      exact saved_load_store state rfl 36 _ (by decide) (by unfold OffsetsApart; decide)
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 41125 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 41127 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 41130 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1089703 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 0) 4
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 0 4 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 3 ?_ (fun _ => rfl) (text_inside 41132 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 64 72 ?_ (fun _ => rfl) (text_inside 41137 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      change model.RIP = 1089708 ∧ MemWritable initial ((Operand.reg 4 : Operand 64).read model + 72) 8 ∧ RangeApart ((Operand.reg 4 : Operand 64).read model + 72) 8 1089708 5
      rw [state.rsp]
      exact ⟨state.rip, frame_writable8 pre 72 (by decide) (by decide), frame_apart pre.stack 72 8 2716 5 (by decide) (by decide)⟩
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro _
      rw [state.rsp]
      exact saved_load_store state rfl 72 _ (by decide) (by unfold OffsetsApart; decide)
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 41139 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 32 16 ?_ (fun _ => rfl) (text_inside 41143 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      change model.RIP = 1089715 ∧ MemWritable initial ((Operand.reg 4 : Operand 64).read model + 16) 4 ∧ RangeApart ((Operand.reg 4 : Operand 64).read model + 16) 4 1089715 4
      rw [state.rsp]
      exact ⟨state.rip, frame_writable4 pre.stack 16 (by decide) (by decide), frame_apart pre.stack 16 4 2723 4 (by decide) (by decide)⟩
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro _
      rw [state.rsp]
      exact saved_load_store state rfl 16 _ (by decide) (by unfold OffsetsApart; decide)
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 41146 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 41149 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 41153 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1089725 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 52) 4
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 52 4 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 3 ?_ (fun _ => rfl) (text_inside 41158 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1089729 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 104) 8
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 104 8 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 3 ?_ (fun _ => rfl) (text_inside 41160 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 41162 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 32 100 ?_ (fun _ => rfl) (text_inside 41166 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      change model.RIP = 1089738 ∧ MemWritable initial ((Operand.reg 4 : Operand 64).read model + 100) 4 ∧ RangeApart ((Operand.reg 4 : Operand 64).read model + 100) 4 1089738 4
      rw [state.rsp]
      exact ⟨state.rip, frame_writable4 pre.stack 100 (by decide) (by decide), frame_apart pre.stack 100 4 2746 4 (by decide) (by decide)⟩
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro _
      rw [state.rsp]
      exact saved_load_store state rfl 100 _ (by decide) (by unfold OffsetsApart; decide)
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 41169 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 41172 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl) (text_inside 41177 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1089748 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 12) 4
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 12 4 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 41180 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  exact .nil _

end Hkdf.Proofs.Common.SHA256.Compression.Safety
