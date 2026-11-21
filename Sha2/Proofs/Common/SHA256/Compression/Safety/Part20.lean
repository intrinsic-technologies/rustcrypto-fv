import Sha2.Proofs.Common.SHA256.Compression.Safety.Steps
import Sha2.Proofs.Common.SHA256.Compression.Safety.Memory
import Sha2.Proofs.Common.SHA256.Compression.Safety.Positions
import Sha2.Proofs.Common.SHA256.Compression.Decoded.Part20

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Safety

open Sha2.Spec Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs

set_option maxRecDepth 4096 in
theorem part20 [Bindings] {initial : RamState} {hash : Array UInt32} {block : ByteArray}
    (pre : BlockPre initial hash block) :
    Certificate initial Decoded.part20 before20 after20 positions20 := by
  unfold Decoded.part20 before20 after20 positions20
  apply Certificate.cons
  · refine StepCertificate.of_register pre 12 ?_ (fun _ => rfl) (text_inside 50364 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 8 ?_ (fun _ => rfl) (text_inside 50367 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 50369 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 50372 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 50374 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 50377 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 50379 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 50382 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 50385 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 10 ?_ (fun _ => rfl) (text_inside 50388 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 10 ?_ (fun _ => rfl) (text_inside 50392 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 10 ?_ (fun _ => rfl) (text_inside 50395 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 50398 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 50401 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 50404 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 32 36 ?_ (fun _ => rfl) (text_inside 50408 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      change model.RIP = 1098980 ∧ MemWritable initial ((Operand.reg 4 : Operand 64).read model + 36) 4 ∧ RangeApart ((Operand.reg 4 : Operand 64).read model + 36) 4 1098980 4
      rw [state.rsp]
      exact ⟨state.rip, frame_writable4 pre.stack 36 (by decide) (by decide), frame_apart pre.stack 36 4 4020 4 (by decide) (by decide)⟩
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro _
      rw [state.rsp]
      exact saved_load_store state rfl 36 _ (by decide) (by unfold OffsetsApart; decide)
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 50410 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 32 20 ?_ (fun _ => rfl) (text_inside 50414 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      change model.RIP = 1098986 ∧ MemWritable initial ((Operand.reg 4 : Operand 64).read model + 20) 4 ∧ RangeApart ((Operand.reg 4 : Operand 64).read model + 20) 4 1098986 4
      rw [state.rsp]
      exact ⟨state.rip, frame_writable4 pre.stack 20 (by decide) (by decide), frame_apart pre.stack 20 4 4026 4 (by decide) (by decide)⟩
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro _
      rw [state.rsp]
      exact saved_load_store state rfl 20 _ (by decide) (by unfold OffsetsApart; decide)
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 50416 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 50419 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 50421 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 50425 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1098997 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 52) 4
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 52 4 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 50427 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 50430 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 50433 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 50436 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 50439 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 50441 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 50444 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 50447 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 50449 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 50452 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 50455 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 50458 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 50461 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 50463 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 50465 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 50468 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 50471 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 10 ?_ (fun _ => rfl) (text_inside 50475 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 10 ?_ (fun _ => rfl) (text_inside 50482 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 50485 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 50488 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 50490 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 50493 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 50496 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 50498 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl) (text_inside 50501 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl) (text_inside 50504 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 50506 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 50508 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 50511 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 50514 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 50516 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 13 ?_ (fun _ => rfl) (text_inside 50519 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl) (text_inside 50522 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl) (text_inside 50526 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 50529 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 50532 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 50535 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 50538 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 1 ?_ (fun _ => rfl) (text_inside 50541 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 10 ?_ (fun _ => rfl) (text_inside 50544 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 10 ?_ (fun _ => rfl) (text_inside 50548 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  exact .nil _

end Sha2.Proofs.Common.SHA256.Compression.Safety
