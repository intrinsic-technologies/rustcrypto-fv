import Hkdf.Proofs.Common.SHA256.Compression.Safety.Steps
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Memory
import Hkdf.Proofs.Common.SHA256.Compression.Safety.Positions
import Hkdf.Proofs.Common.SHA256.Compression.Decoded.Part14

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Safety

open Hkdf.Spec Hkdf.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs

set_option maxRecDepth 4096 in
theorem part14 [Bindings] {initial : RamState} {hash : Array UInt32} {block : ByteArray}
    (pre : BlockPre initial hash block) :
    Certificate initial Decoded.part14 before14 after14 positions14 := by
  unfold Decoded.part14 before14 after14 positions14
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 32 136 ?_ (fun _ => rfl) (text_inside 41187 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      change model.RIP = 1089756 ∧ MemWritable initial ((Operand.reg 4 : Operand 64).read model + 136) 4 ∧ RangeApart ((Operand.reg 4 : Operand 64).read model + 136) 4 1089756 7
      rw [state.rsp]
      exact ⟨state.rip, frame_writable4 pre.stack 136 (by decide) (by decide), frame_apart pre.stack 136 4 2764 7 (by decide) (by decide)⟩
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro _
      rw [state.rsp]
      exact saved_load_store state rfl 136 _ (by decide) (by unfold OffsetsApart; decide)
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl) (text_inside 41191 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl) (text_inside 41199 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1089767 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 156) 4
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 156 4 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 41203 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1089775 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 8) 4
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 8 4 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl) (text_inside 41206 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 32 0 ?_ (fun _ => rfl) (text_inside 41210 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      change model.RIP = 1089782 ∧ MemWritable initial ((Operand.reg 4 : Operand 64).read model + 0) 4 ∧ RangeApart ((Operand.reg 4 : Operand 64).read model + 0) 4 1089782 4
      rw [state.rsp]
      exact ⟨state.rip, frame_writable4 pre.stack 0 (by decide) (by decide), frame_apart pre.stack 0 4 2790 4 (by decide) (by decide)⟩
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro _
      rw [state.rsp]
      exact saved_load_store state rfl 0 _ (by decide) (by unfold OffsetsApart; decide)
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 41213 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 41220 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1089789 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 160) 4
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 160 4 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 41224 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1089796 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 96) 4
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 96 4 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 41226 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 32 52 ?_ (fun _ => rfl) (text_inside 41230 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      change model.RIP = 1089802 ∧ MemWritable initial ((Operand.reg 4 : Operand 64).read model + 52) 4 ∧ RangeApart ((Operand.reg 4 : Operand 64).read model + 52) 4 1089802 4
      rw [state.rsp]
      exact ⟨state.rip, frame_writable4 pre.stack 52 (by decide) (by decide), frame_apart pre.stack 52 4 2810 4 (by decide) (by decide)⟩
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro _
      rw [state.rsp]
      exact saved_load_store state rfl 52 _ (by decide) (by unfold OffsetsApart; decide)
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 41232 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 41235 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 41242 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1089811 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 164) 4
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 164 4 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl) (text_inside 41245 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl) (text_inside 41250 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1089821 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 56) 8
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 56 8 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 41252 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 41255 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 41257 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 41260 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 41262 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 41264 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 41267 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 41269 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl) (text_inside 41274 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1089845 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 20) 4
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 20 4 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl) (text_inside 41277 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 32 96 ?_ (fun _ => rfl) (text_inside 41282 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      change model.RIP = 1089853 ∧ MemWritable initial ((Operand.reg 4 : Operand 64).read model + 96) 4 ∧ RangeApart ((Operand.reg 4 : Operand 64).read model + 96) 4 1089853 5
      rw [state.rsp]
      exact ⟨state.rip, frame_writable4 pre.stack 96 (by decide) (by decide), frame_apart pre.stack 96 4 2861 5 (by decide) (by decide)⟩
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro _
      rw [state.rsp]
      exact saved_load_store state rfl 96 _ (by decide) (by unfold OffsetsApart; decide)
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 41285 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 32 12 ?_ (fun _ => rfl) (text_inside 41289 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      change model.RIP = 1089861 ∧ MemWritable initial ((Operand.reg 4 : Operand 64).read model + 12) 4 ∧ RangeApart ((Operand.reg 4 : Operand 64).read model + 12) 4 1089861 4
      rw [state.rsp]
      exact ⟨state.rip, frame_writable4 pre.stack 12 (by decide) (by decide), frame_apart pre.stack 12 4 2869 4 (by decide) (by decide)⟩
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro _
      rw [state.rsp]
      exact saved_load_store state rfl 12 _ (by decide) (by unfold OffsetsApart; decide)
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 41292 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 41295 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 41302 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1089871 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 180) 4
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 180 4 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl) (text_inside 41307 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1089878 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 88) 8
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 88 8 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 41310 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 41313 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 8 ?_ (fun _ => rfl) (text_inside 41316 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 8 ?_ (fun _ => rfl) (text_inside 41324 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1089892 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 184) 4
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 184 4 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 41327 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 41330 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 8 ?_ (fun _ => rfl) (text_inside 41333 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 41336 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 41339 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 41341 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 41343 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 3 ?_ (fun _ => rfl) (text_inside 41351 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1089919 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 224) 8
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 224 8 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 41353 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 41361 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1089929 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 128) 8
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 128 8 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 41363 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 41366 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 41368 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 15 ?_ (fun _ => rfl) (text_inside 41371 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 15 ?_ (fun _ => rfl) (text_inside 41374 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 41378 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 41383 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl) (text_inside 41391 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1089959 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 208) 8
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 208 8 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 41394 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 41397 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 41400 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 41403 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 41405 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 41408 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 41411 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 41413 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 41418 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1089989 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 112) 8
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 112 8 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  exact .nil _

end Hkdf.Proofs.Common.SHA256.Compression.Safety
