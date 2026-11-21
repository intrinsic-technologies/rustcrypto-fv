import Sha2.Proofs.Common.SHA256.Compression.Safety.Steps
import Sha2.Proofs.Common.SHA256.Compression.Safety.Memory
import Sha2.Proofs.Common.SHA256.Compression.Safety.Positions
import Sha2.Proofs.Common.SHA256.Compression.Decoded.Part51

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Safety

open Sha2.Spec Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs

set_option maxRecDepth 4096 in
theorem part51 [Bindings] {initial : RamState} {hash : Array UInt32} {block : ByteArray}
    (pre : BlockPre initial hash block) :
    Certificate initial Decoded.part51 before51 after51 positions51 := by
  unfold Decoded.part51 before51 after51 positions51
  apply Certificate.cons
  · refine StepCertificate.of_register pre 5 ?_ (fun _ => rfl) (text_inside 56273 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 5 ?_ (fun _ => rfl) (text_inside 56275 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 3 ?_ (fun _ => rfl) (text_inside 56278 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 3 ?_ (fun _ => rfl) (text_inside 56281 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 14 ?_ (fun _ => rfl) (text_inside 56284 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 14 ?_ (fun _ => rfl) (text_inside 56287 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 14 ?_ (fun _ => rfl) (text_inside 56290 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 14 ?_ (fun _ => rfl) (text_inside 56293 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 14 ?_ (fun _ => rfl) (text_inside 56296 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 10 ?_ (fun _ => rfl) (text_inside 56299 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 14 ?_ (fun _ => rfl) (text_inside 56302 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 56305 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl) (text_inside 56308 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl) (text_inside 56311 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 3 ?_ (fun _ => rfl) (text_inside 56314 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 3 ?_ (fun _ => rfl) (text_inside 56317 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 3 ?_ (fun _ => rfl) (text_inside 56319 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 56322 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 56324 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl) (text_inside 56327 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl) (text_inside 56330 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 3 ?_ (fun _ => rfl) (text_inside 56333 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 3 ?_ (fun _ => rfl) (text_inside 56336 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 3 ?_ (fun _ => rfl) (text_inside 56338 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl) (text_inside 56341 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl) (text_inside 56344 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl) (text_inside 56346 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 3 ?_ (fun _ => rfl) (text_inside 56351 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1104922 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 40) 8
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 40 8 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 3 ?_ (fun _ => rfl) (text_inside 56353 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 3 ?_ (fun _ => rfl) (text_inside 56356 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 8 ?_ (fun _ => rfl) (text_inside 56359 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 8 ?_ (fun _ => rfl) (text_inside 56362 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 8 ?_ (fun _ => rfl) (text_inside 56365 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 8 ?_ (fun _ => rfl) (text_inside 56368 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 3 ?_ (fun _ => rfl) (text_inside 56371 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl) (text_inside 56373 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 7 ?_ (fun _ => rfl) (text_inside 56379 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 8 ?_ (fun _ => rfl) (text_inside 56382 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 8 ?_ (fun _ => rfl) (text_inside 56386 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 3 ?_ (fun _ => rfl) (text_inside 56389 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 3 ?_ (fun _ => rfl) (text_inside 56392 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 3 ?_ (fun _ => rfl) (text_inside 56395 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 8 ?_ (fun _ => rfl) (text_inside 56398 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 8 ?_ (fun _ => rfl) (text_inside 56402 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 8 ?_ (fun _ => rfl) (text_inside 56405 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 3 ?_ (fun _ => rfl) (text_inside 56407 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 3 ?_ (fun _ => rfl) (text_inside 56410 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 5 ?_ (fun _ => rfl) (text_inside 56412 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 5 ?_ (fun _ => rfl) (text_inside 56415 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 5 ?_ (fun _ => rfl) (text_inside 56418 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 5 ?_ (fun _ => rfl) (text_inside 56420 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 5 ?_ (fun _ => rfl) (text_inside 56427 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1104996 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 232) 4
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 232 4 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 5 ?_ (fun _ => rfl) (text_inside 56430 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 6 ?_ (fun _ => rfl) (text_inside 56435 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1105006 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 24) 8
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 24 8 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      apply Or.inl
      refine ⟨rfl, ?_⟩
      change (Operand.mem ((Operand.reg 4 : Operand 64).read model + 24) : Operand 64).read model = initial.regValue .rsi
      rw [state.rsp]
      exact state.saved rfl
  apply Certificate.cons
  · refine StepCertificate.of_register pre 14 ?_ (fun _ => rfl) (text_inside 56443 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1105011 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 248) 4
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 248 4 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by decide⟩
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 56450 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1105019 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 264) 4
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 264 4 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by decide⟩
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl) (text_inside 56458 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1105026 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 280) 4
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 280 4 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by decide⟩
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl) (text_inside 56466 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1105034 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 240) 4
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 240 4 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by decide⟩
  apply Certificate.cons
  · refine StepCertificate.of_register pre 3 ?_ (fun _ => rfl) (text_inside 56468 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by decide⟩
  apply Certificate.cons
  · refine StepCertificate.of_register pre 3 ?_ (fun _ => rfl) (text_inside 56470 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by decide⟩
  apply Certificate.cons
  · refine StepCertificate.of_register pre 8 ?_ (fun _ => rfl) (text_inside 56473 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by decide⟩
  apply Certificate.cons
  · refine StepCertificate.of_register pre 8 ?_ (fun _ => rfl) (text_inside 56476 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by decide⟩
  apply Certificate.cons
  · refine StepCertificate.of_register pre 10 ?_ (fun _ => rfl) (text_inside 56484 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1105052 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 256) 4
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 256 4 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by decide⟩
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 56491 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1105060 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 272) 4
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 272 4 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 6 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by decide⟩
  exact .nil _

end Sha2.Proofs.Common.SHA256.Compression.Safety
