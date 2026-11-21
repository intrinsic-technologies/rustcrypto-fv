import Sha2.Proofs.Common.SHA256.Compression.Safety.Steps
import Sha2.Proofs.Common.SHA256.Compression.Safety.Memory
import Sha2.Proofs.Common.SHA256.Compression.Safety.Positions
import Sha2.Proofs.Common.SHA256.Compression.Decoded.Part03

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Safety

open Sha2.Spec Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs

set_option maxRecDepth 4096 in
theorem part03 [Bindings] {initial : RamState} {hash : Array UInt32} {block : ByteArray}
    (pre : BlockPre initial hash block) :
    Certificate initial Decoded.part03 before03 after03 positions03 := by
  unfold Decoded.part03 before03 after03 positions03
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl) (text_inside 47015 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1095586 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 24) 8
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 24 8 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 9 := List.mem_singleton.mp hr
      subst r
      apply Or.inl
      refine ⟨rfl, ?_⟩
      change (Operand.mem ((Operand.reg 4 : Operand 64).read model + 24) : Operand 64).read model = initial.regValue .rsi
      rw [state.rsp]
      exact state.saved rfl
  apply Certificate.cons
  · refine StepCertificate.of_register pre 5 ?_ (fun _ => rfl) (text_inside 47019 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1095591 ∧ MemReadable initial ((Operand.reg 9 : Operand 64).read model + 16) 4
      rw [state.pointers 9 (by decide)]
      exact ⟨state.rip, Sha2.Proofs.Common.Memory.memReadable_sub pre.inputReadable 16 4 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 9 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by decide⟩
  apply Certificate.cons
  · refine StepCertificate.of_register pre 5 ?_ (fun _ => rfl) (text_inside 47021 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 9 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by decide⟩
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 32 36 ?_ (fun _ => rfl) (text_inside 47025 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      change model.RIP = 1095597 ∧ MemWritable initial ((Operand.reg 4 : Operand 64).read model + 36) 4 ∧ RangeApart ((Operand.reg 4 : Operand 64).read model + 36) 4 1095597 4
      rw [state.rsp]
      exact ⟨state.rip, frame_writable4 pre.stack 36 (by decide) (by decide), frame_apart pre.stack 36 4 637 4 (by decide) (by decide)⟩
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro _
      rw [state.rsp]
      exact saved_load_store state rfl 36 _ (by decide) (by unfold OffsetsApart; decide)
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl) (text_inside 47028 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl) (text_inside 47031 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 47033 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 47036 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl) (text_inside 47039 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl) (text_inside 47042 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl) (text_inside 47045 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 47048 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 47051 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 47057 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl) (text_inside 47060 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl) (text_inside 47064 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl) (text_inside 47067 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl) (text_inside 47071 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl) (text_inside 47074 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 5 ?_ (fun _ => rfl) (text_inside 47076 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 5 ?_ (fun _ => rfl) (text_inside 47079 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 5 ?_ (fun _ => rfl) (text_inside 47082 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl) (text_inside 47085 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl) (text_inside 47088 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl) (text_inside 47091 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl) (text_inside 47094 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl) (text_inside 47097 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl) (text_inside 47100 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl) (text_inside 47103 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 0 ?_ (fun _ => rfl) (text_inside 47105 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 9 ?_ (fun _ => rfl) (text_inside 47108 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 47110 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 47113 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl) (text_inside 47116 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl) (text_inside 47120 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl) (text_inside 47123 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 47125 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 47128 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 47131 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl) (text_inside 47136 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1095707 ∧ MemReadable initial ((Operand.reg 4 : Operand 64).read model + 24) 8
      rw [state.rsp]
      exact ⟨state.rip, frame_readable pre.stack 24 8 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 11 := List.mem_singleton.mp hr
      subst r
      apply Or.inl
      refine ⟨rfl, ?_⟩
      change (Operand.mem ((Operand.reg 4 : Operand 64).read model + 24) : Operand 64).read model = initial.regValue .rsi
      rw [state.rsp]
      exact state.saved rfl
  apply Certificate.cons
  · refine StepCertificate.of_register pre 5 ?_ (fun _ => rfl) (text_inside 47140 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      change model.RIP = 1095712 ∧ MemReadable initial ((Operand.reg 11 : Operand 64).read model + 20) 4
      rw [state.pointers 11 (by decide)]
      exact ⟨state.rip, Sha2.Proofs.Common.Memory.memReadable_sub pre.inputReadable 20 4 (by decide)⟩
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 11 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by decide⟩
  apply Certificate.cons
  · refine StepCertificate.of_register pre 5 ?_ (fun _ => rfl) (text_inside 47142 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      intro r hr
      have eq : r = 11 := List.mem_singleton.mp hr
      subst r
      exact Or.inr ⟨by decide, by decide⟩
  apply Certificate.cons
  · refine StepCertificate.of_memory pre 32 64 ?_ (fun _ => rfl) (text_inside 47146 (by decide)) (by decide) ?_ (fun _ h => h)
    · intro model state
      change model.RIP = 1095718 ∧ MemWritable initial ((Operand.reg 4 : Operand 64).read model + 64) 4 ∧ RangeApart ((Operand.reg 4 : Operand 64).read model + 64) 4 1095718 4
      rw [state.rsp]
      exact ⟨state.rip, frame_writable4 pre.stack 64 (by decide) (by decide), frame_apart pre.stack 64 4 758 4 (by decide) (by decide)⟩
    · intro model state
      rw [← state.rsp]
      refine ⟨_, rfl, ?_⟩
      intro _
      rw [state.rsp]
      exact saved_load_store state rfl 64 _ (by decide) (by unfold OffsetsApart; decide)
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl) (text_inside 47149 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl) (text_inside 47152 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 8 ?_ (fun _ => rfl) (text_inside 47155 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 8 ?_ (fun _ => rfl) (text_inside 47158 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl) (text_inside 47161 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl) (text_inside 47164 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl) (text_inside 47167 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 8 ?_ (fun _ => rfl) (text_inside 47170 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl) (text_inside 47173 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl) (text_inside 47177 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 47180 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 2 ?_ (fun _ => rfl) (text_inside 47186 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 8 ?_ (fun _ => rfl) (text_inside 47189 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 8 ?_ (fun _ => rfl) (text_inside 47193 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 8 ?_ (fun _ => rfl) (text_inside 47196 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl) (text_inside 47199 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl) (text_inside 47203 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 11 ?_ (fun _ => rfl) (text_inside 47206 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 5 ?_ (fun _ => rfl) (text_inside 47208 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 5 ?_ (fun _ => rfl) (text_inside 47210 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  apply Certificate.cons
  · refine StepCertificate.of_register pre 8 ?_ (fun _ => rfl) (text_inside 47213 (by decide)) (by simp [blockComponents]) (by decide) (fun h => h) ?_
    · intro model state
      exact state.rip
    · intro model state
      refine ⟨_, rfl, ?_⟩
      simp
  exact .nil _

end Sha2.Proofs.Common.SHA256.Compression.Safety
