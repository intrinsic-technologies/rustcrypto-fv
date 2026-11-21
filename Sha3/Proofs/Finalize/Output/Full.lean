import Sha3.Proofs.Finalize.Output.Blocks
import X86Proofs.Instructions.Mov.Triple

namespace Sha3.Proofs.Finalize.Output

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

attribute [local x86_compose] BitVec.add_zero BitVec.zero_add movR32Imm32Effect

def outputFullBytes : List UInt8 :=
  [0xba, 0xc8, 0, 0, 0, 0x4c, 0x89, 0xf7, 0x48, 0x89, 0xde]

def outputFullEffect (p ptr out : BitVec 64) (_s : RamState) : Effect where
  rip := p + 11
  writes := [⟨(Operand.reg 2 : Operand 64), 200⟩,
    ⟨(Operand.reg 7 : Operand 64), out⟩,
    ⟨(Operand.reg 6 : Operand 64), ptr⟩]

theorem outputFull_advance [Bindings] (p ptr out : BitVec 64) (boundary : ReturnBoundary)
    (code : CodeMap) (hcode : ∀ x ∈ codeRange p outputFullBytes, x ∈ code)
    (hboundary : ∀ offset : Nat, offset ≤ 11 →
      p + BitVec.ofNat 64 offset ≠ boundary.rip) :
    AdvanceTriple boundary 3 (OutputPre p ptr out 200 (.reg 14) code) code
      (Effect.post (outputFullEffect p ptr out)) := by
  refine AdvanceTriple.block_first ?k1
    (show StepEffect _ _ (movR32Imm32Effect p 5 2 200) from
      mov_r32_imm32_effect_step p 0xba (by decide +kernel) 200) ?sub ?pre ?av ?boundary
  case sub =>
    intro x hx
    exact hcode x (codeRange_mem_of_take (by decide +kernel) x hx)
  case pre => intro s hp; exact hp.rip
  case av =>
    intro s hp
    exact Effect.Avoids.of_noMem (by simp [movR32Imm32Effect, Effect.components,
      Write.component, Operand.component, Component.Covers]) _
  case boundary =>
    intros
    exact hboundary 5 (by decide)
  case' k1 => x86_norm
  refine AdvanceTriple.block_then ?k2
    (show StepEffect _ _ (movR64R64Effect (p + 5) 7 14) from
      mov_r64_r64_effect_step (p + 5) 0x4c 0xf7
        (by unfold RexWPrefix; decide +kernel) (by decide +kernel))
    ?loc ?sub ?full ?mid ?boundary
  case loc => x86_local
  case full => x86_full
  case sub =>
    intro x hx
    exact hcode x (codeRange_mem_of_drop 5 (by decide +kernel) x hx)
  case mid =>
    intro s t hp he ho
    refine ⟨he.rip, ?_⟩
    exact Effect.Avoids.of_noMem (by simp [movR64R64Effect, Effect.components,
      Write.component, Operand.component, Component.Covers]) _
  case boundary => intros; x86_norm; exact hboundary 8 (by decide)
  case' k2 => x86_norm
  refine AdvanceTriple.block_then ?k3
    (show StepEffect _ _ (movR64R64Effect (p + 8) 6 3) from
      mov_r64_r64_effect_step (p + 8) 0x48 0xde
        (by unfold RexWPrefix; decide +kernel) (by decide +kernel))
    ?loc ?sub ?full ?mid ?boundary
  case loc => x86_local
  case full => x86_full
  case sub =>
    intro x hx
    exact hcode x (codeRange_mem_of_drop 8 (by decide +kernel) x hx)
  case mid =>
    intro s t hp he ho
    refine ⟨?_, ?_⟩
    · simpa only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using he.rip
    · exact Effect.Avoids.of_noMem (by simp [movR64R64Effect, Effect.components,
        Write.component, Operand.component, Component.Covers]) _
  case boundary => intros; x86_norm; exact hboundary 11 (by decide)
  case' k3 => x86_norm
  apply AdvanceTriple.block_end
  intro s t hp he
  have hstate := hp.state
  have hout := hp.pointer
  x86_norm at hstate hout
  apply he.weaken
  · x86_norm [outputFullEffect]
  · x86_norm [outputFullEffect, hstate, hout]
  · intro i; cases i <;> x86_norm [outputFullEffect]
  · x86_norm [outputFullEffect, hstate, hout]

end Sha3.Proofs.Finalize.Output
