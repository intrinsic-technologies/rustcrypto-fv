import Sha2.Proofs.Wrapper.Prologue.Header
import Sha2.Proofs.Wrapper.Prologue.Save

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Prologue

variable {v : Variant}

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

 theorem header_pre [Bindings] {initial s : RamState} {inputs : Array Input}
    (ctx : Context initial inputs v) (input : Result initial s v) : Header.Pre s v := by
  refine ⟨input.rip, ?_, ?_⟩
  · intro slot hs
    rw [stack_address input.rsp]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl
    all_goals simp only [BitVec.reduceSub]
    all_goals exact stack_writable8 ctx input.toState (by decide) (by decide)
  · intro slot hs offset len bound
    rw [stack_address input.rsp]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl
    all_goals simp only [BitVec.reduceSub]
    all_goals exact stack_codeApart ctx (by decide) (by decide) bound

 theorem header_frame [Bindings] {initial s t : RamState} (input : Result initial s v)
    (h : (Header.effect s v).Holds s t) :
    AgreesExcept [.mem (stackPtr initial - 176) 8, .mem (stackPtr initial - 160) 8,
      .mem (stackPtr initial - 168) 8, .rip] s t := by
  simpa only [Header.effect, Effect.components, List.map_cons, List.map_nil,
    Write.component, Operand.component, List.append_nil, List.cons_append,
    List.nil_append, stack_address input.rsp, BitVec.reduceSub, Nat.reduceDiv, BitVec.ofNat_eq_ofNat] using h.agrees

 theorem header [Bindings] {initial s : RamState} {inputs : Array Input}
    (ctx : Context initial inputs v) (input : Result initial s v) :
    ∃ t, Preserved initial t v ∧ t.RIP = (v.pc 0x29) ∧
      t.regValue .rsi = initial.regValue .rsi := by
  obtain ⟨fuel, t, execution, ready, _, effect⟩ := Header.run (returnBoundary initial)
    (validCall_returnBoundary ctx.machine ctx.call).2.2 s
    (supportedMachine_readyToStep input.machine) (Header.code input.loaded) (header_pre ctx input)
  have frame := header_frame input effect
  have state := input.toState.of_agrees ctx execution ready frame (by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals refine ⟨Stack.region initial v.routine.minStackBytes, by simp, ?_⟩
    all_goals exact stackRegion_contains_sub ctx.call.stack.2.2.1 (by dsimp only [Variant.routine]; decide) (by decide) ha) (by
    intro c hc a ha covered
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    all_goals obtain ⟨i, hi, rfl⟩ := ha
    all_goals obtain ⟨j, hj, he⟩ := covered
    · exact OffsetsApart.ne (c₁ := -48) (len₁ := 56) (c₂ := -176) (len₂ := 8)
        (by unfold OffsetsApart; decide +kernel) (stackPtr initial) hi hj (by decide)
        (by simpa only [BitVec.sub_eq_add_neg] using he)
    · exact OffsetsApart.ne (c₁ := -48) (len₁ := 56) (c₂ := -160) (len₂ := 8)
        (by unfold OffsetsApart; decide +kernel) (stackPtr initial) hi hj (by decide)
        (by simpa only [BitVec.sub_eq_add_neg] using he)
    · exact OffsetsApart.ne (c₁ := -48) (len₁ := 56) (c₂ := -168) (len₂ := 8)
        (by unfold OffsetsApart; decide +kernel) (stackPtr initial) hi hj (by decide)
        (by simpa only [BitVec.sub_eq_add_neg] using he))
  have stores := effect.writes
  change memLoad t.external (rspOf s + 168) 64 = s.regValue .rcx ∧
    memLoad t.external (rspOf s + 184) 64 = s.regValue .rdx ∧
    memLoad t.external (rspOf s + 176) 64 = s.regValue .rdi at stores
  simp only [stack_address input.rsp, BitVec.reduceSub] at stores
  refine ⟨t, ⟨state, (frame.read (n := 64) (r := 4) (by simp)).trans input.rsp,
    stores.1.trans (input.arguments .rcx (by simp)),
    stores.2.2.trans (input.arguments .rdi (by simp)),
    stores.2.1.trans (input.arguments .rdx (by simp))⟩, effect.rip, ?_⟩
  exact (frame.read (n := 64) (r := 6) (by simp)).trans (input.arguments .rsi (by simp))

end Sha2.Proofs.Wrapper.Prologue
