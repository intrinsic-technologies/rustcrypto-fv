import Sha2.Proofs.Wrapper.Variant
import Sha2.Proofs.Wrapper.State
import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Wrapper.Memory
import Sha2.Proofs.Common.Machine.StackRegion
import Sha2.Proofs.Common.Instructions.RepMovsq.Memory
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper

open Sha2.Spec Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

set_option maxRecDepth 2048 in
theorem copy_hash_buffer [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Input}
    (ctx : Context initial inputs v) (state : State initial s v)
    (rip : s.RIP = (v.pc 0x1bb)) (rsp : stackPtr s = stackPtr initial - 344) :
    ∃ t, State initial t v ∧ t.RIP = (v.pc 0x1ce) ∧ stackPtr t = stackPtr initial - 344 ∧
      (∀ i < 104, t.external[stackPtr initial - 344 + BitVec.ofNat 64 i]? =
        s.external[stackPtr initial - 152 + BitVec.ofNat 64 i]?) ∧
      AgreesExcept [.reg 1, .reg 6, .reg 7, .mem (stackPtr initial - 344) 104, .rip] s t := by
  obtain ⟨s1, run1, ready1, effect1⟩ :=
    (mov_r64_r64_effect_step (v.pc 0x1bb) 0x48 0xe7 (by simp [RexWPrefix]) (by cases v <;> decide)).advances
      (supportedMachine_readyToStep state.machine)
      (programText_slice (programLoaded_codeIn state.loaded) (v.textOffset + 0x1bb) [0x48, 0x89, 0xe7]
        (by cases v <;> decide) (by cases v <;> decide +kernel)) rip
      (by simpa only [movR64R64Effect, leaR64Effect, leaLen, immBytes_length, Nat.reduceDiv, AddrMode.tail, Disp.bytes, List.length_cons, List.length_nil, List.length_append, repMovsqEffect, movR32Imm32Effect, Variant.pc, BitVec.ofNat_add, BitVec.add_assoc, BitVec.reduceAdd] using boundary_ne_program (validCall_returnBoundary ctx.machine ctx.call).2.2 (Variant.pc_inProgram v (by decide : 0x1be < 1024)))
  change (movR64R64Effect (v.pc 0x1bb) 7 4 s).Holds s s1 at effect1
  have state1 := state.of_agrees ctx run1 ready1 effect1.agrees
    (by simp [WritesWithin, Component.Covers]) (by simp [Component.Covers])
  have rsp1 : stackPtr s1 = stackPtr initial - 344 :=
    (effect1.agrees.read (n := 64) (r := 4) (by simp)).trans rsp
  have rdi1 : s1.regValue .rdi = stackPtr initial - 344 := effect1.writes.trans rsp
  obtain ⟨s2, run2, ready2, effect2⟩ :=
    (lea_r64_effect_step (v.pc 0x1be) 0x48 (by simp [RexWPrefix]) 6
      (.sib 4 none 0 (.d32 192)) (by cases v <;> decide) rfl rfl).advances
      ready1 (programText_slice (programLoaded_codeIn state1.loaded) (v.textOffset + 0x1be)
        [0x48, 0x8d, 0xb4, 0x24, 0xc0, 0, 0, 0] (by cases v <;> decide) (by cases v <;> decide +kernel)) (by simpa only [movR64R64Effect, leaR64Effect, leaLen, immBytes_length, Nat.reduceDiv, AddrMode.tail, Disp.bytes, List.length_cons, List.length_nil, List.length_append, repMovsqEffect, movR32Imm32Effect, Variant.pc, BitVec.ofNat_add, BitVec.add_assoc, BitVec.reduceAdd] using effect1.rip)
      (by simpa only [movR64R64Effect, leaR64Effect, leaLen, immBytes_length, Nat.reduceDiv, AddrMode.tail, Disp.bytes, List.length_cons, List.length_nil, List.length_append, repMovsqEffect, movR32Imm32Effect, Variant.pc, BitVec.ofNat_add, BitVec.add_assoc, BitVec.reduceAdd] using boundary_ne_program (validCall_returnBoundary ctx.machine ctx.call).2.2 (Variant.pc_inProgram v (by decide : 0x1c6 < 1024)))
  change (leaR64Effect (v.pc 0x1be) 6 (.sib 4 none 0 (.d32 192)) s1).Holds s1 s2 at effect2
  have state2 := state1.of_agrees ctx run2 ready2 effect2.agrees
    (by simp [WritesWithin, Component.Covers]) (by simp [Component.Covers])
  have rsp2 : stackPtr s2 = stackPtr initial - 344 :=
    (effect2.agrees.read (n := 64) (r := 4) (by simp)).trans rsp1
  have rdi2 : s2.regValue .rdi = stackPtr initial - 344 :=
    (effect2.agrees.read (n := 64) (r := 7) (by simp)).trans rdi1
  have rsi2 : s2.regValue .rsi = stackPtr initial - 152 := by
    have hw : s2.regValue .rsi = stackPtr s1 + 192 := effect2.writes
    rw [hw, rsp1]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]
  obtain ⟨s3, run3, ready3, effect3⟩ :=
    (mov_r32_imm32_effect_step (v.pc 0x1c6) 0xb9 (by cases v <;> decide) 13).advances
      ready2 (programText_slice (programLoaded_codeIn state2.loaded) (v.textOffset + 0x1c6)
        [0xb9, 13, 0, 0, 0] (by cases v <;> decide) (by cases v <;> decide +kernel)) (by simpa only [movR64R64Effect, leaR64Effect, leaLen, immBytes_length, Nat.reduceDiv, AddrMode.tail, Disp.bytes, List.length_cons, List.length_nil, List.length_append, repMovsqEffect, movR32Imm32Effect, Variant.pc, BitVec.ofNat_add, BitVec.add_assoc, BitVec.reduceAdd] using effect2.rip)
      (by simpa only [movR64R64Effect, leaR64Effect, leaLen, immBytes_length, Nat.reduceDiv, AddrMode.tail, Disp.bytes, List.length_cons, List.length_nil, List.length_append, repMovsqEffect, movR32Imm32Effect, Variant.pc, BitVec.ofNat_add, BitVec.add_assoc, BitVec.reduceAdd] using boundary_ne_program (validCall_returnBoundary ctx.machine ctx.call).2.2 (Variant.pc_inProgram v (by decide : 0x1cb < 1024)))
  change (movR32Imm32Effect (v.pc 0x1c6) 5 1 13 s2).Holds s2 s3 at effect3
  have state3 := state2.of_agrees ctx run3 ready3 effect3.agrees
    (by simp [WritesWithin, Component.Covers]) (by simp [Component.Covers])
  have rsp3 : stackPtr s3 = stackPtr initial - 344 :=
    (effect3.agrees.read (n := 64) (r := 4) (by simp)).trans rsp2
  have rdi3 : s3.regValue .rdi = stackPtr initial - 344 :=
    (effect3.agrees.read (n := 64) (r := 7) (by simp)).trans rdi2
  have rsi3 : s3.regValue .rsi = stackPtr initial - 152 :=
    (effect3.agrees.read (n := 64) (r := 6) (by simp)).trans rsi2
  have count : (rcx.read s3).toNat = 13 := by
    have hw : s3.regValue .rcx = 13 := effect3.writes
    change (s3.regValue .rcx).toNat = 13
    rw [hw]
    rfl
  have readable (offset : Nat) (lo : offset ≤ 816) (hi : 104 ≤ offset + 8) :
      MemReadable s3 (stackPtr initial - BitVec.ofNat 64 offset) 104 := by
    have original := validCall_stack_sub_readable ctx.call lo hi
    exact ⟨original.low, fun i hi => state3.allocated _ (original.mem i hi)⟩
  have source : MemReadable s3 (rsi.read s3) 104 := by
    change MemReadable s3 (s3.regValue .rsi) 104
    rw [rsi3]
    exact readable 152 (by cases v <;> decide) (by cases v <;> decide)
  have destination : Common.Instructions.CrossPageStore.Writable s3 (rdi.read s3) 104 := by
    change Common.Instructions.CrossPageStore.Writable s3 (s3.regValue .rdi) 104
    rw [rdi3]
    have hr := readable 344 (by cases v <;> decide) (by cases v <;> decide)
    refine ⟨hr, ?_⟩
    apply tables_of_not_reserved (by cases v <;> decide) hr.low
    intro i hi reserved
    apply (ctx.call.separation.2 (Stack.region initial v.routine.minStackBytes) (by simp)).2 _ ?_ (.inr reserved)
    exact stackRegion_contains_sub ctx.call.stack.2.2.1 (offset := 344)
      (by cases v <;> decide) (by cases v <;> decide) ⟨i, hi, rfl⟩
  have bounds := validCall_stack_bounds ctx.call
  have destNat : (stackPtr initial - 344).toNat = (stackPtr initial).toNat - 344 :=
    validCall_stack_sub_toNat ctx.call (offset := 344) (by cases v <;> decide)
  have sourceNat : (stackPtr initial - 152).toNat = (stackPtr initial).toNat - 152 :=
    validCall_stack_sub_toNat ctx.call (offset := 152) (by cases v <;> decide)
  have apart : RangeApart (rdi.read s3) 104 (v.pc 0x1cb) 3 := by
    change RangeApart (s3.regValue .rdi) 104 _ _
    rw [rdi3]
    exact stack_codeApart ctx (by cases v <;> decide) (by cases v <;> decide) (show (v.textOffset + 0x1cb) + 3 ≤ 71757 by cases v <;> decide)
  have disjoint : (rsi.read s3).toNat + 104 ≤ (rdi.read s3).toNat ∨
      (rdi.read s3).toNat + 104 ≤ (rsi.read s3).toNat := by
    change (s3.regValue .rsi).toNat + 104 ≤ (s3.regValue .rdi).toNat ∨
      (s3.regValue .rdi).toNat + 104 ≤ (s3.regValue .rsi).toNat
    rw [rdi3, rsi3, destNat, sourceNat]
    right
    omega
  have pre := Common.Instructions.RepMovsq.pre_of_memory (by simpa only [movR64R64Effect, leaR64Effect, leaLen, immBytes_length, Nat.reduceDiv, AddrMode.tail, Disp.bytes, List.length_cons, List.length_nil, List.length_append, repMovsqEffect, movR32Imm32Effect, Variant.pc, BitVec.ofNat_add, BitVec.add_assoc, BitVec.reduceAdd] using effect3.rip)
    state3.directionFlag.df count source destination disjoint apart
  obtain ⟨run, ready, effect, copied⟩ :=
    Common.Instructions.RepMovsq.rep_movsq_execution ctx.stride ready3
      (programText_slice (programLoaded_codeIn state3.loaded) (v.textOffset + 0x1cb) [0xf3, 0x48, 0xa5]
        (by cases v <;> decide) (by cases v <;> decide +kernel)) pre count
      (by simpa only [movR64R64Effect, leaR64Effect, leaLen, immBytes_length, Nat.reduceDiv, AddrMode.tail, Disp.bytes, List.length_cons, List.length_nil, List.length_append, repMovsqEffect, movR32Imm32Effect, Variant.pc, BitVec.ofNat_add, BitVec.add_assoc, BitVec.reduceAdd] using boundary_ne_program (validCall_returnBoundary ctx.machine ctx.call).2.2 (Variant.pc_inProgram v (by decide : 0x1cb < 1024)))
      (by simpa only [movR64R64Effect, leaR64Effect, leaLen, immBytes_length, Nat.reduceDiv, AddrMode.tail, Disp.bytes, List.length_cons, List.length_nil, List.length_append, repMovsqEffect, movR32Imm32Effect, Variant.pc, BitVec.ofNat_add, BitVec.add_assoc, BitVec.reduceAdd] using boundary_ne_program (validCall_returnBoundary ctx.machine ctx.call).2.2 (Variant.pc_inProgram v (by decide : 0x1ce < 1024)))
  simp only [show max 13 1 = 13 from rfl] at run ready effect copied
  have frame : AgreesExcept [.reg 1, .reg 6, .reg 7,
      .mem (stackPtr initial - 344) 104, .rip] s3 (nextStates 13 s3) := by
    have repFrame : AgreesExcept [.reg 6, .reg 7, .reg 1,
        .mem (stackPtr initial - 344) 104, .rip] s3 (nextStates 13 s3) := by
      simpa only [repMovsqEffect_components, count,
        show rdi.read s3 = stackPtr initial - 344 from rdi3, Nat.reduceMul] using effect.agrees
    exact repFrame.mono (by simp)
  generalize finalEq : nextStates 13 s3 = t at run ready effect copied frame
  have writes : WritesWithin [.reg 1, .reg 6, .reg 7,
      .mem (stackPtr initial - 344) 104, .rip] #v[outputRegion v.routine initial, Stack.region initial v.routine.minStackBytes] := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> try exact ha.elim
    exact ⟨_, by simp, stackRegion_contains_sub ctx.call.stack.2.2.1 (by cases v <;> decide) (by cases v <;> decide) ha⟩
  have saved : ∀ c ∈ [Component.reg 1, .reg 6, .reg 7,
      .mem (stackPtr initial - 344) 104, .rip], ∀ a,
      (Component.mem (stackPtr initial - 48) 56).Covers a → ¬ c.Covers a := by
    intro c hc a ha hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> try exact hw.elim
    obtain ⟨i, hi, rfl⟩ := ha
    obtain ⟨j, hj, equal⟩ := hw
    exact OffsetsApart.ne (c₁ := -48) (len₁ := 56) (c₂ := -344) (len₂ := 104)
      (by unfold OffsetsApart; decide +kernel) (stackPtr initial) hi hj (by cases v <;> decide)
      (by simpa only [BitVec.sub_eq_add_neg] using equal)
  have setupFrame : AgreesExcept [.reg 1, .reg 6, .reg 7, .rip] s s3 :=
    ((effect1.agrees.trans effect2.agrees).trans effect3.agrees).mono (by simp)
  refine ⟨t, state3.of_agrees ctx run ready frame writes saved, (by simpa only [movR64R64Effect, leaR64Effect, leaLen, immBytes_length, Nat.reduceDiv, AddrMode.tail, Disp.bytes, List.length_cons, List.length_nil, List.length_append, repMovsqEffect, movR32Imm32Effect, Variant.pc, BitVec.ofNat_add, BitVec.add_assoc, BitVec.reduceAdd] using effect.rip),
    (frame.read (n := 64) (r := 4) (by simp)).trans rsp3, ?_,
    (setupFrame.trans frame).mono (by simp)⟩
  intro i hi
  have copy := copied i hi
  change t.external[s3.regValue .rdi + BitVec.ofNat 64 i]? =
    s3.external[s3.regValue .rsi + BitVec.ofNat 64 i]? at copy
  rw [rdi3, rsi3, setupFrame.external (by simp [Component.Covers])] at copy
  exact copy

end Sha2.Proofs.Wrapper
