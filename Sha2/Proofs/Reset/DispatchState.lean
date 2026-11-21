import Sha2.Proofs.Reset.Prefix
import Sha2.Proofs.Reset.Dispatch
import Sha2.Proofs.Reset.Inputs
import Sha2.Proofs.Reset.Layouts
import Sha2.Proofs.Common.Encoding.Serialize.Convert.SavePointer

set_option autoImplicit false

namespace Sha2.Proofs.Reset

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA256
open Sha2.Proofs.Common.SHA256.Absorb Sha2.Proofs.Common.SHA256.Instances

private theorem dispatch_regions_avoid {routine : Routine} {initial : RamState} {inputs : Array Input}
    (call : TwoOutputs.ValidCall routine initial inputs) :
    ∀ region ∈ regions routine initial, region.Avoids InProgram := by
  intro region member a ha hp
  have mem : region ∈ [TwoOutputs.outputRegion routine initial,
      TwoOutputs.secondOutputRegion routine initial, Stack.region initial routine.minStackBytes] := by
    simpa only [regions, Vector.mem_mk, List.mem_toArray] using member
  exact (call.separation.2 region mem).2 a ha (.inl hp)

theorem dispatch_branch_state [bindings : Bindings] (v : Wrapper.Variant)
    {initial u : RamState} {inputs : Array Input}
    (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall (resetRoutine v) initial inputs)
    (state : ExecutionState initial u (regions (resetRoutine v) initial))
    (rip : u.RIP = Dispatch.entry v) :
    ∃ b, ExecutionState initial b (regions (resetRoutine v) initial) ∧
      (Dispatch.branchEffect (Dispatch.entry v) u).Holds u b := by
  obtain ⟨fuel, b, run, ready, _, result⟩ := Dispatch.branch (Dispatch.entry v) (displacement := 0x257)
    (returnBoundary initial) (valid_return_boundary machine call.stack call.returnAddress).2.2
    (fun i hi => Dispatch.inside v i (by omega)) (by simpa [BitVec.add_assoc] using Dispatch.inside v 608 (by decide))
    u (supportedMachine_readyToStep state.machine) (Dispatch.branch_code v state.loaded) rip
  refine ⟨b, state.of_agrees (dispatch_regions_avoid call) run ready result.agrees ?_ ?_, result⟩
  · intro c hc a ha
    simp [Dispatch.branchEffect, Effect.components, Component.Covers] at hc ha
    rcases hc with rfl | rfl <;> exact ha.elim
  · simp [Dispatch.branchEffect, Effect.components]

theorem dispatch_tail_state [bindings : Bindings] (v : Wrapper.Variant)
    {initial b : RamState} {inputs : Array Input}
    (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall (resetRoutine v) initial inputs)
    (state : ExecutionState initial b (regions (resetRoutine v) initial))
    (rsp : stackPtr b = stackPtr initial - 248#64)
    (rip : b.RIP = Dispatch.entry v + 9#64) :
    ∃ s, ExecutionState initial s (regions (resetRoutine v) initial) ∧
      (Dispatch.tailEffect (Dispatch.entry v + 9#64) b).Holds b s := by
  have stack : Stack.Valid initial 720 := by simpa only [resetRoutine_stack] using call.stack
  have avoid : (Stack.region initial 720).Avoids (fun a => InProgram a ∨ InPageTables a) := by
    simpa only [resetRoutine_stack, InPageTables] using
      (call.separation.2 _ (by simp [resetRoutine_stack])).2
  have inside : BlockInProgram (Dispatch.entry v + 9#64) 13 := by
    intro i hi
    have h := Dispatch.inside v (9+i) (by omega)
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using h
  have target : InProgram (Dispatch.entry v + 9#64 + 61#64) := by
    simpa [BitVec.add_assoc] using Dispatch.inside v 70 (by decide)
  have write : MemWritable b (rspOf b + 184#64) 8 := by
    rw [show rspOf b = stackPtr initial - 248#64 from rsp]
    exact stack_frame_writable stack (by decide) (fun a ha h => avoid a ha (.inr h))
      state.allocated (by decide) (by decide)
  have apart : RangeApart (rspOf b + 184#64) 8 (Dispatch.entry v + 9#64) 13 := by
    rw [show rspOf b = stackPtr initial - 248#64 from rsp]
    exact stack_frame_codeApart stack (by decide) (fun a ha h => avoid a ha (.inl h))
      (by decide) (fun j hj => inside j (Nat.le_of_lt hj))
  obtain ⟨fuel, s, run, ready, _, result⟩ := Dispatch.tail (Dispatch.entry v + 9#64)
    (returnBoundary initial) (valid_return_boundary machine call.stack call.returnAddress).2.2
    inside target b (supportedMachine_readyToStep state.machine) (Dispatch.tail_code v state.loaded)
    ⟨rip, write, apart⟩
  refine ⟨s, state.of_agrees (dispatch_regions_avoid call) run ready result.agrees ?_ ?_, result⟩
  · intro c hc a ha
    simp only [Dispatch.tailEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.cons_append, List.nil_append] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · refine ⟨Stack.region initial 720, by simp [regions, resetRoutine_stack], ?_⟩
      rw [show rspOf b = stackPtr initial - 248#64 from rsp] at ha
      exact stack_frame_contains stack (frame := 248) (offset := 184) (by decide) (by decide) ha
    all_goals exact ha.elim
  · simp [Dispatch.tailEffect, Effect.components]

set_option maxHeartbeats 800000 in
theorem dispatched [bindings : Bindings] (v : Wrapper.Variant)
    {initial : RamState} {inputs : Array Input}
    (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall (resetRoutine v) initial inputs) :
    ∃ p h u s,
      (Prologue.effect (resetRoutine v).entryAddress .six200 initial).Holds initial p ∧
      (Header.effect ((resetRoutine v).entryAddress + 17#64) p).Holds p h ∧
      Initialize.Post (Initialization.resetInitial.layout v) (rspOf h) h u ∧
      ExecutionState initial s (regions (resetRoutine v) initial) ∧
      Table.InputData (resetDiscarded v) ((resetDiscarded v).chunk.sp initial) inputs s ∧
      Table.Separation (resetDiscarded v) initial s 720 inputs ∧
      ((inputs.size = 0 ∧ s.RIP = Dispatch.entry v + 608#64 ∧
        stackPtr s = (resetDiscarded v).chunk.sp initial ∧
        HasherAt s ((resetDiscarded v).chunk.sp initial) ByteArray.empty v.initialHash ∧
        AgreesExcept [.flags, .rip] u s) ∨
       (Table.LoopState (resetDiscarded v) ((resetDiscarded v).chunk.sp initial) inputs 0 s ∧
        memLoad s.external ((resetDiscarded v).chunk.sp initial + 184#64) 64 =
          initial.regValue .rcx ∧
        AgreesExcept [.mem (rspOf u + 184#64) 8, .reg 15#5, .flags, .rip] u s)) := by
  obtain ⟨p, h, u, stateU, push, args, init, _, rspH, rspU⟩ := initialized v machine call
  obtain ⟨pointer, length, _, count, output⟩ := initialized_arguments push args init
  have sp : (resetDiscarded v).chunk.sp initial = rspOf u := by
    rw [show rspOf u = stackPtr initial - 248#64 from rspU]
    cases v <;> rfl
  have hasher : HasherAt u (rspOf u) ByteArray.empty v.initialHash := by
    rw [show rspOf u = rspOf h from init.rsp]
    exact init.hasher
  have rip : u.RIP = Dispatch.entry v := by
    rw [init.rip]
    cases v <;> decide +kernel
  obtain ⟨b, stateB, branch⟩ := dispatch_branch_state v machine call stateU rip
  have frameB : AgreesExcept [.flags, .rip] u b := branch.agrees
  have rspB : rspOf b = rspOf u := frameB.read (by simp)
  have countEq : u.regValue .r12 = BitVec.ofNat 64 inputs.size :=
    count.trans (by rw [← call.countArgumentMatchesInputs]; simp)
  have memB (a : BitVec 64) : b.external[a]? = u.external[a]? :=
    frameB.byte (by simp [Component.Covers])
  have ptrB : memLoad b.external (rspOf u + 168#64) 64 = initial.regValue .rdi := by
    rw [show memLoad b.external (rspOf u + 168#64) 64 =
        memLoad u.external (rspOf u + 168#64) 64 from
      Common.Encoding.Serialize.read_mem_of_agrees frameB _ (by simp [Component.Covers])]
    exact pointer
  have lenB : memLoad b.external (rspOf u + 176#64) 64 = initial.regValue .rdx := by
    rw [show memLoad b.external (rspOf u + 176#64) 64 =
        memLoad u.external (rspOf u + 176#64) 64 from
      Common.Encoding.Serialize.read_mem_of_agrees frameB _ (by simp [Component.Covers])]
    exact length
  by_cases empty : inputs.size = 0
  · have ripB : b.RIP = Dispatch.entry v + 608#64 := by
      have h : b.RIP = if u.regValue .r12 = 0#64 then Dispatch.entry v + 9#64 + 599#64
          else Dispatch.entry v + 9#64 := branch.rip
      simpa [countEq, empty, BitVec.add_assoc] using h
    have ptr : memLoad b.external ((resetDiscarded v).chunk.sp initial +
        BitVec.ofNat 64 (resetDiscarded v).pointerSlot) 64 = initial.regValue .rdi := by
      rw [sp]; exact ptrB
    have len : memLoad b.external ((resetDiscarded v).chunk.sp initial +
        BitVec.ofNat 64 (resetDiscarded v).lengthSlot) 64 = initial.regValue .rdx := by
      rw [sp]; exact lenB
    refine ⟨p, h, u, b, push, args, init, stateB, table_inputData call stateB.frame _ _ ptr len, ?_,
      Or.inl ⟨empty, ripB, ?_, ?_, frameB⟩⟩
    · simpa only [resetRoutine_stack] using table_separation call (resetDiscarded v) ptr len
    · rw [sp]; exact rspB
    · rw [sp]
      exact hasher.of_bytes (fun i _ => memB _)
  · have countBound := Wrapper.validCall_count_bound (firstOutput_validCall call)
    have nonzero : u.regValue .r12 ≠ 0#64 := by
      rw [countEq]
      intro eq
      have eqNat := congrArg BitVec.toNat eq
      simp only [BitVec.toNat_ofNat] at eqNat
      rw [Nat.mod_eq_of_lt (by omega)] at eqNat
      exact empty eqNat
    have ripB : b.RIP = Dispatch.entry v + 9#64 := by
      have h : b.RIP = if u.regValue .r12 = 0#64 then Dispatch.entry v + 9#64 + 599#64
          else Dispatch.entry v + 9#64 := branch.rip
      simp only [nonzero, ite_false] at h
      exact h
    obtain ⟨s, stateS, tail⟩ := dispatch_tail_state v machine call stateB (rspB.trans rspU) ripB
    have rspS : stackPtr s = rspOf u :=
      (tail.agrees.read (n := 64) (r := 4) (by simp [Dispatch.tailEffect, Effect.components])).trans rspB
    have byteS (i : Nat) (hi : i < 184) :
        s.external[rspOf u + BitVec.ofNat 64 i]? = u.external[rspOf u + BitVec.ofNat 64 i]? := by
      rw [← memB]
      apply tail.agrees.byte
      intro c hc covered
      simp only [Dispatch.tailEffect, Effect.components, List.map_cons, List.map_nil,
        Write.component, Operand.component, List.cons_append, List.nil_append] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · obtain ⟨j, hj, he⟩ := covered
        rw [rspB] at he
        exact OffsetsApart.ne (c₁ := 184) (len₁ := 8) (c₂ := 0) (len₂ := 184)
          (by unfold OffsetsApart; decide +kernel) (rspOf u) hj hi (by decide)
          (by
            change rspOf u + 184#64 + BitVec.ofNat 64 j =
              rspOf u + 0#64 + BitVec.ofNat 64 i
            rw [BitVec.add_zero]
            exact he.symm)
      all_goals exact covered.elim
    have wordS (offset : Nat) (bound : offset + 8 ≤ 184) :
        memLoad s.external (rspOf u + BitVec.ofNat 64 offset) 64 =
          memLoad u.external (rspOf u + BitVec.ofNat 64 offset) 64 := by
      apply memLoad_congr
      intro i hi
      change (s.external[_]?).getD 0 = (u.external[_]?).getD 0
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, byteS (offset+i) (by omega)]
    have ptr : memLoad s.external ((resetDiscarded v).chunk.sp initial +
        BitVec.ofNat 64 (resetDiscarded v).pointerSlot) 64 = initial.regValue .rdi := by
      rw [sp]
      exact (wordS 168 (by decide)).trans pointer
    have len : memLoad s.external ((resetDiscarded v).chunk.sp initial +
        BitVec.ofNat 64 (resetDiscarded v).lengthSlot) 64 = initial.regValue .rdx := by
      rw [sp]
      exact (wordS 176 (by decide)).trans length
    have writes : memLoad s.external (rspOf b + 184#64) 64 = b.regValue .r13 ∧
        s.regValue .r15 = 0 := tail.writes
    refine ⟨p, h, u, s, push, args, init, stateS, table_inputData call stateS.frame _ _ ptr len, ?_, Or.inr ⟨?_, ?_, ?_⟩⟩
    · simpa only [resetRoutine_stack] using table_separation call (resetDiscarded v) ptr len
    · refine ⟨?_, ?_, ?_, ?_, ?_, by omega, ?_, ?_, ?_, ?_⟩
      · rw [tail.rip]
        change Dispatch.entry v + 9#64 + 61#64 = (resetDiscarded v).head
        cases v <;> decide +kernel
      · rw [sp]; exact rspS
      · have preserved := hasher.of_bytes (fun i hi => byteS i (by omega))
        rw [Wrapper.prefixMessage_zero]
        simpa only [Table.Layout.stored, sp, show (resetDiscarded v).storedOffset = 0 from rfl,
          BitVec.add_zero, show (resetDiscarded v).chunk.initialHash = v.initialHash from rfl] using preserved
      · exact writes.2
      · change s.regValue .r12 = BitVec.ofNat 64 inputs.size
        exact (tail.agrees.read (n := 64) (r := 12)
          (by simp [Dispatch.tailEffect, Effect.components])).trans
          ((frameB.read (n := 64) (r := 12) (by simp)).trans countEq)
      · intro _ r hr
        change r ∈ (none : Option (BitVec 4)) at hr
        cases hr
      · intro r hr
        change r ∈ (none : Option (BitVec 4)) at hr
        cases hr
      · intro ne; exact (ne rfl).elim
      · intro call hc r he
        change call ∈ [(Absorption.Loop.resetDiscarded.chunk v).smallCall,
          (Absorption.Loop.resetDiscarded.chunk v).fillCall,
          (Absorption.Loop.resetDiscarded.chunk v).tailCall] at hc
        cases v <;> simp only [Absorption.Loop.chunk, List.mem_cons, List.not_mem_nil, or_false] at hc
        all_goals rcases hc with rfl | rfl | rfl <;> cases he
    · rw [sp, ← rspB, writes.1]
      exact (frameB.read (n := 64) (r := 13) (by simp)).trans output
    · apply (frameB.trans tail.agrees).mono
      simp [Dispatch.tailEffect, Effect.components, rspB]

end Sha2.Proofs.Reset
