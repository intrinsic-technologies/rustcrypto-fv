import Sha2.Proofs.Reset.Prefix
import Sha2.Proofs.Reset.Dispatch

set_option autoImplicit false

namespace Sha2.Proofs.Reset.FinalizePrefix

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA256
open Sha2.Proofs.Common.SHA256.Absorb Sha2.Proofs.Common.SHA256.Instances
open Sha2.Proofs.Common.SHA256.Instances.Absorption

abbrev routine (v : Wrapper.Variant) := Header.Layout.finalize.routine v

theorem routine_stack (v : Wrapper.Variant) : (routine v).minStackBytes = 832 := by cases v <;> rfl

def entryOffset : Wrapper.Variant → Nat
  | .sha224 => 0x6c9
  | .sha256 => 0x22d9

def entry (v : Wrapper.Variant) : BitVec 64 := Extracted.textAddress + BitVec.ofNat 64 (entryOffset v)

theorem inside (v : Wrapper.Variant) : BlockInProgram (entry v) 294 :=
  blockInProgram_of_textOffset (entryOffset v) 294 (by cases v <;> decide +kernel)

theorem branch_code (v : Wrapper.Variant) {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (entry v) (Dispatch.branchBytes 0x11d 6)) s :=
  programText_slice (programLoaded_codeIn loaded) (entryOffset v) _
    (by cases v <;> decide +kernel) (by cases v <;> decide +kernel)

theorem tail_code (v : Wrapper.Variant) {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (entry v + 9) (Dispatch.tailBytes 296 6 41)) s := by
  have h := programText_slice (programLoaded_codeIn loaded) (entryOffset v + 9)
    (Dispatch.tailBytes 296 6 41) (by cases v <;> decide +kernel) (by cases v <;> decide +kernel)
  simpa [entry, BitVec.ofNat_add, BitVec.add_assoc] using h

private theorem regions_avoid {initial : RamState} {inputs : Array Input} {v : Wrapper.Variant}
    (call : TwoOutputs.ValidCall (routine v) initial inputs) :
    ∀ region ∈ regions (routine v) initial, region.Avoids InProgram := by
  intro region member a ha hp
  have mem : region ∈ [TwoOutputs.outputRegion (routine v) initial,
      TwoOutputs.secondOutputRegion (routine v) initial, Stack.region initial (routine v).minStackBytes] := by
    simpa only [regions, Vector.mem_mk, List.mem_toArray] using member
  exact (call.separation.2 region mem).2 a ha (.inl hp)

theorem tail_state [bindings : Bindings] (v : Wrapper.Variant)
    {initial b : RamState} {inputs : Array Input}
    (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall (routine v) initial inputs)
    (state : ExecutionState initial b (regions (routine v) initial))
    (rsp : stackPtr b = stackPtr initial - 360#64)
    (rip : b.RIP = entry v + 9#64) :
    ∃ s, ExecutionState initial s (regions (routine v) initial) ∧
      (Dispatch.tailEffect (entry v + 9#64) b 296 6 41).Holds b s := by
  have stack : Stack.Valid initial 832 := by simpa only [routine_stack] using call.stack
  have avoid : (Stack.region initial 832).Avoids (fun a => InProgram a ∨ InPageTables a) := by
    simpa only [routine_stack, InPageTables] using
      (call.separation.2 _ (by simp [routine_stack])).2
  have inside : BlockInProgram (entry v + 9#64) 13 := by
    intro i hi
    have h := inside v (9+i) (by omega)
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using h
  have target : InProgram (entry v + 9#64 + (13 + (41#8).signExtend 64)) := by
    simpa [BitVec.add_assoc] using FinalizePrefix.inside v 63 (by decide)
  have write : MemWritable b (rspOf b + 296#64) 8 := by
    rw [show rspOf b = stackPtr initial - 360#64 from rsp]
    exact stack_frame_writable stack (by decide) (fun a ha h => avoid a ha (.inr h))
      state.allocated (by decide) (by decide)
  have apart : RangeApart (rspOf b + 296#64) 8 (entry v + 9#64) 13 := by
    rw [show rspOf b = stackPtr initial - 360#64 from rsp]
    exact stack_frame_codeApart stack (by decide) (fun a ha h => avoid a ha (.inl h))
      (by decide) (fun j hj => inside j (Nat.le_of_lt hj))
  obtain ⟨fuel, s, run, ready, _, result⟩ := Dispatch.tailAt (entry v + 9#64)
    (returnBoundary initial) (valid_return_boundary machine call.stack call.returnAddress).2.2
    inside 41 target 296 6 b (supportedMachine_readyToStep state.machine) (tail_code v state.loaded)
    ⟨rip, write, apart⟩
  refine ⟨s, state.of_agrees (regions_avoid call) run ready result.agrees ?_ ?_, result⟩
  · intro c hc a ha
    simp only [Dispatch.tailEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.cons_append, List.nil_append] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · refine ⟨Stack.region initial 832, by simp [regions, routine_stack], ?_⟩
      rw [show rspOf b = stackPtr initial - 360#64 from rsp] at ha
      exact stack_frame_contains stack (frame := 360) (offset := 296) (by decide) (by decide) ha
    all_goals exact ha.elim
  · simp [Dispatch.tailEffect, Effect.components]

set_option maxHeartbeats 800000 in
theorem dispatched [bindings : Bindings] (v : Wrapper.Variant)
    {initial : RamState} {inputs : Array Input}
    (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall (routine v) initial inputs) :
    ∃ p h u s,
      (Prologue.effect (routine v).entryAddress .six312 initial).Holds initial p ∧
      (Header.effectAt .finalize (Header.Layout.finalize.pc v) p).Holds p h ∧
      Initialize.Post (Initialization.finalizeInitial.layout v) (rspOf h + 8#64) h u ∧
      ExecutionState initial s (regions (routine v) initial) ∧
      Table.InputData (finalizeFirstTable v) ((finalizeFirstTable v).chunk.sp initial) inputs s ∧
      Table.Separation (finalizeFirstTable v) initial s 832 inputs ∧
      stackPtr s = stackPtr initial - 360#64 ∧
      memLoad s.external ((finalizeFirstTable v).chunk.sp initial + 216#64) 64 = initial.regValue .rdi ∧
      memLoad s.external ((finalizeFirstTable v).chunk.sp initial + 224#64) 64 = initial.regValue .rdx ∧
      memLoad s.external ((finalizeFirstTable v).chunk.sp initial + 304#64) 64 = initial.regValue .r8 ∧
      s.regValue .r15 = BitVec.ofNat 64 inputs.size ∧
      ((inputs.size = 0 ∧ s.RIP = entry v + 294#64 ∧
        stackPtr s = (finalizeFirstTable v).chunk.sp initial ∧
        HasherAt s ((finalizeFirstTable v).chunk.sp initial + 8#64) ByteArray.empty v.initialHash ∧
        s.regValue .r13 = initial.regValue .rcx ∧ AgreesExcept [.flags, .rip] u s) ∨
       (Table.LoopState (finalizeFirstTable v) ((finalizeFirstTable v).chunk.sp initial) inputs 0 s ∧
        memLoad s.external ((finalizeFirstTable v).chunk.sp initial + 296#64) 64 =
          initial.regValue .rcx ∧
        AgreesExcept [.mem (rspOf u + 296#64) 8, .reg 14#5, .flags, .rip] u s)) := by
  obtain ⟨p, h, u, stateU, push, args, init, _, rspH, rspU⟩ := initialized_at .finalize v machine call
  obtain ⟨pointer, length, output2, count, output, rsi⟩ := initialized_arguments_at push args init
  have sp : (finalizeFirstTable v).chunk.sp initial = rspOf u := by
    rw [show rspOf u = stackPtr initial - 360#64 from rspU]
    cases v <;> rfl
  have hasher : HasherAt u (rspOf u + 8#64) ByteArray.empty v.initialHash := by
    rw [show rspOf u = rspOf h from init.rsp]
    exact init.hasher
  have rip : u.RIP = entry v := by
    rw [init.rip]
    cases v <;> decide +kernel
  obtain ⟨b, stateB, branch⟩ := branch_state machine call stateU rip
    (branch_code v stateU.loaded) (fun i hi => inside v i (by omega))
    (by simpa [BitVec.add_assoc] using inside v 294 (by decide))
  have frameB : AgreesExcept [.flags, .rip] u b := branch.agrees
  have rspB : rspOf b = rspOf u := frameB.read (by simp)
  have countEq : u.regValue .r15 = BitVec.ofNat 64 inputs.size :=
    count.trans (by rw [← call.countArgumentMatchesInputs]; simp)
  have testEq : u.regValue .rsi = BitVec.ofNat 64 inputs.size := (rsi (by decide)).trans (by rw [← call.countArgumentMatchesInputs]; simp)
  have memB (a : BitVec 64) : b.external[a]? = u.external[a]? :=
    frameB.byte (by simp [Component.Covers])
  have ptrB : memLoad b.external (rspOf u + 216#64) 64 = initial.regValue .rdi := by
    rw [show memLoad b.external (rspOf u + 216#64) 64 =
        memLoad u.external (rspOf u + 216#64) 64 from
      Common.Encoding.Serialize.read_mem_of_agrees frameB _ (by simp [Component.Covers])]
    exact pointer
  have lenB : memLoad b.external (rspOf u + 224#64) 64 = initial.regValue .rdx := by
    rw [show memLoad b.external (rspOf u + 224#64) 64 =
        memLoad u.external (rspOf u + 224#64) 64 from
      Common.Encoding.Serialize.read_mem_of_agrees frameB _ (by simp [Component.Covers])]
    exact length
  have out2B : memLoad b.external (rspOf u + 304#64) 64 = initial.regValue .r8 := by
    exact (Common.Encoding.Serialize.read_mem_of_agrees frameB (rspOf u + 304#64) (by simp [Component.Covers])).trans output2
  have countB : b.regValue .r15 = BitVec.ofNat 64 inputs.size :=
    (frameB.read (n := 64) (r := 15) (by simp)).trans countEq
  by_cases empty : inputs.size = 0
  · have ripB : b.RIP = entry v + 294#64 := by
      have h : b.RIP = if u.regValue .rsi = 0#64 then entry v + 9#64 + 285#64
          else entry v + 9#64 := branch.rip
      simpa [testEq, empty, BitVec.add_assoc] using h
    have ptr : memLoad b.external ((finalizeFirstTable v).chunk.sp initial +
        BitVec.ofNat 64 (finalizeFirstTable v).pointerSlot) 64 = initial.regValue .rdi := by
      rw [sp]; exact ptrB
    have len : memLoad b.external ((finalizeFirstTable v).chunk.sp initial +
        BitVec.ofNat 64 (finalizeFirstTable v).lengthSlot) 64 = initial.regValue .rdx := by
      rw [sp]; exact lenB
    refine ⟨p, h, u, b, push, args, init, stateB, table_inputData call stateB.frame _ _ ptr len, ?_,
      (rspB.trans rspU), ?_, ?_, ?_, countB, Or.inl ⟨empty, ripB, ?_, ?_, ?_, frameB⟩⟩
    · simpa only [routine_stack] using table_separation call (finalizeFirstTable v) ptr len
    · rw [sp]; exact ptrB
    · rw [sp]; exact lenB
    · rw [sp]; exact out2B
    · rw [sp]; exact rspB
    · rw [sp]
      exact hasher.of_bytes (fun i _ => memB _)
    · exact (frameB.read (n := 64) (r := 13) (by simp)).trans output
  · have countBound := Wrapper.validCall_count_bound (firstOutput_validCall call)
    have nonzero : u.regValue .rsi ≠ 0#64 := by
      rw [testEq]
      intro eq
      have eqNat := congrArg BitVec.toNat eq
      simp only [BitVec.toNat_ofNat] at eqNat
      rw [Nat.mod_eq_of_lt (by omega)] at eqNat
      exact empty eqNat
    have ripB : b.RIP = entry v + 9#64 := by
      have h : b.RIP = if u.regValue .rsi = 0#64 then entry v + 9#64 + 285#64
          else entry v + 9#64 := branch.rip
      simp only [nonzero, ite_false] at h
      exact h
    obtain ⟨s, stateS, tail⟩ := tail_state v machine call stateB (rspB.trans rspU) ripB
    have rspS : stackPtr s = rspOf u :=
      (tail.agrees.read (n := 64) (r := 4) (by simp [Dispatch.tailEffect, Effect.components])).trans rspB
    have byteS (i : Nat) (hi : i < 296) :
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
        exact OffsetsApart.ne (c₁ := 296) (len₁ := 8) (c₂ := 0) (len₂ := 296)
          (by unfold OffsetsApart; decide +kernel) (rspOf u) hj hi (by decide)
          (by
            change rspOf u + 296#64 + BitVec.ofNat 64 j =
              rspOf u + 0#64 + BitVec.ofNat 64 i
            rw [BitVec.add_zero]
            exact he.symm)
      all_goals exact covered.elim
    have wordS (offset : Nat) (bound : offset + 8 ≤ 296) :
        memLoad s.external (rspOf u + BitVec.ofNat 64 offset) 64 =
          memLoad u.external (rspOf u + BitVec.ofNat 64 offset) 64 := by
      apply memLoad_congr
      intro i hi
      change (s.external[_]?).getD 0 = (u.external[_]?).getD 0
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, byteS (offset+i) (by omega)]
    have ptr : memLoad s.external ((finalizeFirstTable v).chunk.sp initial +
        BitVec.ofNat 64 (finalizeFirstTable v).pointerSlot) 64 = initial.regValue .rdi := by
      rw [sp]
      exact (wordS 216 (by decide)).trans pointer
    have len : memLoad s.external ((finalizeFirstTable v).chunk.sp initial +
        BitVec.ofNat 64 (finalizeFirstTable v).lengthSlot) 64 = initial.regValue .rdx := by
      rw [sp]
      exact (wordS 224 (by decide)).trans length
    have out2S : memLoad s.external (rspOf u + 304#64) 64 = initial.regValue .r8 := by
      apply Eq.trans (Common.Encoding.Serialize.read_mem_of_agrees tail.agrees (rspOf u + 304#64) ?_) out2B
      intro i hi c hc covered
      simp only [Dispatch.tailEffect, Effect.components, List.map_cons, List.map_nil,
        Write.component, Operand.component, List.cons_append, List.nil_append] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · obtain ⟨j,hj,he⟩ := covered
        rw [rspB] at he
        exact OffsetsApart.ne (c₁ := 296) (c₂ := 304) (by unfold OffsetsApart; decide +kernel)
          (rspOf u) hj hi (by decide) he.symm
      all_goals exact covered.elim
    have countS : s.regValue .r15 = BitVec.ofNat 64 inputs.size :=
      (tail.agrees.read (n := 64) (r := 15)
        (by simp [Dispatch.tailEffect, Effect.components])).trans countB
    have writes : memLoad s.external (rspOf b + 296#64) 64 = b.regValue .r13 ∧
        s.regValue .r14 = 0 := tail.writes
    refine ⟨p, h, u, s, push, args, init, stateS, table_inputData call stateS.frame _ _ ptr len, ?_, (rspS.trans rspU), ?_, ?_, ?_, ?_, Or.inr ⟨?_, ?_, ?_⟩⟩
    · simpa only [routine_stack] using table_separation call (finalizeFirstTable v) ptr len
    · exact ptr
    · exact len
    · rw [sp]; exact out2S
    · exact countS
    · refine ⟨?_, ?_, ?_, ?_, ?_, by omega, ?_, ?_, ?_, ?_⟩
      · rw [tail.rip]
        change entry v + 9#64 + (13 + (41#8).signExtend 64) = (finalizeFirstTable v).head
        cases v <;> decide +kernel
      · rw [sp]; exact rspS
      · have preserved : HasherAt s (rspOf u + 8#64) ByteArray.empty v.initialHash := hasher.of_bytes (fun i hi => by
        simpa only [BitVec.add_assoc, ← BitVec.ofNat_add] using byteS (8+i) (by omega))
        rw [Wrapper.prefixMessage_zero]
        simpa only [Table.Layout.stored, sp, show (finalizeFirstTable v).storedOffset = 8 from rfl,
          BitVec.add_zero, show (finalizeFirstTable v).chunk.initialHash = v.initialHash from rfl] using preserved
      · exact writes.2
      · change s.regValue .r15 = BitVec.ofNat 64 inputs.size
        exact (tail.agrees.read (n := 64) (r := 15)
          (by simp [Dispatch.tailEffect, Effect.components])).trans
          ((frameB.read (n := 64) (r := 15) (by simp)).trans countEq)
      · intro _ r hr
        change r ∈ (none : Option (BitVec 4)) at hr
        cases hr
      · intro r hr
        change r ∈ (none : Option (BitVec 4)) at hr
        cases hr
      · intro ne; exact (ne rfl).elim
      · intro call hc r he
        change call ∈ [(Absorption.Loop.finalizeFirst.chunk v).smallCall,
          (Absorption.Loop.finalizeFirst.chunk v).fillCall,
          (Absorption.Loop.finalizeFirst.chunk v).tailCall] at hc
        cases v <;> simp only [Absorption.Loop.chunk, List.mem_cons, List.not_mem_nil, or_false] at hc
        all_goals rcases hc with rfl | rfl | rfl <;> cases he
    · rw [sp, ← rspB, writes.1]
      exact (frameB.read (n := 64) (r := 13) (by simp)).trans output
    · apply (frameB.trans tail.agrees).mono
      simp [Dispatch.tailEffect, Effect.components, rspB]

theorem dispatched_saved {v : Wrapper.Variant} {initial p h u s : RamState}
    (push : (Prologue.effect (Header.Layout.finalize.routine v).entryAddress .six312 initial).Holds initial p)
    (args : (Header.effectAt .finalize (Header.Layout.finalize.pc v) p).Holds p h)
    (init : Initialize.Post (Initialization.finalizeInitial.layout v) (rspOf h + 8#64) h u)
    (rsp : rspOf s = rspOf u)
    (frame : AgreesExcept [.mem (rspOf u + 296#64) 8, .reg 14#5, .flags, .rip] u s) :
    (∀ (r : BitVec 5) (offset : Nat),
      (r, offset) ∈ [(3,0),(12,8),(13,16),(14,24),(15,32),(5,40)] →
      memLoad s.external (rspOf s + BitVec.ofNat 64 (312 + offset)) 64 =
        (Operand.reg r : Operand 64).read initial) ∧
    memLoad s.external (rspOf s + 360#64) 64 = memLoad initial.external (stackPtr initial) 64 := by
  apply initialized_abi_after .finalize push args init rsp frame
  intro c hc a covered
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · obtain ⟨i,hi,he⟩ := covered
    refine ⟨296+i, ?_, ?_⟩
    · change 296+i < 312
      omega
    · simpa only [BitVec.ofNat_add, BitVec.add_assoc] using he
  all_goals exact covered.elim

end Sha2.Proofs.Reset.FinalizePrefix
