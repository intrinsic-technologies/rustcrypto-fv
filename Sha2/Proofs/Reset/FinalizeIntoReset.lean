import Sha2.Proofs.Reset.Last
import Sha2.Proofs.Reset.FinalizePrefix
import Sha2.Proofs.Reset.NormalizeState
import Sha2.Proofs.Reset.Absorb
import Sha2.Proofs.Common.SHA256.Instances.Absorb.Stages
import Sha2.Proofs.Common.SHA256.Instances.Absorb.Contracts
import Sha2.Proofs.Reset.Finalize
import Sha2.Proofs.Reset.Second
import Sha2.Proofs.Common.SHA256.Instances.Digest.Clone

set_option autoImplicit false

namespace Sha2.Proofs.Reset.FinalizeIntoReset

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA256
open Sha2.Proofs.Common.SHA256.Absorb Sha2.Proofs.Common.SHA256.Instances
open Sha2.Proofs.Common.SHA256.Instances.Absorption

def routine (v : Wrapper.Variant) : Routine := Header.Layout.finalize.routine v

theorem routine_stack (v : Wrapper.Variant) : (routine v).minStackBytes = 832 := by
  cases v <;> rfl

theorem traversed [bindings : Bindings] (v : Wrapper.Variant) (last : Bool)
    {initial s : RamState} {inputs : Array Input}
    (stride : UnitStringStride bindings) (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall (routine v) initial inputs)
    (state : ExecutionState initial s (regions (routine v) initial))
    (loop : Table.LoopState (if last then finalizeLastTable v else finalizeFirstTable v)
      (stackPtr initial - 360#64) inputs 0 s)
    (data : Table.InputData (if last then finalizeLastTable v else finalizeFirstTable v)
      (stackPtr initial - 360#64) inputs s)
    (separation : Table.Separation (if last then finalizeLastTable v else finalizeFirstTable v)
      initial s 832 inputs) :
    ∃ t, Table.Finished (if last then finalizeLastTable v else finalizeFirstTable v)
      initial s t (regions (routine v) initial) inputs := by
  have stack : Stack.Valid initial 832 := by simpa only [routine_stack] using call.stack
  have avoid : (Stack.region initial 832).Avoids
      (fun a => InProgram a ∨ InPageTables a) := by
    simpa only [routine_stack, InPageTables] using (call.separation.2 _ (by simp [routine_stack])).2
  have outside := (valid_return_boundary machine stack call.returnAddress).2.2
  cases last
  all_goals simp only [Bool.false_eq_true, ite_false, ite_true] at loop data separation ⊢
  all_goals
    apply Table.correct _
    all_goals first
      | exact finalizeFirstTable_wellFormed v
      | exact finalizeLastTable_wellFormed v
      | exact finalizeFirstTable_flow v
      | exact finalizeLastTable_flow v
      | exact finalizeFirstTable_chunkCodeFacts v
      | exact finalizeLastTable_chunkCodeFacts v
      | exact finalizeFirstTable_callTargets v
      | exact finalizeLastTable_callTargets v
      | exact Loop.blockContracts .finalizeFirst v _ stride outside
      | exact Loop.blockContracts .finalizeLast v _ stride outside
      | exact Absorb.correct _
      | exact finalizeFirstTable_codeFacts v
      | exact finalizeLastTable_codeFacts v
      | exact finalizeFirstTable_tableBlocks v _ stride outside
      | exact finalizeLastTable_tableBlocks v _ stride outside
      | exact stride
      | exact machine
      | exact stack
      | exact avoid
      | exact call.returnAddress
      | exact state
      | exact loop
      | exact data
      | exact separation
      | exact ⟨fun _ impossible => by cases impossible⟩
      | skip
  all_goals
    intro region member address inside
    refine ⟨Stack.region initial 832, by simp [regions, routine_stack], ?_⟩
    first
    | exact Table.footprint_subset_stack (finalizeFirstTable_wellFormed v) stack region member address inside
    | exact Table.footprint_subset_stack (finalizeLastTable_wellFormed v) stack region member address inside

def secondEntry (v : Wrapper.Variant) : BitVec 64 :=
  if v = .sha224 then 0x1009e9 else 0x102605

def secondTailBytes (v : Wrapper.Variant) : List UInt8 :=
  [0x45, 0x31, 0xf6, 0x4c, 0x8d, 0x25] ++
    (if v = .sha224 then [0x64, 0xd3, 0, 0] else [0x48, 0xb7, 0, 0]) ++
    [0xeb, if v = .sha224 then 0x24 else 0x28]

def secondTailEffect (v : Wrapper.Variant) (_ : RamState) : Effect :=
  { rip := (finalizeLastTable v).head
    writes := [⟨(.reg 14 : Operand 64), 0⟩, ⟨(.reg 12 : Operand 64), 0x10dd60⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem second_inside (v : Wrapper.Variant) : BlockInProgram (secondEntry v) 272 := by
  cases v
  · exact blockInProgram_of_textOffset 0x9e9 272 (by decide +kernel)
  · exact blockInProgram_of_textOffset 0x2605 272 (by decide +kernel)

theorem second_tail_run [Bindings] (v : Wrapper.Variant) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = secondEntry v + 9#64)
      (codeRange (secondEntry v + 9#64) (secondTailBytes v))
      (Effect.post (secondTailEffect v)) := by
  have within (n : Nat) (hn : n ≤ 263) : InProgram (secondEntry v + 9#64 + BitVec.ofNat 64 n) := by
    have h := second_inside v (9+n) (by omega)
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using h
  have target : InProgram (finalizeLastTable v).head := (finalizeLastTable_codeFacts v).2.1
  have low : (branchTarget (secondEntry v + 9#64 + 10#64) 2
      ((if v = .sha224 then 36 else 40 : BitVec 8).signExtend 64)).toNat < 2^32 := by
    cases v <;> decide +kernel
  advance_reloc_begin (StepEffect.forgetFlags (h := xor_r32_r32_rex_effect_step
    (secondEntry v + 9#64) 0x45 0xf6 (by simp [RexNoWPrefix]) rfl))
    next (by simpa [BitVec.add_assoc] using boundary_ne_program outside (within 3 (by decide)))
  advance_reloc_then (lea_r64_effect_step (secondEntry v + 9#64 + 3#64) 0x4c
    (by simp [RexWPrefix]) 4 (.rip (if v = .sha224 then 0xd364 else 0xb748))
    (by cases v <;> decide) rfl rfl)
    next (by simpa [BitVec.add_assoc] using boundary_ne_program outside (within 10 (by decide)))
  advance_reloc_then (jmp_rel8_effect_step (secondEntry v + 9#64 + 10#64)
    (if v = .sha224 then 36 else 40) low)
    next (by
      have eq : secondEntry v + (21#64 + (if v = .sha224 then 36#8 else 40#8).signExtend 64) =
          (finalizeLastTable v).head := by cases v <;> decide +kernel
      rw [eq]
      exact boundary_ne_program outside target)
  apply AdvanceTriple.block_end
  intro s t _ h
  apply h.weaken
  · cases v <;> x86_norm [secondTailEffect, secondEntry, finalizeLastTable]
  · x86_norm [secondTailEffect]
    constructor
    · change 0#64 = ((Operand.read s (.reg 14 : Operand 32)) ^^^
        (Operand.read s (.reg 14 : Operand 32))).setWidth 64
      simp
    · cases v <;> decide +kernel
  · intro i; cases i <;> x86_norm [secondTailEffect]
  · x86_norm [secondTailEffect]
  all_goals cases v <;> x86_sub

private theorem slot_readable {initial s : RamState}
    (stack : Stack.Valid initial 832)
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome)
    {slot : Nat} (bound : slot ≤ 360) :
    MemReadable s (stackPtr initial - 360#64 + BitVec.ofNat 64 slot) 8 := by
  rw [stack_frame_address initial bound]
  exact Common.Encoding.Serialize.readable_of_grow
    (stack_valid_sub_readable stack (by omega) (by omega)) grow

private theorem slot_local {initial : RamState} (stack : Stack.Valid initial 832)
    {slot offset len : Nat} (bound : slot ≤ 360) (endBound : offset + len ≤ slot) :
    (⟨(stackPtr initial - 360#64 + BitVec.ofNat 64 slot).toNat, 8⟩ : MemoryRegion).Disjoint
      ⟨(stackPtr initial - 360#64 + BitVec.ofNat 64 offset).toNat, len⟩ := by
  intro a ha hb
  change _ ≤ a ∧ a < _ at ha hb
  dsimp only at ha hb
  rw [stack_frame_toNat stack (by decide) bound] at ha
  rw [stack_frame_toNat stack (by decide) (by omega)] at hb
  omega

private theorem slot_below {initial : RamState} (stack : Stack.Valid initial 832)
    {slot : Nat} (bound : slot ≤ 360) :
    (⟨(stackPtr initial - 360#64 + BitVec.ofNat 64 slot).toNat, 8⟩ : MemoryRegion).Disjoint
      ⟨(stackPtr initial - 360#64 - 344#64).toNat, 344⟩ := by
  intro a ha hb
  change _ ≤ a ∧ a < _ at ha hb
  dsimp only at ha hb
  rw [stack_frame_toNat stack (by decide) bound] at ha
  rw [stack_frame_below_toNat stack (by decide : 360 + 344 ≤ 832)] at hb
  have bounds := stack_valid_bounds stack
  omega

theorem table_saved [Bindings] {v : Wrapper.Variant} {initial s t : RamState}
    {inputs : Array Input} (last : Bool)
    (call : TwoOutputs.ValidCall (routine v) initial inputs)
    (state : ExecutionState initial s (regions (routine v) initial))
    (finished : Table.Finished (if last then finalizeLastTable v else finalizeFirstTable v)
      initial s t (regions (routine v) initial) inputs)
    (slot : Nat) (low : 112 ≤ slot) (bound : slot ≤ 360) :
    memLoad t.external (stackPtr initial - 360#64 + BitVec.ofNat 64 slot) 64 =
      memLoad s.external (stackPtr initial - 360#64 + BitVec.ofNat 64 slot) 64 := by
  have stack : Stack.Valid initial 832 := by simpa only [routine_stack] using call.stack
  apply Table.memLoad_of_frame finished.memory (slot_readable stack state.allocated bound)
  intro region member
  cases last
  all_goals
    change region ∈ #v[⟨(stackPtr initial - 360#64 + 8#64).toNat, 104⟩,
      ⟨(stackPtr initial - 360#64 + 8#64).toNat, 104⟩,
      ⟨(stackPtr initial - 360#64 - 344#64).toNat, 344⟩] at member
    simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact slot_local stack bound (by omega : 8 + 104 ≤ slot)
    · exact slot_local stack bound (by omega : 8 + 104 ≤ slot)
    · exact slot_below stack bound

theorem finalized_saved [Bindings] {v : Wrapper.Variant} {initial s t : RamState}
    {inputs : Array Input} {message : ByteArray} (last : Bool)
    (call : TwoOutputs.ValidCall (routine v) initial inputs)
    (state : ExecutionState initial s (regions (routine v) initial))
    (finished : Finalize.Finalized ((if last then Finalization.finalizeLast else .finalizeFirst).layout v)
      initial s t (regions (routine v) initial) message)
    (slot : Nat) (low : (if last then 296 else 176) ≤ slot) (bound : slot ≤ 360) :
    memLoad t.external (stackPtr initial - 360#64 + BitVec.ofNat 64 slot) 64 =
      memLoad s.external (stackPtr initial - 360#64 + BitVec.ofNat 64 slot) 64 := by
  have stack : Stack.Valid initial 832 := by simpa only [routine_stack] using call.stack
  apply Table.memLoad_of_frame finished.frame.memory (slot_readable stack state.allocated bound)
  intro region member
  cases last
  · change region ∈ #v[⟨(stackPtr initial - 360#64 + 8#64).toNat, 64⟩,
      ⟨(stackPtr initial - 360#64 + 8#64 + 64#64).toNat, 32⟩,
      ⟨(stackPtr initial - 360#64 + 112#64).toNat, 64⟩,
      ⟨(stackPtr initial - 360#64 - 344#64).toNat, 344⟩] at member
    simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact slot_local stack bound (by simp only [Bool.false_eq_true, ite_false] at low; omega : 8 + 64 ≤ slot)
    · simpa only [BitVec.add_assoc, show (8#64 + 64#64) = 72#64 from rfl] using slot_local stack bound
        (by simp only [Bool.false_eq_true, ite_false] at low; omega : 72 + 32 ≤ slot)
    · exact slot_local stack bound (by simp only [Bool.false_eq_true, ite_false] at low; omega : 112 + 64 ≤ slot)
    · exact slot_below stack bound
  · change region ∈ #v[⟨(stackPtr initial - 360#64 + 112#64).toNat, 64⟩,
      ⟨(stackPtr initial - 360#64 + 112#64 + 64#64).toNat, 32⟩,
      ⟨(stackPtr initial - 360#64 + 232#64).toNat, 64⟩,
      ⟨(stackPtr initial - 360#64 - 344#64).toNat, 344⟩] at member
    simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact slot_local stack bound (by simp only [ite_true] at low; omega : 112 + 64 ≤ slot)
    · simpa only [BitVec.add_assoc, show (112#64 + 64#64) = 176#64 from rfl] using slot_local stack bound
        (by simp only [ite_true] at low; omega : 176 + 32 ≤ slot)
    · exact slot_local stack bound (by simp only [ite_true] at low; omega : 232 + 64 ≤ slot)
    · exact slot_below stack bound

theorem second_tail_code (v : Wrapper.Variant) {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (secondEntry v + 9#64) (secondTailBytes v)) s := by
  have pc : secondEntry v + 9#64 = Extracted.textAddress +
      BitVec.ofNat 64 (if v = .sha224 then 0x9f2 else 0x260e) := by
    cases v <;> decide +kernel
  rw [pc]
  exact programText_slice (programLoaded_codeIn loaded) _ _
    (by cases v <;> decide +kernel) (by cases v <;> decide +kernel)

private theorem regions_avoid {initial : RamState} {inputs : Array Input} {v : Wrapper.Variant}
    (call : TwoOutputs.ValidCall (routine v) initial inputs) :
    ∀ region ∈ regions (routine v) initial, region.Avoids InProgram := by
  intro region member a ha hp
  have mem : region ∈ [TwoOutputs.outputRegion (routine v) initial,
      TwoOutputs.secondOutputRegion (routine v) initial, Stack.region initial (routine v).minStackBytes] := by
    simpa only [regions, Vector.mem_mk, List.mem_toArray] using member
  exact (call.separation.2 region mem).2 a ha (.inl hp)

theorem second_tail_ready [bindings : Bindings] (v : Wrapper.Variant)
    {initial s : RamState} {inputs : Array Input}
    (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall (routine v) initial inputs)
    (state : ExecutionState initial s (regions (routine v) initial))
    (rsp : rspOf s = stackPtr initial - 360#64)
    (rip : s.RIP = secondEntry v + 9#64)
    (hasher : HasherAt s (rspOf s + 8#64) ByteArray.empty v.initialHash)
    (count : s.regValue .r15 = BitVec.ofNat 64 inputs.size)
    (positive : 0 < inputs.size)
    (pointer : memLoad s.external (rspOf s + 216#64) 64 = initial.regValue .rdi)
    (length : memLoad s.external (rspOf s + 224#64) 64 = initial.regValue .rdx) :
    ∃ t, ExecutionState initial t (regions (routine v) initial) ∧
      Table.LoopState (finalizeLastTable v) (stackPtr initial - 360#64) inputs 0 t ∧
      Table.InputData (finalizeLastTable v) (stackPtr initial - 360#64) inputs t ∧
      Table.Separation (finalizeLastTable v) initial t 832 inputs ∧
      rspOf t = rspOf s ∧ t.external = s.external := by
  obtain ⟨fuel, t, run, ready, _, result⟩ := second_tail_run v (returnBoundary initial)
    (valid_return_boundary machine call.stack call.returnAddress).2.2 s
    (supportedMachine_readyToStep state.machine) (second_tail_code v state.loaded) rip
  have nomem : ∀ c ∈ (secondTailEffect v s).components, ∀ a, ¬ c.Covers a := by
    simp [secondTailEffect, Effect.components, Component.Covers]
  have stateT := state.of_agrees (regions_avoid call) run ready result.agrees
    (fun c hc a ha => (nomem c hc a ha).elim) (by simp [secondTailEffect, Effect.components])
  have memory := result.agrees.external nomem
  have rspT : rspOf t = rspOf s := result.agrees.read (n := 64) (r := 4)
    (by simp [secondTailEffect, Effect.components])
  have ptr : memLoad t.external ((finalizeLastTable v).chunk.sp initial +
      BitVec.ofNat 64 (finalizeLastTable v).pointerSlot) 64 = initial.regValue .rdi := by
    change memLoad t.external (stackPtr initial - 360#64 + 216#64) 64 = _
    rw [memory, ← rsp]; exact pointer
  have len : memLoad t.external ((finalizeLastTable v).chunk.sp initial +
      BitVec.ofNat 64 (finalizeLastTable v).lengthSlot) 64 = initial.regValue .rdx := by
    change memLoad t.external (stackPtr initial - 360#64 + 224#64) 64 = _
    rw [memory, ← rsp]; exact length
  have writes : t.regValue .r14 = 0#64 ∧ t.regValue .r12 = 0x10dd60#64 := result.writes
  refine ⟨t, stateT, ?_, table_inputData call stateT.frame _ _ ptr len, ?_, rspT, memory⟩
  · refine ⟨result.rip, rspT.trans rsp, ?_, writes.1, ?_, positive, ?_, ?_, ?_, ?_⟩
    · rw [Wrapper.prefixMessage_zero]
      change HasherAt t (stackPtr initial - 360#64 + 8#64) ByteArray.empty v.initialHash
      rw [← rsp]
      exact hasher.of_bytes (fun _ _ => by rw [memory])
    · exact (result.agrees.read (n := 64) (r := 15)
        (by simp [secondTailEffect, Effect.components])).trans count
    · intro _ r hr; change r ∈ (none : Option (BitVec 4)) at hr; cases hr
    · intro r hr; change r ∈ (none : Option (BitVec 4)) at hr; cases hr
    · intro ne; exact (ne rfl).elim
    · intro call hc r he
      change call ∈ [(Absorption.Loop.finalizeLast.chunk v).smallCall,
        (Absorption.Loop.finalizeLast.chunk v).fillCall,
        (Absorption.Loop.finalizeLast.chunk v).tailCall] at hc
      cases v <;> simp only [Absorption.Loop.chunk, List.mem_cons, List.not_mem_nil, or_false] at hc
      all_goals rcases hc with rfl | rfl | rfl <;> cases he
      all_goals exact writes.2
  · simpa only [routine_stack] using table_separation call (finalizeLastTable v) ptr len

def secondDisplacement (v : Wrapper.Variant) : BitVec 32 := if v = .sha224 then 0xf6 else 0xfa

theorem second_branch_code (v : Wrapper.Variant) {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (secondEntry v) (Dispatch.branchBytes (secondDisplacement v) 15)) s := by
  have pc : secondEntry v = Extracted.textAddress +
      BitVec.ofNat 64 (if v = .sha224 then 0x9e9 else 0x2605) := by
    cases v <;> decide +kernel
  rw [pc]
  exact programText_slice (programLoaded_codeIn loaded) _ _
    (by cases v <;> decide +kernel) (by cases v <;> decide +kernel)

theorem second_dispatched [bindings : Bindings] (v : Wrapper.Variant)
    {initial s : RamState} {inputs : Array Input}
    (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall (routine v) initial inputs)
    (state : ExecutionState initial s (regions (routine v) initial))
    (rsp : rspOf s = stackPtr initial - 360#64)
    (rip : s.RIP = secondEntry v)
    (hasher : HasherAt s (rspOf s + 8#64) ByteArray.empty v.initialHash)
    (count : s.regValue .r15 = BitVec.ofNat 64 inputs.size)
    (pointer : memLoad s.external (rspOf s + 216#64) 64 = initial.regValue .rdi)
    (length : memLoad s.external (rspOf s + 224#64) 64 = initial.regValue .rdx) :
    ∃ t, ExecutionState initial t (regions (routine v) initial) ∧
      rspOf t = stackPtr initial - 360#64 ∧ t.external = s.external ∧
      ((inputs.size = 0 ∧ t.RIP = (finalizeLastTable v).exit ∧
        HasherAt t (rspOf t + 8#64) ByteArray.empty v.initialHash) ∨
       (Table.LoopState (finalizeLastTable v) (stackPtr initial - 360#64) inputs 0 t ∧
        Table.InputData (finalizeLastTable v) (stackPtr initial - 360#64) inputs t ∧
        Table.Separation (finalizeLastTable v) initial t 832 inputs)) := by
  have jump : secondEntry v + 9#64 + (secondDisplacement v).signExtend 64 =
      (finalizeLastTable v).exit := by cases v <;> decide +kernel
  have target : InProgram (secondEntry v + 9#64 + (secondDisplacement v).signExtend 64) := by
    rw [jump]; exact (finalizeLastTable_codeFacts v).2.2
  obtain ⟨fuel, b, run, ready, _, branch⟩ := Dispatch.branch
    (displacement := secondDisplacement v) (count := 15) (secondEntry v)
    (returnBoundary initial) (valid_return_boundary machine call.stack call.returnAddress).2.2
    (fun i hi => second_inside v i (by omega)) target s
    (supportedMachine_readyToStep state.machine) (second_branch_code v state.loaded) rip
  have frameB : AgreesExcept [.flags, .rip] s b := branch.agrees
  have nomem : ∀ c ∈ ([.flags, .rip] : List Component), ∀ a, ¬ c.Covers a := by
    simp [Component.Covers]
  have stateB := state.of_agrees (regions_avoid call) run ready frameB
    (fun c hc a ha => (nomem c hc a ha).elim) (by simp)
  have memB := frameB.external nomem
  have rspB : rspOf b = rspOf s := frameB.read (n := 64) (r := 4) (by simp)
  have hashB : HasherAt b (rspOf b + 8#64) ByteArray.empty v.initialHash := by
    rw [rspB]; exact hasher.of_bytes (fun _ _ => by rw [memB])
  have countB : b.regValue .r15 = BitVec.ofNat 64 inputs.size :=
    (frameB.read (n := 64) (r := 15) (by simp)).trans count
  by_cases empty : inputs.size = 0
  · have ripB : b.RIP = (finalizeLastTable v).exit := by
      have h : b.RIP = if s.regValue .r15 = 0#64 then
        secondEntry v + 9#64 + (secondDisplacement v).signExtend 64 else secondEntry v + 9#64 := branch.rip
      simpa [count, empty, jump] using h
    exact ⟨b, stateB, rspB.trans rsp, memB, Or.inl ⟨empty, ripB, hashB⟩⟩
  · have bound := Wrapper.validCall_count_bound (firstOutput_validCall call)
    have nonzero : s.regValue .r15 ≠ 0#64 := by
      rw [count]
      intro eq
      have eqNat := congrArg BitVec.toNat eq
      simp only [BitVec.toNat_ofNat] at eqNat
      rw [Nat.mod_eq_of_lt (by omega)] at eqNat
      exact empty eqNat
    have ripB : b.RIP = secondEntry v + 9#64 := by
      have h : b.RIP = if s.regValue .r15 = 0#64 then
        secondEntry v + 9#64 + (secondDisplacement v).signExtend 64 else secondEntry v + 9#64 := branch.rip
      simpa only [nonzero, ite_false] using h
    obtain ⟨t, stateT, loop, data, apart, rspT, memT⟩ := second_tail_ready v machine call stateB
      (rspB.trans rsp) ripB hashB countB (by omega)
      (by rw [memB, rspB]; exact pointer) (by rw [memB, rspB]; exact length)
    exact ⟨t, stateT, rspT.trans (rspB.trans rsp), memT.trans memB, Or.inr ⟨loop, data, apart⟩⟩

def firstLoadPC (v : Wrapper.Variant) : BitVec 64 :=
  (Finalization.finalizeFirst.layout v).exit

def firstStorePC (v : Wrapper.Variant) : BitVec 64 :=
  if v = .sha224 then 0x100988 else 0x1025a0

theorem first_load_inside (v : Wrapper.Variant) :
    BlockInProgram (firstLoadPC v) (Serialize.bytes (.loadSwap .at72 (v == .sha224))).length := by
  cases v
  · exact blockInProgram_of_textOffset 0x95a _ (by decide +kernel)
  · exact blockInProgram_of_textOffset 0x256a _ (by decide +kernel)

theorem first_load_code (v : Wrapper.Variant) {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (firstLoadPC v) (Serialize.bytes (.loadSwap .at72 (v == .sha224)))) s := by
  cases v
  · exact programText_slice (programLoaded_codeIn loaded) 0x95a _
      (by decide +kernel) (by decide +kernel)
  · exact programText_slice (programLoaded_codeIn loaded) 0x256a _
      (by decide +kernel) (by decide +kernel)

theorem first_store_inside (v : Wrapper.Variant) :
    BlockInProgram (firstStorePC v) (Serialize.bytes (.store .r13 (v == .sha224))).length := by
  cases v
  · exact blockInProgram_of_textOffset 0x988 _ (by decide +kernel)
  · exact blockInProgram_of_textOffset 0x25a0 _ (by decide +kernel)

theorem first_store_code (v : Wrapper.Variant) {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (firstStorePC v) (Serialize.bytes (.store .r13 (v == .sha224)))) s := by
  cases v
  · exact programText_slice (programLoaded_codeIn loaded) 0x988 _
      (by decide +kernel) (by decide +kernel)
  · exact programText_slice (programLoaded_codeIn loaded) 0x25a0 _
      (by decide +kernel) (by decide +kernel)

theorem first_serialized [bindings : Bindings] (v : Wrapper.Variant)
    {initial s : RamState} {inputs : Array Input} {hash : Array UInt32}
    (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall (routine v) initial inputs)
    (state : ExecutionState initial s (regions (routine v) initial))
    (rsp : rspOf s = stackPtr initial - 360#64)
    (rip : s.RIP = firstLoadPC v)
    (words : HashStateAt s (rspOf s + 72#64) hash)
    (base : s.regValue .rbx = rspOf s + 72#64)
    (output : s.regValue .r13 = initial.regValue .rcx) :
    ∃ a b t, ExecutionState initial t (regions (routine v) initial) ∧
      (Serialize.effect (firstLoadPC v) (.loadSwap .at72 (v == .sha224)) s).Holds s a ∧
      (Serialize.effect (firstStorePC v) (.store .r13 (v == .sha224)) a).Holds a b ∧
      Initialize.Post (Initialization.finalizeReset.layout v) (rspOf b + 8#64) b t ∧
      rspOf t = stackPtr initial - 360#64 ∧ t.RIP = secondEntry v ∧
      HasherAt t (rspOf t + 8#64) ByteArray.empty v.initialHash ∧
      (TwoOutputs.outputRegion (routine v) initial).HasBytes t.external (v.serializeHash hash) ∧
      MemoryWriteFrame a b #v[TwoOutputs.outputRegion (routine v) initial] := by
  obtain ⟨a, stateA, load, swapped⟩ := serialize_load_generic v (routine v) 360 .at72
    (by rw [routine_stack]; decide) (by decide) (firstLoadPC v) machine call state
    rsp rip words (first_load_inside v) (first_load_code v state.loaded)
  have rspA : rspOf a = rspOf s := load.agrees.read (n := 64) (r := 4)
    (by cases v <;> simp [Serialize.effect, Effect.components])
  have outputA : a.regValue .r13 = initial.regValue .rcx :=
    (load.agrees.read (n := 64) (r := 13)
      (by cases v <;> simp [Serialize.effect, Effect.components])).trans output
  have baseA : a.regValue .rbx = rspOf a + 72#64 := by
    rw [rspA]
    exact (load.agrees.read (n := 64) (r := 3)
      (by cases v <;> simp [Serialize.effect, Effect.components])).trans base
  have ripA : a.RIP = firstStorePC v := by
    rw [load.rip]
    change firstLoadPC v + BitVec.ofNat 64 (Serialize.bytes (.loadSwap .at72 (v == .sha224))).length = _
    cases v <;> decide +kernel
  have member : (⟨(initial.regValue .rcx).toNat, v.outputBytes⟩ : MemoryRegion) ∈
      [TwoOutputs.outputRegion (routine v) initial, TwoOutputs.secondOutputRegion (routine v) initial] := by
    cases v <;> simp [routine, Header.Layout.routine, TwoOutputs.outputRegion, registerRegion,
      sha224FinalizeIntoReset, sha256FinalizeIntoReset, Wrapper.Variant.outputBytes]
  obtain ⟨b, stateB, store, frameB, payload⟩ := serialize_store_generic v (routine v)
    (firstStorePC v) .r13 (initial.regValue .rcx) machine call stateA member outputA swapped ripA
    (first_store_inside v) (first_store_code v stateA.loaded)
  have rspB : rspOf b = rspOf a := store.agrees.read (n := 64) (r := 4)
    (by cases v <;> simp [Serialize.effect, Effect.components])
  have baseB : b.regValue .rbx = rspOf b + 72#64 := by
    rw [rspB]
    exact (store.agrees.read (n := 64) (r := 3)
      (by cases v <;> simp [Serialize.effect, Effect.components])).trans baseA
  have ripB : b.RIP = (Initialization.finalizeReset.layout v).start := by
    rw [store.rip]
    change firstStorePC v + BitVec.ofNat 64 (Serialize.bytes (.store .r13 (v == .sha224))).length = _
    cases v <;> decide +kernel
  obtain ⟨t, stateT, init⟩ := initialize_state_at v (occ := .finalizeReset) machine call stateB
    (rspB.trans (rspA.trans rsp)) ripB
    (by rw [routine_stack]; decide) (by decide) (by intro _; exact baseB)
  have rspT : rspOf t = rspOf b := init.rsp
  have firstB : (TwoOutputs.outputRegion (routine v) initial).HasBytes b.external (v.serializeHash hash) := by
    cases v <;> exact payload
  have frameT : MemoryWriteFrame b t
      #v[TwoOutputs.secondOutputRegion (routine v) initial, Stack.region initial (routine v).minStackBytes] := by
    apply init.frame.memoryWriteFrame
    intro c hc a ha
    change c ∈ [.reg 0, .reg 0, .reg 0, .reg 0,
      .mem ((rspOf b + 8#64) + 64#64) 32, .mem ((rspOf b + 8#64) + 96#64) 8,
      .mem ((rspOf b + 8#64) + 63#64) 1, .rip] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals refine ⟨Stack.region initial (routine v).minStackBytes, by simp, ?_⟩
    all_goals rw [rspB, rspA, rsp, BitVec.add_assoc] at ha
    · exact stack_frame_contains call.stack (frame := 360) (offset := 72) (len := 32)
        (by rw [routine_stack]; decide) (by decide) ha
    · exact stack_frame_contains call.stack (frame := 360) (offset := 104) (len := 8)
        (by rw [routine_stack]; decide) (by decide) ha
    · exact stack_frame_contains call.stack (frame := 360) (offset := 71) (len := 1)
        (by rw [routine_stack]; decide) (by decide) ha
  refine ⟨a, b, t, stateT, load, store, init, rspT.trans (rspB.trans (rspA.trans rsp)), ?_, ?_, ?_, ?_⟩
  · rw [init.rip]
    change (Initialization.finalizeReset.layout v).finish = secondEntry v
    cases v <;> decide +kernel
  · rw [rspT]; exact init.hasher
  · refine ⟨firstB.1, fun i => ?_⟩
    rw [firstOutput_unchanged call frameT ?_]
    · exact firstB.2 i
    · have bounded := (call.outputInMemory (TwoOutputs.outputRegion (routine v) initial) (by simp)).2.1
      have size := firstB.1
      change (v.serializeHash hash).size = (TwoOutputs.outputRegion (routine v) initial).size at size
      change (TwoOutputs.outputRegion (routine v) initial).start +
        (TwoOutputs.outputRegion (routine v) initial).size < 2^32 at bounded
      change _ ≤ (BitVec.ofNat 64 ((TwoOutputs.outputRegion (routine v) initial).start + i.val)).toNat ∧ _
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
  · cases v <;> exact frameB

theorem cloned_stack [bindings : Bindings] (k : Blocks.Digest.CloneSetup.Kind)
    (routine : Routine) (p : BitVec 64) {initial s : RamState}
    {inputs : Array Input} {message : ByteArray} {hash : Array UInt32}
    (stride : UnitStringStride bindings) (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall routine initial inputs)
    (capacity : 360 ≤ routine.minStackBytes)
    (state : ExecutionState initial s (regions routine initial))
    (rsp : rspOf s = stackPtr initial - 360#64) (rip : s.RIP = p)
    (hasher : HasherAt s (rspOf s + k.source) message hash)
    (inside : BlockInProgram p ((Blocks.Digest.CloneSetup.bytesFor k).length + 3))
    (code : CodeIn (codeRange p (Blocks.Digest.CloneSetup.bytesFor k ++ [0xf3,0x48,0xa5])) s) :
    ∃ c t, ExecutionState initial t (regions routine initial) ∧
      (Blocks.Digest.CloneSetup.effectFor k p s).Holds s c ∧
      (repMovsqEffect (p + BitVec.ofNat 64 (Blocks.Digest.CloneSetup.bytesFor k).length) c).Holds c t ∧
      HasherAt t (rspOf s + k.destination) message hash ∧ rspOf t = rspOf s ∧
      t.RIP = p + BitVec.ofNat 64 ((Blocks.Digest.CloneSetup.bytesFor k).length + 3) ∧
      MemoryWriteFrame s t #v[⟨(rspOf s + k.destination).toNat, 104⟩] := by
  have outside := (valid_return_boundary machine call.stack call.returnAddress).2.2
  have avoids : ∀ region ∈ regions routine initial, region.Avoids InProgram := by
    intro region member a ha hp
    exact (call.separation.2 region (by simpa [regions] using member)).2 a ha (.inl hp)
  have avoidStack : (Stack.region initial routine.minStackBytes).Avoids
      (fun a => InProgram a ∨ InPageTables a) := by
    simpa only [InPageTables] using (call.separation.2 _ (by simp)).2
  have setupCode : CodeIn (codeRange p (Blocks.Digest.CloneSetup.bytesFor k)) s := by
    apply code.mono
    intro x hx
    exact (codeRange_append _ _ _).symm ▸ List.mem_append_left _ hx
  obtain ⟨fuel, c, run, ready, _, setup⟩ := Blocks.Digest.CloneSetup.runFor k p
    (returnBoundary initial) outside (fun i hi => inside i (by omega)) s
    (supportedMachine_readyToStep state.machine) setupCode rip
  have nomem : ∀ comp ∈ (Blocks.Digest.CloneSetup.effectFor k p s).components,
      ∀ a, ¬ comp.Covers a := by
    simp [Blocks.Digest.CloneSetup.effectFor, Effect.components, Component.Covers]
  have stateC := state.of_agrees avoids run ready setup.agrees
    (fun comp hc a ha => (nomem comp hc a ha).elim)
    (by simp [Blocks.Digest.CloneSetup.effectFor, Effect.components])
  have memC := setup.agrees.external nomem
  have rspC : rspOf c = rspOf s := setup.agrees.read (n := 64) (r := 4)
    (by simp [Blocks.Digest.CloneSetup.effectFor, Effect.components])
  have values : rdi.read c = rspOf s + k.destination ∧
      rsi.read c = rspOf s + k.source ∧ rcx.read c = 13 := setup.writes
  have count : (rcx.read c).toNat = 13 := by rw [values.2.2]; decide
  have src : MemReadable c (rsi.read c) 104 := by
    rw [values.2.1, rsp]
    cases k <;> exact stack_frame_readable call.stack capacity stateC.allocated (by decide)
  have dst : CrossPageStore.Writable c (rdi.read c) 104 := by
    rw [values.1, rsp]
    apply CrossPageStore.Writable.of_memWritable
    cases k <;> exact stack_frame_writable call.stack capacity
      (fun a ha h => avoidStack a ha (.inr h)) stateC.allocated (by decide) (by decide)
  let pc := p + BitVec.ofNat 64 (Blocks.Digest.CloneSetup.bytesFor k).length
  have cloneInside : BlockInProgram pc 3 := by
    intro i hi
    have h := inside ((Blocks.Digest.CloneSetup.bytesFor k).length+i) (by omega)
    simpa only [pc, BitVec.ofNat_add, BitVec.add_assoc] using h
  have apart : RangeApart (rdi.read c) 104 pc 3 := by
    rw [values.1, rsp]
    cases k <;> exact stack_frame_codeApart call.stack capacity
      (fun a ha h => avoidStack a ha (.inl h)) (by decide)
      (fun j hj => cloneInside j (Nat.le_of_lt hj))
  have disjoint : (rsi.read c).toNat + 104 ≤ (rdi.read c).toNat ∨
      (rdi.read c).toNat + 104 ≤ (rsi.read c).toNat := by
    rw [values.1, values.2.1, rsp]
    cases k
    all_goals
      simp only [Blocks.Digest.CloneSetup.Kind.source, Blocks.Digest.CloneSetup.Kind.destination]
      have h0 := stack_frame_toNat call.stack capacity (offset := 0) (by decide)
      have h8 := stack_frame_toNat call.stack capacity (offset := 8) (by decide)
      have h112 := stack_frame_toNat call.stack capacity (offset := 112) (by decide)
      have h168 := stack_frame_toNat call.stack capacity (offset := 168) (by decide)
      simp only [BitVec.ofNat_eq_ofNat] at h0 h8 h112 h168 ⊢
      omega
  have pre : RepMovsq.RepMovsqPre pc c := RepMovsq.pre_of_memory setup.rip
    stateC.directionFlag.df count src dst disjoint apart
  have cloneCode : CodeIn (codeRange pc [0xf3,0x48,0xa5]) c := by
    have preserved : CodeIn (codeRange p (Blocks.Digest.CloneSetup.bytesFor k ++ [0xf3,0x48,0xa5])) c := by
      simpa only [CodeIn, memC] using code
    apply preserved.mono
    intro x hx
    exact (codeRange_append _ _ _).symm ▸ List.mem_append_right _ hx
  have coverage : ∀ a, (Component.mem (rdi.read c) 104).Covers a →
      ∃ region ∈ regions routine initial, region.Contains a.toNat := by
    intro a ha
    refine ⟨Stack.region initial routine.minStackBytes, by simp [regions], ?_⟩
    rw [values.1, rsp] at ha
    cases k <;> exact stack_frame_contains call.stack capacity (by decide) ha
  have sourceHasher : HasherAt c (rsi.read c) message hash := by
    rw [values.2.1]
    exact hasher.of_bytes (fun _ _ => by rw [memC])
  obtain ⟨stateT, copy, hashed, rspT, frame⟩ := Instances.Digest.clone stride stateC avoids
    cloneCode pre count
    (boundary_ne_program outside (by simpa only [BitVec.add_zero] using cloneInside 0 (by decide)))
    (boundary_ne_program outside (cloneInside 3 (by decide))) coverage sourceHasher
  refine ⟨c, nextStates 13 c, stateT, setup, copy, ?_, rspT.trans rspC, ?_, ?_⟩
  · simpa only [values.1] using hashed
  · simpa only [pc, repMovsqEffect, BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using copy.rip
  · intro a outside
    rw [frame a (by simpa only [values.1] using outside), memC]

theorem first_prepared [bindings : Bindings] (v : Wrapper.Variant)
    {initial s : RamState} {inputs : Array Input}
    (stride : UnitStringStride bindings) (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall (routine v) initial inputs)
    (state : ExecutionState initial s (regions (routine v) initial))
    (rsp : rspOf s = stackPtr initial - 360#64)
    (data : Table.InputData (finalizeFirstTable v) ((finalizeFirstTable v).chunk.sp initial) inputs s)
    (separation : Table.Separation (finalizeFirstTable v) initial s 832 inputs)
    (count : s.regValue .r15 = BitVec.ofNat 64 inputs.size)
    (branch :
      (inputs.size = 0 ∧ s.RIP = Normalize.emptyEntry v .finalize ∧
        HasherAt s (rspOf s + 8#64) ByteArray.empty v.initialHash ∧
        s.regValue .r13 = initial.regValue .rcx) ∨
      (Table.LoopState (finalizeFirstTable v) ((finalizeFirstTable v).chunk.sp initial) inputs 0 s ∧
        memLoad s.external (rspOf s + 296#64) 64 = initial.regValue .rcx)) :
    ∃ n, ExecutionState initial n (regions (routine v) initial) ∧
      Finalize.Prepared (Finalization.finalizeFirst.layout v)
        (stackPtr initial - 360#64) (message inputs) n ∧
      n.regValue .r13 = initial.regValue .rcx ∧
      (∀ slot, 216 ≤ slot → slot ≤ 360 →
        memLoad n.external (stackPtr initial - 360#64 + BitVec.ofNat 64 slot) 64 =
          memLoad s.external (stackPtr initial - 360#64 + BitVec.ofNat 64 slot) 64) ∧
      n.regValue .r15 = BitVec.ofNat 64 inputs.size := by
  rcases branch with ⟨empty, rip, hasher, output⟩ | ⟨loop, output⟩
  · obtain ⟨n, stateN, effect, prepared, memory⟩ := normalized_empty v .finalize machine call state rip hasher
    have emptyInputs : inputs = #[] := Array.eq_empty_of_size_eq_zero empty
    have msg : message inputs = ByteArray.empty := by simp [emptyInputs, message]
    refine ⟨n, stateN, ?_, ?_, ?_, ?_⟩
    · simpa only [msg, rsp, Normalize.finalization] using prepared
    · exact (effect.agrees.read (n := 64) (r := 13)
        (by simp [Normalize.emptyEffect, Normalize.tailReg, Normalize.finalization,
          Finalization.variant, Finalize.Variant.registers, Blocks.Length.Registers.tail,
          Effect.components])).trans output
    · intro slot _ _; rw [memory]
    · exact (effect.agrees.read (n := 64) (r := 15)
        (by simp [Normalize.emptyEffect, Normalize.tailReg, Normalize.finalization,
          Finalization.variant, Finalize.Variant.registers, Blocks.Length.Registers.tail,
          Effect.components])).trans count
  · obtain ⟨t, done⟩ := traversed v false stride machine call state loop data separation
    have rspT : rspOf t = stackPtr initial - 360#64 := done.rsp
    have ripT : t.RIP = Normalize.entry true v .finalize := by
      have eq : (finalizeFirstTable v).exit = Normalize.entry true v .finalize := by cases v <;> decide +kernel
      exact done.rip.trans eq
    have hashT : HasherAt t (rspOf t + 8#64) (message inputs) v.initialHash := by
      rw [rspT]
      exact done.hasher
    obtain ⟨n, stateN, effect, prepared⟩ := normalized v true (form := .finalize)
      machine call done.state done.rsp ripT hashT (routine_stack v)
    have memory : n.external = t.external := Normalize.memory effect
    have saved (slot : Nat) (low : 216 ≤ slot) (high : slot ≤ 360) :=
      table_saved false call state done slot (by omega) high
    refine ⟨n, stateN, ?_, ?_, ?_, ?_⟩
    · simpa only [rspT, Normalize.finalization] using prepared
    · have out : n.regValue .r13 = memLoad t.external (rspOf t + 296#64) 64 :=
        Normalize.restored_output effect
      rw [out, rspT, saved 296 (by decide) (by decide), ← rsp]
      exact output
    · intro slot low high
      rw [memory, saved slot low high]
    · exact (effect.agrees.read (n := 64) (r := 15)
        (by simp [Normalize.effect, Normalize.shifted, Normalize.tailReg, Normalize.outputReg,
          Normalize.finalization, Finalization.variant, Finalize.Variant.registers,
          Blocks.Length.Registers.tail, Effect.components])).trans done.count

def lastClonePC (v : Wrapper.Variant) : BitVec 64 := (finalizeLastTable v).exit

theorem last_clone_inside (v : Wrapper.Variant) :
    BlockInProgram (lastClonePC v) ((Blocks.Digest.CloneSetup.bytesFor .finalizeLast).length + 3) := by
  cases v with
  | sha224 => exact blockInProgram_of_textOffset 0xae8 _ (by decide +kernel)
  | sha256 => exact blockInProgram_of_textOffset 0x2708 _ (by decide +kernel)

theorem last_clone_code (v : Wrapper.Variant) {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (lastClonePC v)
      (Blocks.Digest.CloneSetup.bytesFor .finalizeLast ++ [0xf3,0x48,0xa5])) s := by
  cases v with
  | sha224 =>
    exact programText_slice (programLoaded_codeIn loaded) 0xae8 _
      (by decide +kernel) (by decide +kernel)
  | sha256 =>
    exact programText_slice (programLoaded_codeIn loaded) 0x2708 _
      (by decide +kernel) (by decide +kernel)

def lastLoadPC (v : Wrapper.Variant) : BitVec 64 := (Finalization.finalizeLast.layout v).exit

def lastStorePC (v : Wrapper.Variant) : BitVec 64 := lastLoadPC v +
  BitVec.ofNat 64 (Serialize.bytes (.loadSwap .at176 (v == .sha224))).length + 8

def returnPC (v : Wrapper.Variant) : BitVec 64 := lastStorePC v +
  BitVec.ofNat 64 (Serialize.bytes (.store (if v = .sha224 then .r10 else .r11) (v == .sha224))).length

theorem last_load_inside (v : Wrapper.Variant) :
    BlockInProgram (lastLoadPC v) (Serialize.bytes (.loadSwap .at176 (v == .sha224))).length := by
  let offset := (lastLoadPC v).toNat - 0x100000
  have eq : lastLoadPC v = Extracted.textAddress + BitVec.ofNat 64 offset := by cases v <;> decide +kernel
  rw [eq]
  exact blockInProgram_of_textOffset offset _ (by cases v <;> decide +kernel)

theorem last_load_code (v : Wrapper.Variant) {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (lastLoadPC v) (Serialize.bytes (.loadSwap .at176 (v == .sha224)))) s := by
  let offset := (lastLoadPC v).toNat - 0x100000
  have eq : lastLoadPC v = Extracted.textAddress + BitVec.ofNat 64 offset := by cases v <;> decide +kernel
  rw [eq]
  exact programText_slice (programLoaded_codeIn loaded) offset _
    (by cases v <;> decide +kernel) (by cases v <;> decide +kernel)

theorem last_pointer_code (v : Wrapper.Variant) {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (lastStorePC v - 8#64)
      ([0x4c,0x8b,if v = .sha224 then 0x94 else 0x9c,0x24] ++ immBytes 32 304)) s := by
  let offset := (lastStorePC v - 8#64).toNat - 0x100000
  have eq : lastStorePC v - 8#64 = Extracted.textAddress + BitVec.ofNat 64 offset := by cases v <;> decide +kernel
  rw [eq]
  exact programText_slice (programLoaded_codeIn loaded) offset _
    (by cases v <;> decide +kernel) (by cases v <;> decide +kernel)

theorem last_store_inside (v : Wrapper.Variant) :
    BlockInProgram (lastStorePC v)
      (Serialize.bytes (.store (if v = .sha224 then .r10 else .r11) (v == .sha224))).length := by
  let offset := (lastStorePC v).toNat - 0x100000
  have eq : lastStorePC v = Extracted.textAddress + BitVec.ofNat 64 offset := by cases v <;> decide +kernel
  rw [eq]
  exact blockInProgram_of_textOffset offset _ (by cases v <;> decide +kernel)

theorem last_store_code (v : Wrapper.Variant) {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (lastStorePC v)
      (Serialize.bytes (.store (if v = .sha224 then .r10 else .r11) (v == .sha224)))) s := by
  let offset := (lastStorePC v).toNat - 0x100000
  have eq : lastStorePC v = Extracted.textAddress + BitVec.ofNat 64 offset := by cases v <;> decide +kernel
  rw [eq]
  exact programText_slice (programLoaded_codeIn loaded) offset _
    (by cases v <;> decide +kernel) (by cases v <;> decide +kernel)

theorem return_inside (v : Wrapper.Variant) : BlockInProgram (returnPC v) Epilogue.Layout.six312.length := by
  let offset := (returnPC v).toNat - 0x100000
  have eq : returnPC v = Extracted.textAddress + BitVec.ofNat 64 offset := by cases v <;> decide +kernel
  rw [eq]
  exact blockInProgram_of_textOffset offset _ (by cases v <;> decide +kernel)

theorem return_code (v : Wrapper.Variant) {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (returnPC v) (Epilogue.bytes .six312 ++ [0xc3])) s := by
  let offset := (returnPC v).toNat - 0x100000
  have eq : returnPC v = Extracted.textAddress + BitVec.ofNat 64 offset := by cases v <;> decide +kernel
  rw [eq]
  exact programText_slice (programLoaded_codeIn loaded) offset _
    (by cases v <;> decide +kernel) (by cases v <;> decide +kernel)

theorem last_prepared [bindings : Bindings] (v : Wrapper.Variant)
    {initial s : RamState} {inputs : Array Input}
    (stride : UnitStringStride bindings) (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall (routine v) initial inputs)
    (state : ExecutionState initial s (regions (routine v) initial))
    (rsp : rspOf s = stackPtr initial - 360#64)
    (rip : s.RIP = lastClonePC v)
    (hasher : HasherAt s (rspOf s + 8#64) (message inputs) v.initialHash) :
    ∃ n, ExecutionState initial n (regions (routine v) initial) ∧
      Finalize.Prepared (Finalization.finalizeLast.layout v)
        (stackPtr initial - 360#64) (message inputs) n ∧
      MemoryWriteFrame s n #v[⟨(stackPtr initial - 360#64 + 112#64).toNat,104⟩] := by
  obtain ⟨c,t,stateT,_,_,hasherT,rspT,ripT,frameT⟩ := cloned_stack .finalizeLast
    (routine v) (lastClonePC v) stride machine call (by rw [routine_stack]; decide)
    state rsp rip hasher (last_clone_inside v) (last_clone_code v state.loaded)
  have ripT' : t.RIP = Normalize.entry false v .finalize := by
    rw [ripT]; cases v <;> decide +kernel
  have hasherT' : HasherAt t (rspOf t + 112#64) (message inputs) v.initialHash := by
    rw [rspT]; exact hasherT
  obtain ⟨n,stateN,effect,prepared⟩ := normalized v false (form := .finalize)
    machine call stateT (rspT.trans rsp) ripT' hasherT' (routine_stack v)
  refine ⟨n,stateN,?_,?_⟩
  · simpa only [Normalize.finalization, rspT, rsp] using prepared
  · intro a outside
    rw [Normalize.memory effect]
    apply frameT a
    simpa only [Blocks.Digest.CloneSetup.Kind.destination, rsp, BitVec.ofNat_eq_ofNat] using outside

theorem first_finalized [bindings : Bindings] (v : Wrapper.Variant)
    {initial n : RamState} {inputs : Array Input}
    (stride : UnitStringStride bindings) (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall (routine v) initial inputs)
    (state : ExecutionState initial n (regions (routine v) initial))
    (prepared : Finalize.Prepared (Finalization.finalizeFirst.layout v)
      (stackPtr initial - 360#64) (message inputs) n)
    (output : n.regValue .r13 = initial.regValue .rcx)
    (count : n.regValue .r15 = BitVec.ofNat 64 inputs.size) :
    ∃ f hash, ExecutionState initial f (regions (routine v) initial) ∧
      rspOf f = stackPtr initial - 360#64 ∧ f.RIP = firstLoadPC v ∧
      HashStateAt f (rspOf f + 72#64) hash ∧
      v.serializeHash hash = v.hash (message inputs) ∧
      f.regValue .rbx = rspOf f + 72#64 ∧ f.regValue .r13 = initial.regValue .rcx ∧
      f.regValue .r15 = BitVec.ofNat 64 inputs.size ∧
      (∀ slot, 216 ≤ slot → slot ≤ 360 →
        memLoad f.external (stackPtr initial - 360#64 + BitVec.ofNat 64 slot) 64 =
          memLoad n.external (stackPtr initial - 360#64 + BitVec.ofNat 64 slot) 64) := by
  obtain ⟨f,done⟩ := finalized v .finalizeFirst (routine_stack v) stride machine call state prepared
  obtain ⟨hash,words,digest⟩ := done.digest
  have rsp : rspOf f = stackPtr initial - 360#64 := done.rsp
  refine ⟨f,hash,done.state,rsp,done.rip,?_,digest,?_,?_,?_,?_⟩
  · rw [rsp]
    change HashStateAt f (stackPtr initial - 360#64 + 8#64 + 64#64) hash at words
    simpa only [BitVec.add_assoc, show (8#64 + 64#64) = 72#64 from rfl] using words
  · rw [rsp]
    have hp := done.hashPointer
    change f.regValue .rbx = stackPtr initial - 360#64 + 8#64 + 64#64 at hp
    simpa only [BitVec.add_assoc, show (8#64 + 64#64) = 72#64 from rfl] using hp
  · exact (done.frame.registers 13 (by decide)
      (by change ¬ (13 : BitVec 5) ∈ Finalize.Variant.finalizeFirst.clobbered; decide +kernel)).trans output
  · exact (done.frame.registers 15 (by decide)
      (by change ¬ (15 : BitVec 5) ∈ Finalize.Variant.finalizeFirst.clobbered; decide +kernel)).trans count
  · intro slot low high
    exact finalized_saved false call state done slot (by change 176 ≤ slot; omega) high

theorem last_serialized [bindings : Bindings] (v : Wrapper.Variant)
    {initial s : RamState} {inputs : Array Input} {hash : Array UInt32} {first : ByteArray}
    (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall (routine v) initial inputs)
    (state : ExecutionState initial s (regions (routine v) initial))
    (rsp : rspOf s = stackPtr initial - 360#64) (rip : s.RIP = lastLoadPC v)
    (words : HashStateAt s (rspOf s + 176#64) hash)
    (saved : memLoad s.external (rspOf s + 304#64) 64 = initial.regValue .r8)
    (firstBytes : (TwoOutputs.outputRegion (routine v) initial).HasBytes s.external first) :
    ∃ t, ExecutionState initial t (regions (routine v) initial) ∧ t.RIP = returnPC v ∧
      (TwoOutputs.outputRegion (routine v) initial).HasBytes t.external first ∧
      (TwoOutputs.secondOutputRegion (routine v) initial).HasBytes t.external (v.serializeHash hash) ∧
      rspOf t = rspOf s ∧ MemoryWriteFrame s t #v[TwoOutputs.secondOutputRegion (routine v) initial] := by
  obtain ⟨t,stateT,ripT,firstT,secondT,rspT,frameT⟩ := serialized_last_generic v
    (routine v) 360 .at176 304 (lastLoadPC v) (lastStorePC v)
    (by rw [routine_stack]; decide) (by decide) (by decide) (by decide)
    (by cases v <;> rfl) (by cases v <;> decide +kernel)
    (last_load_inside v) (last_load_code v) (last_pointer_code v)
    (by simpa only [BitVec.add_zero] using last_store_inside v 0 (by omega))
    (last_store_inside v) (last_store_code v) machine call state rsp rip words saved firstBytes
  refine ⟨t,stateT,ripT,firstT,?_,rspT,frameT⟩
  cases v <;> exact secondT

theorem last_hashed [bindings : Bindings] (v : Wrapper.Variant)
    {initial s : RamState} {inputs : Array Input} {first : ByteArray}
    (stride : UnitStringStride bindings) (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall (routine v) initial inputs)
    (state : ExecutionState initial s (regions (routine v) initial))
    (rsp : rspOf s = stackPtr initial - 360#64) (rip : s.RIP = lastClonePC v)
    (hasher : HasherAt s (rspOf s + 8#64) (message inputs) v.initialHash)
    (firstBytes : (TwoOutputs.outputRegion (routine v) initial).HasBytes s.external first) :
    ∃ f hash, ExecutionState initial f (regions (routine v) initial) ∧
      rspOf f = stackPtr initial - 360#64 ∧ f.RIP = lastLoadPC v ∧
      HashStateAt f (rspOf f + 176#64) hash ∧ v.serializeHash hash = v.hash (message inputs) ∧
      (TwoOutputs.outputRegion (routine v) initial).HasBytes f.external first ∧
      (∀ slot, 296 ≤ slot → slot ≤ 360 →
        memLoad f.external (stackPtr initial - 360#64 + BitVec.ofNat 64 slot) 64 =
          memLoad s.external (stackPtr initial - 360#64 + BitVec.ofNat 64 slot) 64) := by
  have stack : Stack.Valid initial 832 := by simpa only [routine_stack] using call.stack
  obtain ⟨n,stateN,prepared,frameN⟩ := last_prepared v stride machine call state rsp rip hasher
  have firstN := Last.frame_preserves_output call frameN (by
    intro region member a ha
    simp only [Vector.mem_mk, List.mem_toArray, List.mem_singleton] at member
    subst region
    simpa only [routine_stack] using stack_frame_region_subset stack
      (by decide : 360 ≤ 832) (by decide : 112 + 104 ≤ 360) ha) firstBytes
  have savedN (slot : Nat) (low : 296 ≤ slot) (high : slot ≤ 360) :
      memLoad n.external (stackPtr initial - 360#64 + BitVec.ofNat 64 slot) 64 =
        memLoad s.external (stackPtr initial - 360#64 + BitVec.ofNat 64 slot) 64 := by
    apply Table.memLoad_of_frame frameN (slot_readable stack state.allocated high)
    intro region member
    simp only [Vector.mem_mk, List.mem_toArray, List.mem_singleton] at member
    subst region
    exact slot_local stack high (by omega : 112 + 104 ≤ slot)
  obtain ⟨f,done⟩ := finalized v .finalizeLast (routine_stack v) stride machine call stateN prepared
  obtain ⟨hash,words,digest⟩ := done.digest
  have rspF : rspOf f = stackPtr initial - 360#64 := done.rsp
  refine ⟨f,hash,done.state,rspF,done.rip,?_,digest,?_,?_⟩
  · rw [rspF]
    change HashStateAt f (stackPtr initial - 360#64 + 112#64 + 64#64) hash at words
    simpa only [BitVec.add_assoc, show (112#64 + 64#64) = 176#64 from rfl] using words
  · exact Last.frame_preserves_output call done.frame.memory (by
      simpa only [routine_stack, Finalization.reserve] using (Finalize.footprint_subset_stack
        (Finalization.wellFormed .finalizeLast v) stack)) firstN
  · intro slot low high
    exact (finalized_saved true call stateN done slot low high).trans (savedN slot low high)

theorem second_hashed [bindings : Bindings] (v : Wrapper.Variant)
    {initial s : RamState} {inputs : Array Input} {first : ByteArray}
    (stride : UnitStringStride bindings) (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall (routine v) initial inputs)
    (state : ExecutionState initial s (regions (routine v) initial))
    (rsp : rspOf s = stackPtr initial - 360#64) (rip : s.RIP = secondEntry v)
    (hasher : HasherAt s (rspOf s + 8#64) ByteArray.empty v.initialHash)
    (count : s.regValue .r15 = BitVec.ofNat 64 inputs.size)
    (pointer : memLoad s.external (rspOf s + 216#64) 64 = initial.regValue .rdi)
    (length : memLoad s.external (rspOf s + 224#64) 64 = initial.regValue .rdx)
    (firstBytes : (TwoOutputs.outputRegion (routine v) initial).HasBytes s.external first) :
    ∃ f hash, ExecutionState initial f (regions (routine v) initial) ∧
      rspOf f = stackPtr initial - 360#64 ∧ f.RIP = lastLoadPC v ∧
      HashStateAt f (rspOf f + 176#64) hash ∧ v.serializeHash hash = v.hash (message inputs) ∧
      (TwoOutputs.outputRegion (routine v) initial).HasBytes f.external first ∧
      (∀ slot, 296 ≤ slot → slot ≤ 360 →
        memLoad f.external (stackPtr initial - 360#64 + BitVec.ofNat 64 slot) 64 =
          memLoad s.external (stackPtr initial - 360#64 + BitVec.ofNat 64 slot) 64) := by
  obtain ⟨d,stateD,rspD,memoryD,branch⟩ := second_dispatched v machine call state rsp rip hasher count pointer length
  have stack : Stack.Valid initial 832 := by simpa only [routine_stack] using call.stack
  have finished : ∃ t, ExecutionState initial t (regions (routine v) initial) ∧
      rspOf t = stackPtr initial - 360#64 ∧ t.RIP = lastClonePC v ∧
      HasherAt t (rspOf t + 8#64) (message inputs) v.initialHash ∧
      (TwoOutputs.outputRegion (routine v) initial).HasBytes t.external first ∧
      (∀ slot, 296 ≤ slot → slot ≤ 360 →
        memLoad t.external (stackPtr initial - 360#64 + BitVec.ofNat 64 slot) 64 =
          memLoad s.external (stackPtr initial - 360#64 + BitVec.ofNat 64 slot) 64) := by
    rcases branch with ⟨empty,ripD,hasherD⟩ | ⟨loop,data,separation⟩
    · have msg : message inputs = ByteArray.empty := by
        rw [Array.eq_empty_of_size_eq_zero empty]; rfl
      refine ⟨d,stateD,rspD,ripD,?_,?_,?_⟩
      · rw [msg]; exact hasherD
      · simpa only [memoryD] using firstBytes
      · intro slot _ _; rw [memoryD]
    · obtain ⟨t,done⟩ := traversed v true stride machine call stateD loop data separation
      have rspT : rspOf t = stackPtr initial - 360#64 := done.rsp
      refine ⟨t,done.state,rspT,done.rip,?_,?_,?_⟩
      · rw [rspT]; exact done.hasher
      · apply Last.frame_preserves_output call done.memory
          (by simpa only [routine_stack, ite_true] using (Table.footprint_subset_stack
            (finalizeLastTable_wellFormed v) stack))
        simpa only [memoryD] using firstBytes
      · intro slot low high
        rw [table_saved true call stateD done slot (by omega) high, memoryD]
  obtain ⟨t,stateT,rspT,ripT,hasherT,firstT,savedT⟩ := finished
  obtain ⟨f,hash,stateF,rspF,ripF,words,digest,firstF,savedF⟩ :=
    last_hashed v stride machine call stateT rspT ripT hasherT firstT
  exact ⟨f,hash,stateF,rspF,ripF,words,digest,firstF,
    fun slot low high => (savedF slot low high).trans (savedT slot low high)⟩

theorem second_completed [bindings : Bindings] (v : Wrapper.Variant)
    {initial s : RamState} {inputs : Array Input}
    (stride : UnitStringStride bindings) (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall (routine v) initial inputs)
    (state : ExecutionState initial s (regions (routine v) initial))
    (rsp : rspOf s = stackPtr initial - 360#64) (rip : s.RIP = secondEntry v)
    (hasher : HasherAt s (rspOf s + 8#64) ByteArray.empty v.initialHash)
    (count : s.regValue .r15 = BitVec.ofNat 64 inputs.size)
    (pointer : memLoad s.external (rspOf s + 216#64) 64 = initial.regValue .rdi)
    (length : memLoad s.external (rspOf s + 224#64) 64 = initial.regValue .rdx)
    (second : memLoad s.external (rspOf s + 304#64) 64 = initial.regValue .r8)
    (first : (TwoOutputs.outputRegion (routine v) initial).HasBytes s.external (v.hash (message inputs)))
    (saved : ∀ (r : BitVec 5) (offset : Nat),
      (r, offset) ∈ [(3,0),(12,8),(13,16),(14,24),(15,32)] →
      memLoad s.external (rspOf s + BitVec.ofNat 64 (312 + offset)) 64 =
        (Operand.reg r : Operand 64).read initial)
    (savedRbp : memLoad s.external (rspOf s + 352#64) 64 = (Operand.reg 5 : Operand 64).read initial)
    (returnWord : memLoad s.external (stackPtr initial) 64 = (returnBoundary initial).rip) :
    ∃ fuel final, UniqueExecution initial fuel final ∧ SupportedMachine bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧ DirectionFlagUnset final ∧
      MemoryWriteFrame initial final (regions (routine v) initial) ∧
      (TwoOutputs.outputRegion (routine v) initial).HasBytes final.external (v.hash (message inputs)) ∧
      (TwoOutputs.secondOutputRegion (routine v) initial).HasBytes final.external (v.hash (message inputs)) := by
  obtain ⟨f,hash,stateF,rspF,ripF,words,digest,firstF,savedF⟩ :=
    second_hashed v stride machine call state rsp rip hasher count pointer length first
  have secondF : memLoad f.external (rspOf f + 304#64) 64 = initial.regValue .r8 := by
    rw [rspF, savedF 304 (by decide) (by decide), ← rsp]; exact second
  obtain ⟨t,stateT,ripT,firstT,secondT,rspT,frameT⟩ :=
    last_serialized v machine call stateF rspF ripF words secondF firstF
  have stackT : rspOf t = stackPtr initial - 360#64 := rspT.trans rspF
  have savedT (slot : Nat) (low : 296 ≤ slot) (high : slot ≤ 360) :
      memLoad t.external (rspOf t + BitVec.ofNat 64 slot) 64 =
        memLoad s.external (rspOf s + BitVec.ofNat 64 slot) 64 := by
    rw [stackT, Last.output_word (depth := 360) call (by simp) frameT (by rw [routine_stack]; decide) slot high,
      savedF slot low high, ← rsp]
  have abi : ∀ (r : BitVec 5) (offset : Nat),
      (r, offset) ∈ [(3,0),(12,8),(13,16),(14,24),(15,32)] →
      memLoad t.external (rspOf t + BitVec.ofNat 64 (312 + offset)) 64 =
        (Operand.reg r : Operand 64).read initial := by
    intro r offset member
    have bound : offset ≤ 32 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
      omega
    exact (savedT (312 + offset) (by omega) (by omega)).trans (saved r offset member)
  have rbp : memLoad t.external (rspOf t + 352#64) 64 = (Operand.reg 5 : Operand 64).read initial :=
    (savedT 352 (by decide) (by decide)).trans savedRbp
  have ret : memLoad t.external (stackPtr initial) 64 = (returnBoundary initial).rip := by
    have h := savedT 360 (by decide) (by decide)
    rw [stackT, rsp, BitVec.sub_add_cancel] at h
    exact h.trans returnWord
  obtain ⟨fuel,final,run,mach,abiFinal,df,frame,memory⟩ := returned_at (routine v) .six312
    (returnPC v) rfl (by rw [routine_stack]; decide) machine call stateT stackT ripT abi rbp
    (return_inside v) (return_code v stateT.loaded) ret
  refine ⟨fuel,final,run,mach,abiFinal,df,frame,?_,?_⟩
  · simpa only [memory] using firstT
  · rw [memory, ← digest]; exact secondT

theorem first_completed [bindings : Bindings] (v : Wrapper.Variant)
    {initial n : RamState} {inputs : Array Input}
    (stride : UnitStringStride bindings) (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall (routine v) initial inputs)
    (state : ExecutionState initial n (regions (routine v) initial))
    (prepared : Finalize.Prepared (Finalization.finalizeFirst.layout v)
      (stackPtr initial - 360#64) (message inputs) n)
    (output : n.regValue .r13 = initial.regValue .rcx)
    (count : n.regValue .r15 = BitVec.ofNat 64 inputs.size) :
    ∃ t, ExecutionState initial t (regions (routine v) initial) ∧
      rspOf t = stackPtr initial - 360#64 ∧ t.RIP = secondEntry v ∧
      t.regValue .r15 = BitVec.ofNat 64 inputs.size ∧
      HasherAt t (rspOf t + 8#64) ByteArray.empty v.initialHash ∧
      (TwoOutputs.outputRegion (routine v) initial).HasBytes t.external (v.hash (message inputs)) ∧
      (∀ slot, 216 ≤ slot → slot ≤ 360 →
        memLoad t.external (stackPtr initial - 360#64 + BitVec.ofNat 64 slot) 64 =
          memLoad n.external (stackPtr initial - 360#64 + BitVec.ofNat 64 slot) 64) := by
  obtain ⟨f,hash,stateF,rspF,ripF,words,digest,base,outputF,countF,savedF⟩ :=
    first_finalized v stride machine call state prepared output count
  obtain ⟨a,b,t,stateT,load,store,init,rspT,ripT,empty,bytes,storeFrame⟩ :=
    first_serialized v machine call stateF rspF ripF words base outputF
  have rspA : rspOf a = rspOf f := load.agrees.read (n := 64) (r := 4)
    (by cases v <;> simp [Serialize.effect, Effect.components])
  have rspB : rspOf b = rspOf a := store.agrees.read (n := 64) (r := 4)
    (by cases v <;> simp [Serialize.effect, Effect.components])
  have memoryA : a.external = f.external := load.agrees.external
    (by cases v <;> simp [Serialize.effect, Effect.components, Component.Covers])
  have countA : a.regValue .r15 = f.regValue .r15 := load.agrees.read (n := 64) (r := 15)
    (by cases v <;> simp [Serialize.effect, Effect.components])
  have countB : b.regValue .r15 = a.regValue .r15 := store.agrees.read (n := 64) (r := 15)
    (by cases v <;> simp [Serialize.effect, Effect.components])
  have countT : t.regValue .r15 = b.regValue .r15 := init.frame.read (n := 64) (r := 15)
    (by cases v <;> simp [Initialize.Layout.components, Initialization.layout,
      Initialization.word, Initialization.temporary])
  refine ⟨t,stateT,rspT,ripT,countT.trans (countB.trans (countA.trans countF)),empty,?_,?_⟩
  · rw [← digest]; exact bytes
  · intro slot low high
    have initSaved := Reset.initialize_saved init slot (Or.inr (by
      change 8 + 104 ≤ slot; omega)) high
    have stackB : rspOf b = stackPtr initial - 360#64 := rspB.trans (rspA.trans rspF)
    rw [stackB] at initSaved
    rw [initSaved, Last.output_word (depth := 360) call (by simp) storeFrame
      (by rw [routine_stack]; decide) slot high, memoryA]
    exact savedF slot low high

theorem correct [bindings : Bindings] (v : Wrapper.Variant)
    {initial : RamState} {inputs : Array Input}
    (stride : UnitStringStride bindings) (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall (routine v) initial inputs) :
    ∃ fuel final, UniqueExecution initial fuel final ∧ SupportedMachine bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧ DirectionFlagUnset final ∧
      MemoryWriteFrame initial final (regions (routine v) initial) ∧
      (TwoOutputs.outputRegion (routine v) initial).HasBytes final.external (v.hash (message inputs)) ∧
      (TwoOutputs.secondOutputRegion (routine v) initial).HasBytes final.external (v.hash (message inputs)) := by
  obtain ⟨p,h,u,s,push,args,init,stateS,data,separation,rspS,pointer,length,second,count,branch⟩ :=
    FinalizePrefix.dispatched v machine call
  have frame : AgreesExcept [.mem (rspOf u + 296#64) 8, .reg 14#5, .flags, .rip] u s := by
    rcases branch with ⟨_,_,_,_,_,frame⟩ | ⟨_,_,frame⟩
    · apply frame.mono; simp
    · exact frame
  have rspSU : rspOf s = rspOf u := frame.read (n := 64) (r := 4) (by simp)
  have abi := FinalizePrefix.dispatched_saved push args init rspSU frame
  have branch' :
      (inputs.size = 0 ∧ s.RIP = Normalize.emptyEntry v .finalize ∧
        HasherAt s (rspOf s + 8#64) ByteArray.empty v.initialHash ∧
        s.regValue .r13 = initial.regValue .rcx) ∨
      (Table.LoopState (finalizeFirstTable v) ((finalizeFirstTable v).chunk.sp initial) inputs 0 s ∧
        memLoad s.external (rspOf s + 296#64) 64 = initial.regValue .rcx) := by
    rcases branch with ⟨empty,rip,_,hasher,output,_⟩ | ⟨loop,output,_⟩
    · refine .inl ⟨empty,?_,?_,output⟩
      · exact rip.trans (by cases v <;> decide +kernel)
      · rw [show rspOf s = stackPtr initial - 360#64 from rspS]; exact hasher
    · refine .inr ⟨loop,?_⟩
      rw [show rspOf s = stackPtr initial - 360#64 from rspS]; exact output
  obtain ⟨n,stateN,prepared,outputN,savedN,countN⟩ :=
    first_prepared v stride machine call stateS rspS data separation count branch'
  obtain ⟨t,stateT,rspT,ripT,countT,empty,first,savedT⟩ :=
    first_completed v stride machine call stateN prepared outputN countN
  have saved (slot : Nat) (low : 216 ≤ slot) (high : slot ≤ 360) :
      memLoad t.external (rspOf t + BitVec.ofNat 64 slot) 64 =
        memLoad s.external (rspOf s + BitVec.ofNat 64 slot) 64 := by
    rw [rspT, show rspOf s = stackPtr initial - 360#64 from rspS]
    exact (savedT slot low high).trans (savedN slot low high)
  have pointerT : memLoad t.external (rspOf t + 216#64) 64 = initial.regValue .rdi := by
    rw [saved 216 (by decide) (by decide), show rspOf s = stackPtr initial - 360#64 from rspS]
    exact pointer
  have lengthT : memLoad t.external (rspOf t + 224#64) 64 = initial.regValue .rdx := by
    rw [saved 224 (by decide) (by decide), show rspOf s = stackPtr initial - 360#64 from rspS]
    exact length
  have secondT : memLoad t.external (rspOf t + 304#64) 64 = initial.regValue .r8 := by
    rw [saved 304 (by decide) (by decide), show rspOf s = stackPtr initial - 360#64 from rspS]
    exact second
  have registers : ∀ (r : BitVec 5) (offset : Nat),
      (r, offset) ∈ [(3,0),(12,8),(13,16),(14,24),(15,32)] →
      memLoad t.external (rspOf t + BitVec.ofNat 64 (312 + offset)) 64 =
        (Operand.reg r : Operand 64).read initial := by
    intro r offset member
    have bounds : offset ≤ 32 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
      omega
    apply (saved (312+offset) (by omega) (by omega)).trans
    exact abi.1 r offset (List.mem_append_left [(5,40)] member)
  have rbp : memLoad t.external (rspOf t + 352#64) 64 = (Operand.reg 5 : Operand 64).read initial :=
    (saved 352 (by decide) (by decide)).trans (abi.1 5 40 (by simp))
  have ret : memLoad t.external (stackPtr initial) 64 = (returnBoundary initial).rip := by
    have h := (saved 360 (by decide) (by decide)).trans abi.2
    rw [rspT, BitVec.sub_add_cancel] at h
    exact h
  exact second_completed v stride machine call stateT rspT ripT empty countT pointerT lengthT
    secondT first registers rbp ret

end Sha2.Proofs.Reset.FinalizeIntoReset
