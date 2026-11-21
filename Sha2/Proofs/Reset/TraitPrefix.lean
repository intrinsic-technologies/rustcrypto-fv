import Sha2.Proofs.Reset.Prefix
import Sha2.Proofs.Reset.Dispatch

set_option autoImplicit false

namespace Sha2.Proofs.Reset.TraitPrefix

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.Instructions

def offset : Wrapper.Variant → Nat
  | .sha224 => 0x1558
  | .sha256 => 0x31a8

def pc (v : Wrapper.Variant) (i : Nat := 0) : BitVec 64 :=
  Extracted.textAddress + BitVec.ofNat 64 (offset v + i)

def saveBytes : List UInt8 := [0x48, 0x89, 0x74, 0x24, 0x68]

def tailBytes : List UInt8 :=
  [0x4c, 0x89, 0xa4, 0x24, 0x28, 1, 0, 0, 0x45, 0x31, 0xff,
   0x49, 0x89, 0xe5, 0x48, 0x8d, 0x54, 0x24, 0x70, 0xeb, 0x41]

structure SavePre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  write : MemWritable s (rspOf s + 104) 8
  apart : RangeApart (rspOf s + 104) 8 p 5

def saveEffect (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p + 5
    writes := [⟨(.mem (rspOf s + 104) : Operand 64), (.reg 6 : Operand 64).read s⟩] }

theorem save [Bindings] (p : BitVec 64) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p 5) :
    AdvanceTriple boundary (SavePre p) (codeRange p saveBytes)
      (Effect.post (saveEffect p)) := by
  advance_reloc_begin (mov_m64_r64_effect_step p 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d8 104)) (by decide) rfl rfl)
    next (boundary_ne_program outside (inside 5 (by decide)))
  apply AdvanceTriple.block_end
  intro s t _ h
  apply h.weaken
  · x86_norm [saveEffect]
  · x86_norm [saveEffect]
    congr 2 <;> decide +kernel
  · intro i; cases i <;> x86_norm [saveEffect]
  · x86_norm [saveEffect]

structure TailPre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  write : MemWritable s (rspOf s + 296) 8
  apart : RangeApart (rspOf s + 296) 8 p 21

def tailEffect (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p + 86
    writes := [⟨(.mem (rspOf s + 296) : Operand 64), (.reg 12 : Operand 64).read s⟩,
      ⟨(.reg 15 : Operand 64), 0⟩, ⟨(.reg 13 : Operand 64), rspOf s⟩,
      ⟨(.reg 2 : Operand 64), rspOf s + 112⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem tail [Bindings] (p : BitVec 64) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p 21)
    (target : InProgram (p + 86)) :
    AdvanceTriple boundary (TailPre p) (codeRange p tailBytes)
      (Effect.post (tailEffect p)) := by
  have low : (branchTarget (p + 19) 2 ((65 : BitVec 8).signExtend 64)).toNat < 2^32 := by
    obtain ⟨byte, mem⟩ := target
    have bound := programSections_low.codeLow (_, byte) mem
    simpa [branchTarget, BitVec.add_assoc, Prelude.userAddressLimit] using bound
  advance_reloc_begin (mov_m64_r64_effect_step p 0x4c (by simp [RexWPrefix]) 4
    (.sib 4 none 0 (.d32 296)) (by decide) rfl rfl)
    next (boundary_ne_program outside (inside 8 (by decide)))
  advance_reloc_then (StepEffect.forgetFlags (h := xor_r32_r32_rex_effect_step
    (p + 8) 0x45 0xff (by simp [RexNoWPrefix]) rfl))
    next (boundary_ne_program outside (inside 11 (by decide)))
  advance_reloc_then (mov_r64_r64_effect_step (p + 11) 0x49 0xe5
    (by simp [RexWPrefix]) rfl)
    next (boundary_ne_program outside (inside 14 (by decide)))
  advance_reloc_then (lea_r64_effect_step (p + 14) 0x48 (by simp [RexWPrefix]) 2
    (.sib 4 none 0 (.d8 112)) (by decide) rfl rfl)
    next (boundary_ne_program outside (inside 19 (by decide)))
  advance_reloc_then (jmp_rel8_effect_step (p + 19) 65 low)
    next (boundary_ne_program outside target)
  apply AdvanceTriple.block_end
  intro s t _ h
  apply h.weaken
  · x86_norm [tailEffect]
  · x86_norm [tailEffect]
    refine ⟨?_, ?_, ?_⟩
    · congr 2 <;> decide +kernel
    · change 0#64 = ((Operand.read s (.reg 15 : Operand 32)) ^^^
        (Operand.read s (.reg 15 : Operand 32))).setWidth 64
      simp
    · congr 2 <;> decide +kernel
  · intro i; cases i <;> x86_norm [tailEffect]
  · x86_norm [tailEffect]

theorem inside (v : Wrapper.Variant) : BlockInProgram (pc v) 341 :=
  blockInProgram_of_textOffset (offset v) 341 (by cases v <;> decide +kernel)

theorem save_code (v : Wrapper.Variant) {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (pc v) saveBytes) s :=
  programText_slice (programLoaded_codeIn loaded) (offset v) saveBytes
    (by cases v <;> decide +kernel) (by cases v <;> decide +kernel)

theorem branch_code (v : Wrapper.Variant) {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (pc v 5) (Dispatch.branchBytes 0x147 6)) s :=
  programText_slice (programLoaded_codeIn loaded) (offset v + 5) (Dispatch.branchBytes 0x147 6)
    (by cases v <;> decide +kernel) (by cases v <;> decide +kernel)

theorem tail_code (v : Wrapper.Variant) {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (pc v 14) tailBytes) s :=
  programText_slice (programLoaded_codeIn loaded) (offset v + 14) tailBytes
    (by cases v <;> decide +kernel) (by cases v <;> decide +kernel)


theorem pc_add (v : Wrapper.Variant) (i j : Nat) :
    pc v i + BitVec.ofNat 64 j = pc v (i + j) := by
  simp only [pc, BitVec.ofNat_add, BitVec.add_assoc]

theorem inside_at (v : Wrapper.Variant) (i n : Nat) (bound : i + n ≤ 341) :
    BlockInProgram (pc v i) n := by
  intro j hj
  rw [pc_add]
  simpa only [pc_add, Nat.zero_add] using inside v (i+j) (by omega)

private theorem regions_avoid {routine : Routine} {initial : RamState} {inputs : Array Input}
    (call : TwoOutputs.ValidCall routine initial inputs) :
    ∀ region ∈ regions routine initial, region.Avoids InProgram := by
  intro region member a ha hp
  have mem : region ∈ [TwoOutputs.outputRegion routine initial,
      TwoOutputs.secondOutputRegion routine initial, Stack.region initial routine.minStackBytes] := by
    simpa only [regions, Vector.mem_mk, List.mem_toArray] using member
  exact (call.separation.2 region mem).2 a ha (.inl hp)

private theorem slot_pre [Bindings] {routine : Routine} {initial s : RamState}
    {inputs : Array Input} (call : TwoOutputs.ValidCall routine initial inputs)
    (state : ExecutionState initial s (regions routine initial))
    (rsp : rspOf s = stackPtr initial - 360#64)
    (capacity : 360 ≤ routine.minStackBytes) {slot len : Nat} {p : BitVec 64}
    (bound : slot + 8 ≤ 360) (inside : BlockInProgram p len) :
    MemWritable s (rspOf s + BitVec.ofNat 64 slot) 8 ∧
      RangeApart (rspOf s + BitVec.ofNat 64 slot) 8 p len := by
  have avoid := (call.separation.2 (Stack.region initial routine.minStackBytes) (by simp)).2
  rw [rsp]
  exact ⟨stack_frame_writable call.stack capacity (fun a ha h => avoid a ha (.inr h))
    state.allocated bound (by decide),
    stack_frame_codeApart call.stack capacity (fun a ha h => avoid a ha (.inl h))
      bound (fun j hj => inside j (Nat.le_of_lt hj))⟩

private theorem lift [Bindings] {routine : Routine} {initial s t : RamState}
    {inputs : Array Input} {fuel slot : Nat} {e : Effect}
    (call : TwoOutputs.ValidCall routine initial inputs)
    (state : ExecutionState initial s (regions routine initial))
    (rsp : rspOf s = stackPtr initial - 360#64)
    (capacity : 360 ≤ routine.minStackBytes) (bound : slot + 8 ≤ 360)
    (run : Advances (returnBoundary initial) fuel s t) (ready : ReadyToStep t)
    (effect : e.Holds s t)
    (memory : ∀ c ∈ e.components, ∀ a, c.Covers a →
      Component.Covers (.mem (rspOf s + BitVec.ofNat 64 slot) 8) a)
    (df : .df ∉ e.components) : ExecutionState initial t (regions routine initial) := by
  apply state.of_agrees (regions_avoid call) run ready effect.agrees _ df
  intro c hc a ha
  refine ⟨Stack.region initial routine.minStackBytes, by simp [regions], ?_⟩
  have covered := memory c hc a ha
  rw [rsp] at covered
  exact stack_frame_contains call.stack capacity bound covered

theorem save_state [bindings : Bindings] (v : Wrapper.Variant)
    {routine : Routine} {initial s : RamState} {inputs : Array Input}
    (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall routine initial inputs)
    (state : ExecutionState initial s (regions routine initial))
    (capacity : 360 ≤ routine.minStackBytes)
    (rsp : rspOf s = stackPtr initial - 360#64) (rip : s.RIP = pc v) :
    ∃ t, ExecutionState initial t (regions routine initial) ∧
      (saveEffect (pc v) s).Holds s t := by
  have ins := inside_at v 0 5 (by decide)
  obtain ⟨write, apart⟩ := slot_pre call state rsp capacity (slot := 104) (by decide) ins
  obtain ⟨fuel, t, run, ready, _, result⟩ := save (pc v) (returnBoundary initial)
    (valid_return_boundary machine call.stack call.returnAddress).2.2 ins s
    (supportedMachine_readyToStep state.machine) (save_code v state.loaded) ⟨rip, write, apart⟩
  refine ⟨t, lift call state rsp capacity (slot := 104) (by decide) run ready result ?_ ?_, result⟩
  · intro c hc a ha
    simp only [saveEffect, Effect.components, List.map_cons, List.map_nil, Write.component,
      Operand.component, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ha
    · exact ha.elim
  · simp [saveEffect, Effect.components]

theorem tail_state [bindings : Bindings] (v : Wrapper.Variant)
    {routine : Routine} {initial s : RamState} {inputs : Array Input}
    (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall routine initial inputs)
    (state : ExecutionState initial s (regions routine initial))
    (capacity : 360 ≤ routine.minStackBytes)
    (rsp : rspOf s = stackPtr initial - 360#64) (rip : s.RIP = pc v 14) :
    ∃ t, ExecutionState initial t (regions routine initial) ∧
      (tailEffect (pc v 14) s).Holds s t := by
  have ins := inside_at v 14 21 (by decide)
  obtain ⟨write, apart⟩ := slot_pre call state rsp capacity (slot := 296) (by decide) ins
  obtain ⟨fuel, t, run, ready, _, result⟩ := tail (pc v 14) (returnBoundary initial)
    (valid_return_boundary machine call.stack call.returnAddress).2.2 ins
    (by simpa [pc, BitVec.ofNat_add, BitVec.add_assoc] using inside v 100 (by decide)) s
    (supportedMachine_readyToStep state.machine) (tail_code v state.loaded) ⟨rip, write, apart⟩
  refine ⟨t, lift call state rsp capacity (slot := 296) (by decide) run ready result ?_ ?_, result⟩
  · intro c hc a ha
    simp only [tailEffect, Effect.components, List.map_cons, List.map_nil, Write.component,
      Operand.component, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ha
    all_goals exact ha.elim
  · simp [tailEffect, Effect.components]


open Sha2.Proofs.Common.SHA256 Sha2.Proofs.Common.SHA256.Absorb
open Sha2.Proofs.Common.SHA256.Instances Sha2.Proofs.Common.SHA256.Instances.Absorption

private theorem byte_preserved {s t : RamState} {sp : BitVec 64} {cs : List Component}
    (frame : AgreesExcept cs s t)
    (memory : ∀ c ∈ cs, ∀ a, c.Covers a →
      (.mem (sp + 104) 8 : Component).Covers a ∨ (.mem (sp + 296) 8 : Component).Covers a)
    (i : Nat) (lo : 112 ≤ i) (hi : i < 296) :
    t.external[sp + BitVec.ofNat 64 i]? = s.external[sp + BitVec.ofNat 64 i]? := by
  apply frame.byte
  intro c hc covered
  rcases memory c hc _ covered with h | h
  all_goals obtain ⟨j, hj, he⟩ := h
  · exact OffsetsApart.ne (c₁ := 104) (len₁ := 8) (c₂ := 112) (len₂ := 184)
      (by unfold OffsetsApart; decide +kernel) sp hj (show i - 112 < 184 by omega)
      (by decide) (by
        have eq : sp + 112 + BitVec.ofNat 64 (i - 112) = sp + BitVec.ofNat 64 i := by
          change sp + BitVec.ofNat 64 112 + BitVec.ofNat 64 (i - 112) = _
          rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 112 + (i - 112) = i by omega]
        rw [eq]
        exact he.symm)
  · exact OffsetsApart.ne (c₁ := 296) (len₁ := 8) (c₂ := 112) (len₂ := 184)
      (by unfold OffsetsApart; decide +kernel) sp hj (show i - 112 < 184 by omega)
      (by decide) (by
        have eq : sp + 112 + BitVec.ofNat 64 (i - 112) = sp + BitVec.ofNat 64 i := by
          change sp + BitVec.ofNat 64 112 + BitVec.ofNat 64 (i - 112) = _
          rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 112 + (i - 112) = i by omega]
        rw [eq]
        exact he.symm)

theorem save_memory {p : BitVec 64} {s t : RamState}
    (h : (saveEffect p s).Holds s t) (i : Nat) (lo : 112 ≤ i) (hi : i < 296) :
    t.external[rspOf s + BitVec.ofNat 64 i]? = s.external[rspOf s + BitVec.ofNat 64 i]? := by
  apply byte_preserved h.agrees _ i lo hi
  intro c hc a ha
  simp only [saveEffect, Effect.components, List.map_cons, List.map_nil, Write.component,
    Operand.component, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact Or.inl ha
  · exact ha.elim

theorem tail_memory {p : BitVec 64} {s t : RamState}
    (h : (tailEffect p s).Holds s t) (i : Nat) (lo : 112 ≤ i) (hi : i < 296) :
    t.external[rspOf s + BitVec.ofNat 64 i]? = s.external[rspOf s + BitVec.ofNat 64 i]? := by
  apply byte_preserved h.agrees _ i lo hi
  intro c hc a ha
  simp only [tailEffect, Effect.components, List.map_cons, List.map_nil, Write.component,
    Operand.component, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inr ha
  all_goals exact ha.elim


theorem loop_state (v : Wrapper.Variant) {u a b s : RamState} {inputs : Array Input}
    (saved : (saveEffect (pc v) u).Holds u a)
    (branch : (Dispatch.branchEffect (pc v 5) a 0x147 6).Holds a b)
    (tail : (tailEffect (pc v 14) b).Holds b s)
    (hasher : HasherAt u (rspOf u + 112) ByteArray.empty v.initialHash)
    (count : u.regValue .rsi = BitVec.ofNat 64 inputs.size)
    (nonempty : 0 < inputs.size) :
    Table.LoopState (traitFirst v) (rspOf u) inputs 0 s := by
  have rspA : rspOf a = rspOf u := saved.agrees.read (n := 64) (r := 4)
    (by simp [saveEffect, Effect.components])
  have frameB : AgreesExcept [.flags, .rip] a b := branch.agrees
  have rspB : rspOf b = rspOf u := (frameB.read (by simp)).trans rspA
  have rspS : rspOf s = rspOf u := (tail.agrees.read (n := 64) (r := 4)
    (by simp [tailEffect, Effect.components])).trans rspB
  have bytes (i : Nat) (hi : i < 104) :
      s.external[rspOf u + 112 + BitVec.ofNat 64 i]? =
        u.external[rspOf u + 112 + BitVec.ofNat 64 i]? := by
    have addr : rspOf u + 112 + BitVec.ofNat 64 i = rspOf u + BitVec.ofNat 64 (112+i) := by
      simp [BitVec.ofNat_add, BitVec.add_assoc]
    rw [addr, ← rspB, tail_memory tail (112+i) (by omega) (by omega), rspB]
    rw [frameB.byte (by simp [Component.Covers]), save_memory saved (112+i) (by omega) (by omega)]
  have savedCount : memLoad a.external (rspOf u + 104) 64 = u.regValue .rsi := saved.writes
  have countB : memLoad b.external (rspOf u + 104) 64 = u.regValue .rsi := by
    exact (Common.Encoding.Serialize.read_mem_of_agrees frameB _ (by simp [Component.Covers])).trans savedCount
  have countS : memLoad s.external (rspOf u + 104) 64 = u.regValue .rsi := by
    apply Eq.trans (Common.Encoding.Serialize.read_mem_of_agrees tail.agrees _ ?_) countB
    intro i hi c hc covered
    simp only [tailEffect, Effect.components, List.map_cons, List.map_nil, Write.component,
      Operand.component, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨j, hj, he⟩ := covered
      rw [rspB] at he
      exact OffsetsApart.ne (by unfold OffsetsApart; decide +kernel) (rspOf u) hj hi (by decide) he.symm
    all_goals exact covered.elim
  have writes : memLoad s.external (rspOf b + 296) 64 = b.regValue .r12 ∧
      s.regValue .r15 = 0 ∧ s.regValue .r13 = rspOf b ∧ s.regValue .rdx = rspOf b + 112 := tail.writes
  refine ⟨?_, rspS, ?_, writes.2.1, countS.trans count, nonempty, ?_, ?_, ?_, ?_⟩
  · rw [tail.rip]
    change pc v 14 + 86 = (traitFirst v).head
    cases v <;> decide +kernel
  · rw [Wrapper.prefixMessage_zero]
    exact hasher.of_bytes bytes
  · intro eq
    have impossible : (traitFirst v).cloneIn ≠ [] := by cases v <;> decide +kernel
    exact (impossible eq).elim
  · intro r hr
    have eq : r = 13 := by simpa only [traitFirst, Option.mem_def, Option.some.injEq] using hr.symm
    subst r
    change s.regValue .r13 = rspOf u + 0#64
    simpa only [rspB, BitVec.add_zero] using writes.2.2.1
  · intro _
    change s.regValue .rdx = rspOf u + 112
    simpa only [rspB] using writes.2.2.2
  · intro call hc r he
    cases v <;> simp only [traitFirst, List.mem_cons, List.not_mem_nil, or_false] at hc
    all_goals rcases hc with rfl | rfl | rfl <;> cases he


def changes (sp : BitVec 64) : List Component :=
  [.mem (sp + 104) 8, .mem (sp + 296) 8, .reg 15, .reg 13, .reg 2, .flags, .rip]

set_option maxHeartbeats 800000 in
theorem dispatched [bindings : Bindings] (v : Wrapper.Variant)
    {initial : RamState} {inputs : Array Input}
    (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall (Header.Layout.trait.routine v) initial inputs) :
    ∃ p h u s,
      (Prologue.effect (Header.Layout.trait.routine v).entryAddress .six312 initial).Holds initial p ∧
      (Header.effectAt .trait (Header.Layout.trait.pc v) p).Holds p h ∧
      Initialize.Post (Initialization.traitInitial.layout v) (rspOf h + 112) h u ∧
      ExecutionState initial s (regions (Header.Layout.trait.routine v) initial) ∧
      Table.InputData (traitFirst v) ((traitFirst v).chunk.sp initial) inputs s ∧
      Table.Separation (traitFirst v) initial s (Header.Layout.trait.routine v).minStackBytes inputs ∧
      stackPtr s = (traitFirst v).chunk.sp initial ∧
      AgreesExcept (changes ((traitFirst v).chunk.sp initial)) u s ∧
      memLoad s.external ((traitFirst v).chunk.sp initial + 216) 64 = initial.regValue .rdi ∧
      memLoad s.external ((traitFirst v).chunk.sp initial + 224) 64 = initial.regValue .rdx ∧
      memLoad s.external ((traitFirst v).chunk.sp initial + 304) 64 = initial.regValue .r8 ∧
      memLoad s.external ((traitFirst v).chunk.sp initial + 104) 64 = BitVec.ofNat 64 inputs.size ∧
      ((inputs.size = 0 ∧ s.RIP = pc v 341 ∧
        HasherAt s ((traitFirst v).stored ((traitFirst v).chunk.sp initial)) ByteArray.empty v.initialHash ∧
        s.regValue .r12 = initial.regValue .rcx) ∨
       (Table.LoopState (traitFirst v) ((traitFirst v).chunk.sp initial) inputs 0 s ∧
        memLoad s.external ((traitFirst v).chunk.sp initial + 296) 64 = initial.regValue .rcx)) := by
  obtain ⟨p,h,u,stateU,push,args,init,_,rspH,rspU⟩ := initialized_at .trait v machine call
  obtain ⟨pointer,length,out2,count,output,_⟩ := initialized_arguments_at push args init
  have capacity : 360 ≤ (Header.Layout.trait.routine v).minStackBytes := by cases v <;> decide +kernel
  have sp : (traitFirst v).chunk.sp initial = rspOf u := rspU.symm
  have hasher : HasherAt u (rspOf u + 112) ByteArray.empty v.initialHash := by
    rw [show rspOf u = rspOf h from init.rsp]
    exact init.hasher
  have ripU : u.RIP = pc v := by
    rw [init.rip]
    cases v <;> decide +kernel
  obtain ⟨a,stateA,saved⟩ := save_state v machine call stateU capacity rspU ripU
  have rspA : rspOf a = rspOf u := saved.agrees.read (n := 64) (r := 4)
    (by simp [saveEffect, Effect.components])
  have ripA : a.RIP = pc v 5 := by
    rw [saved.rip]
    simpa [saveEffect] using pc_add v 0 5
  obtain ⟨b,stateB,branch⟩ := branch_state machine call stateA ripA
    (branch_code v stateA.loaded) (inside_at v 5 9 (by decide))
    (by simpa [pc, BitVec.ofNat_add, BitVec.add_assoc] using inside v 341 (by decide))
  have frameB : AgreesExcept [.flags, .rip] a b := branch.agrees
  have rspB : rspOf b = rspOf u := (frameB.read (by simp)).trans rspA
  have countU : u.regValue .rsi = BitVec.ofNat 64 inputs.size :=
    count.trans (by rw [← call.countArgumentMatchesInputs]; simp)
  have countA : a.regValue .rsi = BitVec.ofNat 64 inputs.size :=
    (saved.agrees.read (n := 64) (r := 6) (by simp [saveEffect, Effect.components])).trans countU
  have countB : memLoad b.external (rspOf u + 104) 64 = BitVec.ofNat 64 inputs.size :=
    (Common.Encoding.Serialize.read_mem_of_agrees frameB _ (by simp [Component.Covers])).trans
      (saved.writes.trans countU)
  have outputB : b.regValue .r12 = initial.regValue .rcx :=
    (frameB.read (n := 64) (r := 12) (by simp)).trans
      ((saved.agrees.read (n := 64) (r := 12) (by simp [saveEffect, Effect.components])).trans output)
  have result : ∃ s, ExecutionState initial s (regions (Header.Layout.trait.routine v) initial) ∧
      stackPtr s = rspOf u ∧ AgreesExcept (changes (rspOf u)) u s ∧
      memLoad s.external (rspOf u + 104) 64 = BitVec.ofNat 64 inputs.size ∧
      ((inputs.size = 0 ∧ s.RIP = pc v 341 ∧
        HasherAt s (rspOf u + 112) ByteArray.empty v.initialHash ∧ s.regValue .r12 = initial.regValue .rcx) ∨
       (Table.LoopState (traitFirst v) (rspOf u) inputs 0 s ∧
        memLoad s.external (rspOf u + 296) 64 = initial.regValue .rcx)) := by
    by_cases empty : inputs.size = 0
    · refine ⟨b,stateB,rspB,?_,countB,Or.inl ⟨empty,?_,?_,outputB⟩⟩
      · apply (saved.agrees.trans frameB).mono
        simp [saveEffect, Effect.components, changes]
      · rw [branch.rip]
        change (if a.regValue .rsi = 0#64 then _ else _) = _
        simp only [countA, empty, BitVec.ofNat_eq_ofNat, ite_true]
        simp [pc, BitVec.ofNat_add, BitVec.add_assoc]
      · apply hasher.of_bytes
        intro i hi
        rw [frameB.byte (by simp [Component.Covers])]
        have eq : rspOf u + 112 + BitVec.ofNat 64 i = rspOf u + BitVec.ofNat 64 (112+i) := by
          simp [BitVec.ofNat_add, BitVec.add_assoc]
        rw [eq, save_memory saved (112+i) (by omega) (by omega)]
    · have nonzero : a.regValue .rsi ≠ 0#64 := by
        rw [countA]
        intro eq
        have bound := Wrapper.validCall_count_bound (firstOutput_validCall call)
        have eqNat := congrArg BitVec.toNat eq
        simp only [BitVec.toNat_ofNat] at eqNat
        rw [Nat.mod_eq_of_lt (by omega)] at eqNat
        exact empty eqNat
      have ripB : b.RIP = pc v 14 := by
        rw [branch.rip]
        simp only [Dispatch.branchEffect]
        change (if a.regValue .rsi = 0#64 then _ else _) = _
        rw [ite_eq_right (by exact nonzero)]
        exact pc_add v 5 9
      obtain ⟨s,stateS,tail⟩ := tail_state v machine call stateB capacity (rspB.trans rspU) ripB
      have loop := loop_state v saved branch tail hasher countU (by omega)
      refine ⟨s,stateS,loop.rsp,?_,loop.count,Or.inr ⟨loop,?_⟩⟩
      · apply ((saved.agrees.trans frameB).trans tail.agrees).mono
        simp [saveEffect, tailEffect, Effect.components, changes, rspB]
      · rw [← rspB]
        exact tail.writes.1.trans outputB
  obtain ⟨s,stateS,rspS,frame,countS,outcome⟩ := result
  have slot (n : Nat) (member : n ∈ [216,224,304]) :
      memLoad s.external (rspOf u + BitVec.ofNat 64 n) 64 =
        memLoad u.external (rspOf u + BitVec.ofNat 64 n) 64 := by
    apply Common.Encoding.Serialize.read_mem_of_agrees frame
    intro i hi c hc covered
    simp only [changes, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    all_goals obtain ⟨j,hj,he⟩ := covered
    all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    all_goals rcases member with rfl | rfl | rfl
    all_goals
      exact OffsetsApart.ne (by unfold OffsetsApart; decide +kernel)
        (rspOf u) hj hi (by decide) he.symm
  have ptr := (slot 216 (by simp)).trans pointer
  have len := (slot 224 (by simp)).trans length
  have out := (slot 304 (by simp)).trans out2
  refine ⟨p,h,u,s,push,args,init,stateS,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [sp]
    exact table_inputData call stateS.frame _ _ ptr len
  · apply table_separation call
    · rw [sp]; exact ptr
    · rw [sp]; exact len
  · rw [sp]; exact rspS
  · rw [sp]; exact frame
  · rw [sp]; exact ptr
  · rw [sp]; exact len
  · rw [sp]; exact out
  · rw [sp]; exact countS
  · rw [sp]
    exact outcome

theorem dispatched_saved {v : Wrapper.Variant} {initial p h u s : RamState}
    (push : (Prologue.effect (Header.Layout.trait.routine v).entryAddress .six312 initial).Holds initial p)
    (args : (Header.effectAt .trait (Header.Layout.trait.pc v) p).Holds p h)
    (init : Initialize.Post (Initialization.traitInitial.layout v) (rspOf h + 112#64) h u)
    (rsp : rspOf s = rspOf u)
    (frame : AgreesExcept (changes (rspOf u)) u s) :
    (∀ (r : BitVec 5) (offset : Nat),
      (r, offset) ∈ [(3,0),(12,8),(13,16),(14,24),(15,32),(5,40)] →
      memLoad s.external (rspOf s + BitVec.ofNat 64 (312 + offset)) 64 =
        (Operand.reg r : Operand 64).read initial) ∧
    memLoad s.external (rspOf s + 360#64) 64 = memLoad initial.external (stackPtr initial) 64 := by
  apply initialized_abi_after .trait push args init rsp frame
  intro c hc a covered
  simp only [changes, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨i,hi,he⟩ := covered
    refine ⟨104+i, ?_, ?_⟩
    · change 104+i < 312
      omega
    · simpa only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using he
  · obtain ⟨i,hi,he⟩ := covered
    refine ⟨296+i, ?_, ?_⟩
    · change 296+i < 312
      omega
    · simpa only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using he
  all_goals exact covered.elim

end Sha2.Proofs.Reset.TraitPrefix
