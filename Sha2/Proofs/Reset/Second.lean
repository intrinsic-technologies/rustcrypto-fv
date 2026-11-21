import Sha2.Proofs.Reset.Serialize
import Sha2.Proofs.Reset.Dispatch
import Sha2.Proofs.Reset.Prefix
import Sha2.Proofs.Reset.Inputs
import Sha2.Proofs.Reset.Layouts
import Sha2.Proofs.Reset.Normalize
import Sha2.Proofs.Common.Instructions.ForgetFlags
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.Movzx.Generated.RR8.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Reset.Second

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA256
open Sha2.Proofs.Common.SHA256.Instances Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.SHA256.Absorb

def offset (v : Wrapper.Variant) : Nat := if v = .sha224 then 0x120a else 0x2e46

def entry (v : Wrapper.Variant) : BitVec 64 := Extracted.textAddress + BitVec.ofNat 64 (offset v)

def displacement (v : Wrapper.Variant) : BitVec 32 := if v = .sha224 then 0xf3 else 0xf7

def emptyPC (v : Wrapper.Variant) : BitVec 64 := Normalize.entry false v + 16#64

def tailBytes (v : Wrapper.Variant) : List UInt8 :=
  [0x45, 0x31, 0xff, 0x48, 0x8d, 0x1d] ++
    (if v = .sha224 then [0x43, 0xcb, 0, 0] else [7, 0xaf, 0, 0]) ++
    [0xeb, if v = .sha224 then 0x1e else 0x22]

def tailEffect (v : Wrapper.Variant) (_ : RamState) : Effect :=
  { rip := (resetSecond v).head
    writes := [⟨(.reg 15 : Operand 64), 0⟩, ⟨(.reg 3 : Operand 64), 0x10dd60⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

def emptyBytes : List UInt8 := [0x45,0x31,0xf6,0x31,0xc0,0x44,0x0f,0xb6,0xf8]

def emptyEffect (p : BitVec 64) (_ : RamState) : Effect :=
  { rip := p + 9#64
    writes := [⟨(.reg 14 : Operand 64), 0⟩, ⟨(.reg 0 : Operand 64), 0⟩,
      ⟨(.reg 15 : Operand 64), 0⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem inside (v : Wrapper.Variant) : BlockInProgram (entry v) 256 :=
  blockInProgram_of_textOffset (offset v) 256 (by cases v <;> decide +kernel)

theorem tail_run [Bindings] (v : Wrapper.Variant) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = entry v + 9#64)
      (codeRange (entry v + 9#64) (tailBytes v)) (Effect.post (tailEffect v)) := by
  have within (n : Nat) (hn : n ≤ 247) : InProgram (entry v + 9#64 + BitVec.ofNat 64 n) := by
    have h := inside v (9+n) (by omega)
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using h
  have target : InProgram (resetSecond v).head := by
    have h := inside v (if v = .sha224 then 51 else 55) (by cases v <;> decide)
    cases v <;> exact h
  have low : (branchTarget (entry v + 9#64 + 10#64) 2
      ((if v = .sha224 then 30 else 34 : BitVec 8).signExtend 64)).toNat < 2^32 := by
    cases v <;> decide +kernel
  advance_reloc_begin (StepEffect.forgetFlags (h := xor_r32_r32_rex_effect_step
    (entry v + 9#64) 0x45 0xff (by simp [RexNoWPrefix]) rfl))
    next (by simpa [BitVec.add_assoc] using boundary_ne_program outside (within 3 (by decide)))
  advance_reloc_then (lea_r64_effect_step (entry v + 9#64 + 3#64) 0x48
    (by simp [RexWPrefix]) 3 (.rip (if v = .sha224 then 0xcb43 else 0xaf07))
    (by cases v <;> decide) rfl rfl)
    next (by simpa [BitVec.add_assoc] using boundary_ne_program outside (within 10 (by decide)))
  advance_reloc_then (jmp_rel8_effect_step (entry v + 9#64 + 10#64)
    (if v = .sha224 then 30 else 34) low)
    next (by
      have eq : entry v + (21#64 + (if v = .sha224 then 30#8 else 34#8).signExtend 64) =
          (resetSecond v).head := by cases v <;> decide +kernel
      rw [eq]
      exact boundary_ne_program outside target)
  apply AdvanceTriple.block_end
  intro s t _ h
  apply h.weaken
  · cases v <;> x86_norm [tailEffect, entry, offset, resetSecond]
  · x86_norm [tailEffect]
    constructor
    · change 0#64 = ((Operand.read s (.reg 15 : Operand 32)) ^^^
        (Operand.read s (.reg 15 : Operand 32))).setWidth 64
      simp
    · cases v <;> decide +kernel
  · intro i; cases i <;> x86_norm [tailEffect]
  · x86_norm [tailEffect]
  all_goals cases v <;> x86_sub

theorem empty_run [Bindings] (p : BitVec 64) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p 9) :
    AdvanceTriple boundary (fun s => s.RIP = p) (codeRange p emptyBytes)
      (Effect.post (emptyEffect p)) := by
  exact Normalize.empty_run p .reset boundary outside inside

theorem tail_code (v : Wrapper.Variant) {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (entry v + 9#64) (tailBytes v)) s := by
  have h := programText_slice (programLoaded_codeIn loaded) (offset v + 9) (tailBytes v)
    (by cases v <;> decide +kernel) (by cases v <;> decide +kernel)
  simpa [entry, BitVec.ofNat_add, BitVec.add_assoc] using h

theorem empty_code (v : Wrapper.Variant) {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (emptyPC v) emptyBytes) s := by
  have h := programText_slice (programLoaded_codeIn loaded)
    (Normalize.entryOffset false v + 16) emptyBytes
    (by cases v <;> decide +kernel) (by cases v <;> decide +kernel)
  simpa [emptyPC, Normalize.entry, BitVec.ofNat_add, BitVec.add_assoc] using h

theorem empty_inside (v : Wrapper.Variant) : BlockInProgram (emptyPC v) 9 := by
  have h := blockInProgram_of_textOffset (Normalize.entryOffset false v + 16) 9
    (by cases v <;> decide +kernel)
  simpa [emptyPC, Normalize.entry, BitVec.ofNat_add, BitVec.add_assoc] using h

private theorem avoid_regions {initial : RamState} {inputs : Array Input} {v : Wrapper.Variant}
    (call : TwoOutputs.ValidCall (resetRoutine v) initial inputs) :
    ∀ region ∈ regions (resetRoutine v) initial, region.Avoids InProgram := by
  intro region member a ha hp
  have mem : region ∈ [TwoOutputs.outputRegion (resetRoutine v) initial,
      TwoOutputs.secondOutputRegion (resetRoutine v) initial,
      Stack.region initial (resetRoutine v).minStackBytes] := by
    simpa only [regions, Vector.mem_mk, List.mem_toArray] using member
  exact (call.separation.2 region mem).2 a ha (.inl hp)

theorem tail_ready [bindings : Bindings] (v : Wrapper.Variant)
    {initial b : RamState} {inputs : Array Input}
    (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall (resetRoutine v) initial inputs)
    (state : ExecutionState initial b (regions (resetRoutine v) initial))
    (rsp : rspOf b = stackPtr initial - 248#64)
    (rip : b.RIP = entry v + 9#64)
    (hasher : HasherAt b (rspOf b) ByteArray.empty v.initialHash)
    (count : b.regValue .r12 = BitVec.ofNat 64 inputs.size)
    (positive : 0 < inputs.size)
    (pointer : memLoad b.external (rspOf b + 168#64) 64 = initial.regValue .rdi)
    (length : memLoad b.external (rspOf b + 176#64) 64 = initial.regValue .rdx) :
    ∃ t, ExecutionState initial t (regions (resetRoutine v) initial) ∧
      Table.LoopState (resetSecond v) ((resetSecond v).chunk.sp initial) inputs 0 t ∧
      Table.InputData (resetSecond v) ((resetSecond v).chunk.sp initial) inputs t ∧
      Table.Separation (resetSecond v) initial t 720 inputs ∧
      (tailEffect v b).Holds b t ∧ t.external = b.external := by
  obtain ⟨fuel, t, run, ready, _, result⟩ := tail_run v (returnBoundary initial)
    (valid_return_boundary machine call.stack call.returnAddress).2.2 b
    (supportedMachine_readyToStep state.machine) (tail_code v state.loaded) rip
  have nomem : ∀ c ∈ (tailEffect v b).components, ∀ a, ¬ c.Covers a := by
    simp [tailEffect, Effect.components, Component.Covers]
  have stateT := state.of_agrees (avoid_regions call) run ready result.agrees
    (fun c hc a ha => (nomem c hc a ha).elim) (by simp [tailEffect, Effect.components])
  have memory := result.agrees.external nomem
  have rspT : rspOf t = rspOf b := result.agrees.read (n := 64) (r := 4)
    (by simp [tailEffect, Effect.components])
  have sp : (resetSecond v).chunk.sp initial = rspOf b := by
    rw [rsp]; cases v <;> rfl
  have ptr : memLoad t.external ((resetSecond v).chunk.sp initial +
      BitVec.ofNat 64 (resetSecond v).pointerSlot) 64 = initial.regValue .rdi := by
    rw [memory, sp]; exact pointer
  have len : memLoad t.external ((resetSecond v).chunk.sp initial +
      BitVec.ofNat 64 (resetSecond v).lengthSlot) 64 = initial.regValue .rdx := by
    rw [memory, sp]; exact length
  have writes : t.regValue .r15 = 0#64 ∧ t.regValue .rbx = 0x10dd60#64 := result.writes
  refine ⟨t, stateT, ?_, table_inputData call stateT.frame _ _ ptr len, ?_, result, memory⟩
  · refine ⟨result.rip, ?_, ?_, writes.1, ?_, positive, ?_, ?_, ?_, ?_⟩
    · rw [sp]; exact rspT
    · rw [Wrapper.prefixMessage_zero]
      have preserved := hasher.of_bytes (fun i _ => by rw [memory])
      simpa only [Table.Layout.stored, sp, show (resetSecond v).storedOffset = 0 from rfl,
        BitVec.add_zero, show (resetSecond v).chunk.initialHash = v.initialHash from rfl] using preserved
    · exact (result.agrees.read (n := 64) (r := 12)
        (by simp [tailEffect, Effect.components])).trans count
    · intro _ r hr; change r ∈ (none : Option (BitVec 4)) at hr; cases hr
    · intro r hr; change r ∈ (none : Option (BitVec 4)) at hr; cases hr
    · intro ne; exact (ne rfl).elim
    · intro call hc r he
      change call ∈ [(Absorption.Loop.resetLast.chunk v).smallCall,
        (Absorption.Loop.resetLast.chunk v).fillCall,
        (Absorption.Loop.resetLast.chunk v).tailCall] at hc
      cases v <;> simp only [Absorption.Loop.chunk, List.mem_cons, List.not_mem_nil, or_false] at hc
      all_goals rcases hc with rfl | rfl | rfl
      all_goals cases he
      all_goals exact writes.2
  · simpa only [resetRoutine_stack] using table_separation call (resetSecond v) ptr len

theorem empty_ready [bindings : Bindings] (v : Wrapper.Variant)
    {initial b : RamState} {inputs : Array Input}
    (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall (resetRoutine v) initial inputs)
    (state : ExecutionState initial b (regions (resetRoutine v) initial))
    (rsp : rspOf b = stackPtr initial - 248#64)
    (rip : b.RIP = emptyPC v)
    (hasher : HasherAt b (rspOf b) ByteArray.empty v.initialHash) :
    ∃ t, ExecutionState initial t (regions (resetRoutine v) initial) ∧
      Finalize.Prepared (Finalization.resetLast.layout v)
        ((Finalization.resetLast.layout v).sp initial) ByteArray.empty t ∧
      (emptyEffect (emptyPC v) b).Holds b t ∧ t.external = b.external := by
  obtain ⟨fuel, t, run, ready, _, result⟩ := empty_run (emptyPC v) (returnBoundary initial)
    (valid_return_boundary machine call.stack call.returnAddress).2.2 (empty_inside v) b
    (supportedMachine_readyToStep state.machine) (empty_code v state.loaded) rip
  have nomem : ∀ c ∈ (emptyEffect (emptyPC v) b).components, ∀ a, ¬ c.Covers a := by
    simp [emptyEffect, Effect.components, Component.Covers]
  have stateT := state.of_agrees (avoid_regions call) run ready result.agrees
    (fun c hc a ha => (nomem c hc a ha).elim) (by simp [emptyEffect, Effect.components])
  have memory := result.agrees.external nomem
  have rspT : rspOf t = rspOf b := result.agrees.read (n := 64) (r := 4)
    (by simp [emptyEffect, Effect.components])
  have sp : (Finalization.resetLast.layout v).sp initial = rspOf b := by
    rw [rsp]; cases v <;> rfl
  have writes : t.regValue .r14 = 0#64 ∧ t.regValue .rax = 0#64 ∧
      t.regValue .r15 = 0#64 := result.writes
  refine ⟨t, stateT, ?_, result, memory⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [result.rip]
    change emptyPC v + 9#64 = _
    cases v <;> decide +kernel
  · rw [sp]; exact rspT
  · have preserved := hasher.of_bytes (fun i _ => by rw [memory])
    change HasherAt t ((Finalization.resetLast.layout v).sp initial + 0#64) ByteArray.empty v.initialHash
    rw [BitVec.add_zero, sp]
    exact preserved
  · exact writes.2.2
  · exact writes.1
  · intro impossible; cases impossible

theorem after_first_pc (v : Wrapper.Variant) :
    resetStorePC v false + BitVec.ofNat 64 (Serialize.bytes (.store .r13 (v == .sha224))).length =
      entry v := by
  cases v <;> decide +kernel

theorem first_registers {v : Wrapper.Variant} {s a b t : RamState}
    (load : (Serialize.effect (resetLoadPC v false) (.loadSwap .at64 (v == .sha224)) s).Holds s a)
    (init : Initialize.Post (Initialization.resetOutput.layout v) (rspOf a) a b)
    (store : (Serialize.effect (resetStorePC v false) (.store .r13 (v == .sha224)) b).Holds b t)
    (r : BitVec 5) (member : r ∈ [3#5, 4#5, 5#5, 12#5, 13#5]) :
    (.reg r : Operand 64).read t = (.reg r : Operand 64).read s := by
  have h₁ : (.reg r : Operand 64).read a = (.reg r : Operand 64).read s := by
    apply load.agrees.read
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    all_goals cases v <;> simp [Serialize.effect, Effect.components]
  have h₂ : (.reg r : Operand 64).read b = (.reg r : Operand 64).read a := by
    apply init.frame.read
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    all_goals cases v <;> simp [Initialize.Layout.components, Initialization.layout,
      Initialization.word, Initialization.temporary]
  have h₃ : (.reg r : Operand 64).read t = (.reg r : Operand 64).read b := by
    apply store.agrees.read
    cases v <;> simp [Serialize.effect, Effect.components]
  exact h₃.trans (h₂.trans h₁)

theorem branch_code (v : Wrapper.Variant) {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (entry v) (Dispatch.branchBytes (displacement := displacement v))) s :=
  programText_slice (programLoaded_codeIn loaded) (offset v)
    (Dispatch.branchBytes (displacement := displacement v))
    (by cases v <;> decide +kernel) (by cases v <;> decide +kernel)

theorem dispatched [bindings : Bindings] (v : Wrapper.Variant)
    {initial s : RamState} {inputs : Array Input} {first : ByteArray}
    (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall (resetRoutine v) initial inputs)
    (state : ExecutionState initial s (regions (resetRoutine v) initial))
    (rsp : rspOf s = stackPtr initial - 248#64)
    (rip : s.RIP = entry v)
    (hasher : HasherAt s (rspOf s) ByteArray.empty v.initialHash)
    (count : s.regValue .r12 = BitVec.ofNat 64 inputs.size)
    (pointer : memLoad s.external (rspOf s + 168#64) 64 = initial.regValue .rdi)
    (length : memLoad s.external (rspOf s + 176#64) 64 = initial.regValue .rdx)
    (firstBytes : (TwoOutputs.outputRegion (resetRoutine v) initial).HasBytes s.external first) :
    ∃ t, ExecutionState initial t (regions (resetRoutine v) initial) ∧
      (TwoOutputs.outputRegion (resetRoutine v) initial).HasBytes t.external first ∧
      t.external = s.external ∧
      ((Table.LoopState (resetSecond v) ((resetSecond v).chunk.sp initial) inputs 0 t ∧
        Table.InputData (resetSecond v) ((resetSecond v).chunk.sp initial) inputs t ∧
        Table.Separation (resetSecond v) initial t 720 inputs) ∨
       (inputs.size = 0 ∧ Finalize.Prepared (Finalization.resetLast.layout v)
         ((Finalization.resetLast.layout v).sp initial) ByteArray.empty t)) := by
  have jump : entry v + 9#64 + (displacement v).signExtend 64 = emptyPC v := by
    cases v <;> decide +kernel
  have target : InProgram (entry v + 9#64 + (displacement v).signExtend 64) := by
    rw [jump]
    have h := empty_inside v 0 (by decide)
    simpa only [BitVec.add_zero] using h
  obtain ⟨fuel, b, run, ready, _, branch⟩ := Dispatch.branch (displacement := displacement v)
    (entry v) (returnBoundary initial) (valid_return_boundary machine call.stack call.returnAddress).2.2
    (fun i hi => inside v i (by omega)) target s (supportedMachine_readyToStep state.machine)
    (branch_code v state.loaded) rip
  have frameB : AgreesExcept [.flags, .rip] s b := branch.agrees
  have nomem : ∀ c ∈ ([.flags, .rip] : List Component), ∀ a, ¬ c.Covers a := by
    simp [Component.Covers]
  have stateB := state.of_agrees (avoid_regions call) run ready frameB
    (fun c hc a ha => (nomem c hc a ha).elim) (by simp)
  have memB := frameB.external nomem
  have rspB : rspOf b = rspOf s := frameB.read (n := 64) (r := 4) (by simp)
  have hashB : HasherAt b (rspOf b) ByteArray.empty v.initialHash := by
    rw [rspB]
    exact hasher.of_bytes (fun _ _ => by rw [memB])
  by_cases empty : inputs.size = 0
  · have ripB : b.RIP = emptyPC v := by
      have h : b.RIP = if s.regValue .r12 = 0#64 then
          entry v + 9#64 + (displacement v).signExtend 64 else entry v + 9#64 := branch.rip
      simpa [count, empty, jump] using h
    obtain ⟨t, stateT, prepared, _, memory⟩ := empty_ready v machine call stateB
      (rspB.trans rsp) ripB hashB
    have memT := memory.trans memB
    exact ⟨t, stateT, by rw [memT]; exact firstBytes, memT, Or.inr ⟨empty, prepared⟩⟩
  · have bound := Wrapper.validCall_count_bound (firstOutput_validCall call)
    have nonzero : s.regValue .r12 ≠ 0#64 := by
      rw [count]
      intro eq
      have eqNat := congrArg BitVec.toNat eq
      simp only [BitVec.toNat_ofNat] at eqNat
      rw [Nat.mod_eq_of_lt (by omega)] at eqNat
      exact empty eqNat
    have ripB : b.RIP = entry v + 9#64 := by
      have h : b.RIP = if s.regValue .r12 = 0#64 then
          entry v + 9#64 + (displacement v).signExtend 64 else entry v + 9#64 := branch.rip
      simp only [nonzero, ite_false] at h
      exact h
    obtain ⟨t, stateT, loop, data, apart, _, memory⟩ := tail_ready v machine call stateB
      (rspB.trans rsp) ripB hashB
      ((frameB.read (n := 64) (r := 12) (by simp)).trans count) (by omega)
      (by rw [memB, rspB]; exact pointer) (by rw [memB, rspB]; exact length)
    have memT := memory.trans memB
    exact ⟨t, stateT, by rw [memT]; exact firstBytes, memT, Or.inl ⟨loop, data, apart⟩⟩

end Sha2.Proofs.Reset.Second
