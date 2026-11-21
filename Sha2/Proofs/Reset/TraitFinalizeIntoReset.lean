import Sha2.Proofs.Reset.Dispatch
import Sha2.Proofs.Reset.Serialize
import Sha2.Proofs.Reset.NormalizeState
import Sha2.Proofs.Reset.TraitPrefix
import Sha2.Proofs.Reset.FinalizeIntoReset
import Sha2.Proofs.Reset.Return
import Sha2.Proofs.Reset.Last
import Sha2.Proofs.Common.SHA256.Finalize.Proof.Geometry
import Sha2.Proofs.Common.SHA256.Absorb.Traversal
import Sha2.Proofs.Common.SHA256.Absorb.Correctness
import Sha2.Proofs.Common.SHA256.Instances.Absorb.TraitTable.Contracts
import Sha2.Proofs.Common.SHA256.Instances.Absorb.Stages
import Sha2.Proofs.Reset.Entry
import Sha2.Proofs.Reset.Inputs
import Sha2.Proofs.Common.Machine.FrameMemory
import Sha2.Proofs.Common.SHA256.Instances.Absorb.TableLayouts
import Sha2.Proofs.Common.SHA256.Blocks.Absorb

set_option autoImplicit false

namespace Sha2.Proofs.Reset.TraitFinalizeIntoReset

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine

def branchBytes (slot : BitVec 8 := 104) (disp : BitVec 32 := 0x11f) : List UInt8 :=
  encodeCmpM64Imm8 (.sib 4 none 0 (.d8 slot)) 0 ++ [0x0f,0x84] ++ immBytes 32 disp

def branchEffect (p : BitVec 64) (s : RamState) (slot : BitVec 8 := 104) (disp : BitVec 32 := 0x11f) : Effect :=
  { rip := if memLoad s.external (rspOf s + slot.signExtend 64) 64 = 0 then p + (12#64 + disp.signExtend 64) else p + 12#64
    flags := some ⟨none, none, none, none, none, none⟩ }

set_option maxHeartbeats 800000 in
theorem branch [Bindings] (slot : BitVec 8) (disp : BitVec 32) (p : BitVec 64) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p 12)
    (target : InProgram (p + (12#64 + disp.signExtend 64))) :
    AdvanceTriple boundary (fun s => s.RIP = p ∧ MemReadable s (rspOf s + slot.signExtend 64) 8) (codeRange p (branchBytes slot disp))
      (Effect.post (fun s => branchEffect p s slot disp)) := by
  intro s ready loaded rip
  have test := Common.SHA256.Absorb.Blocks.compareZeroStack_step p (.d8 slot) 0 (by simp [AddrMode.Valid])
  obtain ⟨u, run, readyU, tested⟩ := test.advances ready
    (loaded.mono (codeRange_mem_of_take (by simp [branchBytes]))) ⟨rip.1, rip.2⟩
    (boundary_ne_program outside (inside 6 (by decide)))
  have frame : AgreesExcept [.flags, .rip] s u := tested.agrees
  have codeU := frame.codeIn (by simp [Component.Covers]) loaded
  have testedRip : u.RIP = p + (6 : BitVec 64) := tested.rip
  have low : (branchTarget (p + 6#64) 6 (disp.signExtend 64)).toNat < 2^32 := by
    obtain ⟨byte, mem⟩ := target
    have bound := programSections_low.codeLow (_, byte) mem
    simpa [branchTarget, BitVec.add_assoc, Prelude.userAddressLimit] using bound
  obtain ⟨t, step, readyT, jumped⟩ := jcc_rel32_effect_step (p + 6#64) 4 disp u readyU
    (codeU.mono (codeRange_mem_of_drop 6 (by simp [branchBytes, encodeCmpM64Imm8, AddrMode.tail, Disp.bytes, immBytes, jccOpcode32, List.take_of_length_le]))) ⟨testedRip, fun _ => low⟩
  have zero : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = (memLoad s.external (rspOf s + slot.signExtend 64) 64 == 0) := by
    have zero := tested.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
      (memLoad s.external (rspOf s + slot.signExtend 64) 64 - 0 == 0) at zero
    exact zero.trans (by congr 1; exact BitVec.sub_zero _)
  have ripT : t.RIP = (branchEffect p s slot disp).rip := by
    rw [jumped.rip]
    simp only [jccEffect, X86Proofs.branchEffect, branchTarget, condHolds]
    change (if (StatusFlags.ofRFLAGS u.RFLAGS).ZF then p + 6#64 + 6#64 +
      disp.signExtend 64 else p + 6#64 + 6#64) = _
    rw [zero]
    simp [branchEffect, BitVec.add_assoc]
  have frameT : AgreesExcept [.flags, .rip] s t :=
    (frame.trans jumped.agrees).mono (by simp [jccEffect, X86Proofs.branchEffect, Effect.components])
  have advance : Advances boundary 1 u t := by
    apply Advances.of_step step
    left
    rw [ripT]
    simp only [branchEffect]
    split
    · exact boundary_ne_program outside target
    · exact boundary_ne_program outside (inside 12 (by decide))
  refine ⟨2, t, run.trans advance, readyT, ?_, ?_⟩
  · exact frameT.codeIn (by simp [Component.Covers]) loaded
  · refine ⟨ripT, ?_, ?_, ?_⟩
    · exact trivial
    · exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
    · exact frameT


def tailBytes : List UInt8 :=
  [0x45,0x31,0xff,0x48,0x89,0xe5,0x48,0x8d,0x54,0x24,0x70,0xeb,0x40]

def tailEffect (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p + 77#64
    writes := [⟨(.reg 15 : Operand 64), 0⟩,
      ⟨(.reg 5 : Operand 64), rspOf s⟩,
      ⟨(.reg 2 : Operand 64), rspOf s + 112#64⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

theorem tail [Bindings] (p : BitVec 64) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p 13)
    (target : InProgram (p + 77#64)) :
    AdvanceTriple boundary (fun s => s.RIP = p) (codeRange p tailBytes)
      (Effect.post (tailEffect p)) := by
  have low : (branchTarget (p + 11#64) 2 ((64 : BitVec 8).signExtend 64)).toNat < 2^32 := by
    obtain ⟨byte, mem⟩ := target
    have bound := programSections_low.codeLow (_, byte) mem
    simpa [branchTarget, BitVec.add_assoc, Prelude.userAddressLimit] using bound
  advance_reloc_begin (StepEffect.forgetFlags (h := xor_r32_r32_rex_effect_step p
    0x45 0xff (by simp [RexNoWPrefix]) rfl))
    next (boundary_ne_program outside (inside 3 (by decide)))
  advance_reloc_then (mov_r64_r64_effect_step (p + 3#64) 0x48 0xe5
    (by simp [RexWPrefix]) rfl)
    next (boundary_ne_program outside (inside 6 (by decide)))
  advance_reloc_then (lea_r64_effect_step (p + 6#64) 0x48 (by simp [RexWPrefix]) 2
    (.sib 4 none 0 (.d8 112)) (by decide) rfl rfl)
    next (boundary_ne_program outside (inside 11 (by decide)))
  advance_reloc_then (jmp_rel8_effect_step (p + 11#64) 64 low)
    next (boundary_ne_program outside target)
  apply AdvanceTriple.block_end
  intro s t _ h
  apply h.weaken
  · x86_norm [tailEffect]
  · x86_norm [tailEffect]
    simp [gprNumber, rexB, rexR, modrmRm, modrmReg]
  · intro i; cases i <;> x86_norm [tailEffect]
  · x86_norm [tailEffect]

def secondPC (v : Wrapper.Variant) : BitVec 64 :=
  if v = .sha224 then 0x1018d3 else 0x103533

theorem branch_code (v : Wrapper.Variant) {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (secondPC v) branchBytes) s := by
  cases v with
  | sha224 =>
    exact programText_slice (programLoaded_codeIn loaded) 0x18d3 branchBytes
      (by decide +kernel) (by decide +kernel)
  | sha256 =>
    exact programText_slice (programLoaded_codeIn loaded) 0x3533 branchBytes
      (by decide +kernel) (by decide +kernel)

theorem tail_code (v : Wrapper.Variant) {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (secondPC v + 12#64) tailBytes) s := by
  cases v with
  | sha224 =>
    exact programText_slice (programLoaded_codeIn loaded) 0x18df tailBytes
      (by decide +kernel) (by decide +kernel)
  | sha256 =>
    exact programText_slice (programLoaded_codeIn loaded) 0x353f tailBytes
      (by decide +kernel) (by decide +kernel)

theorem second_inside (v : Wrapper.Variant) : BlockInProgram (secondPC v) 299 := by
  cases v with
  | sha224 => exact blockInProgram_of_textOffset 0x18d3 299 (by decide +kernel)
  | sha256 => exact blockInProgram_of_textOffset 0x3533 299 (by decide +kernel)

open Sha2.Proofs.Program Prelude Sha2.Proofs.Common.SHA256 Sha2.Proofs.Common.SHA256.Absorb
open Sha2.Proofs.Common.SHA256.Instances.Absorption

theorem second_dispatched [bindings : Bindings] (v : Wrapper.Variant)
    {routine : Routine} {initial s : RamState} {inputs : Array Input}
    (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall routine initial inputs)
    (capacity : 360 ≤ routine.minStackBytes)
    (state : ExecutionState initial s (regions routine initial))
    (rsp : rspOf s = stackPtr initial - 360#64) (rip : s.RIP = secondPC v)
    (hasher : HasherAt s (rspOf s + 112#64) ByteArray.empty v.initialHash)
    (count : memLoad s.external (rspOf s + 104#64) 64 = BitVec.ofNat 64 inputs.size)
    (pointer : memLoad s.external (rspOf s + 216#64) 64 = initial.regValue .rdi)
    (length : memLoad s.external (rspOf s + 224#64) 64 = initial.regValue .rdx) :
    ∃ t, ExecutionState initial t (regions routine initial) ∧
      t.external = s.external ∧ rspOf t = rspOf s ∧
      ((inputs.size = 0 ∧ t.RIP = (traitLastTable v).exit ∧
        HasherAt t (rspOf t + 112#64) ByteArray.empty v.initialHash) ∨
       (Table.LoopState (traitLastTable v) ((traitLastTable v).chunk.sp initial) inputs 0 t ∧
        Table.InputData (traitLastTable v) ((traitLastTable v).chunk.sp initial) inputs t ∧
        Table.Separation (traitLastTable v) initial t routine.minStackBytes inputs)) := by
  have outside := (valid_return_boundary machine call.stack call.returnAddress).2.2
  have avoid : ∀ region ∈ regions routine initial, region.Avoids InProgram := by
    intro region member a ha hp
    exact (call.separation.2 region (by simpa [regions] using member)).2 a ha (.inl hp)
  have readable : MemReadable s (rspOf s + 104#64) 8 := by
    rw [rsp]
    exact stack_frame_readable call.stack capacity state.allocated (by decide)
  obtain ⟨_, b, run, ready, _, effect⟩ := branch 104 0x11f (secondPC v) (returnBoundary initial)
    outside (fun i hi => second_inside v i (by omega)) (second_inside v 299 (by decide))
    s (supportedMachine_readyToStep state.machine) (branch_code v state.loaded) ⟨rip, readable⟩
  have nomem : ∀ c ∈ (branchEffect (secondPC v) s).components, ∀ a, ¬ c.Covers a := by
    simp [branchEffect, Effect.components, Component.Covers]
  have stateB := state.of_agrees avoid run ready effect.agrees
    (fun c hc a ha => (nomem c hc a ha).elim) (by simp [branchEffect, Effect.components])
  have memB := effect.agrees.external nomem
  have rspB : rspOf b = rspOf s := effect.agrees.read (n := 64) (r := 4)
    (by simp [branchEffect, Effect.components])
  have hashB : HasherAt b (rspOf b + 112#64) ByteArray.empty v.initialHash := by
    rw [rspB]
    exact hasher.of_bytes (fun _ _ => by rw [memB])
  by_cases empty : inputs.size = 0
  · refine ⟨b, stateB, memB, rspB, Or.inl ⟨empty, ?_, hashB⟩⟩
    have pc : secondPC v + 299#64 = (traitLastTable v).exit := by cases v <;> decide +kernel
    have h := effect.rip
    change b.RIP = if memLoad s.external (rspOf s + 104#64) 64 = 0#64 then
      secondPC v + 299#64 else secondPC v + 12#64 at h
    rw [count, empty] at h
    simpa only [BitVec.ofNat_eq_ofNat, ite_true, pc] using h
  · have bound := Wrapper.validCall_count_bound (firstOutput_validCall call)
    have nonzero : memLoad s.external (rspOf s + 104#64) 64 ≠ 0 := by
      rw [count]
      intro eq
      have h := congrArg BitVec.toNat eq
      simp only [BitVec.toNat_ofNat] at h
      rw [Nat.mod_eq_of_lt (by omega)] at h
      exact empty h
    have ripB : b.RIP = secondPC v + 12#64 := by
      simpa only [branchEffect, show (104 : BitVec 8).signExtend 64 = 104#64 from by decide, nonzero, ite_false] using effect.rip
    have inside : BlockInProgram (secondPC v + 12#64) 13 := by
      intro i hi
      have h := second_inside v (12 + i) (by omega)
      simpa only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using h
    have target : InProgram (secondPC v + 12#64 + 77#64) := by
      have h := second_inside v 89 (by decide)
      simpa [BitVec.add_assoc] using h
    obtain ⟨_, t, runT, readyT, _, tailResult⟩ := tail (secondPC v + 12#64) (returnBoundary initial)
      outside inside target b ready (tail_code v stateB.loaded) ripB
    have nomemT : ∀ c ∈ (tailEffect (secondPC v + 12#64) b).components, ∀ a, ¬ c.Covers a := by
      simp [tailEffect, Effect.components, Component.Covers]
    have stateT := stateB.of_agrees avoid runT readyT tailResult.agrees
      (fun c hc a ha => (nomemT c hc a ha).elim) (by simp [tailEffect, Effect.components])
    have memory := (tailResult.agrees.external nomemT).trans memB
    have rspT : rspOf t = rspOf s :=
      (tailResult.agrees.read (n := 64) (r := 4) (by simp [tailEffect, Effect.components])).trans rspB
    have sp : (traitLastTable v).chunk.sp initial = rspOf s := by
      rw [rsp]; cases v <;> rfl
    have ptr : memLoad t.external ((traitLastTable v).chunk.sp initial + 216#64) 64 = initial.regValue .rdi := by
      rw [memory, sp]; exact pointer
    have len : memLoad t.external ((traitLastTable v).chunk.sp initial + 224#64) 64 = initial.regValue .rdx := by
      rw [memory, sp]; exact length
    refine ⟨t, stateT, memory, rspT, Or.inr ⟨?_,
      table_inputData call stateT.frame _ _ ptr len,
      table_separation call _ ptr len⟩⟩
    have writes : t.regValue .r15 = 0 ∧ t.regValue .rbp = rspOf b ∧
        t.regValue .rdx = rspOf b + 112#64 := tailResult.writes
    refine ⟨?_, ?_, ?_, writes.1, ?_, by omega, ?_, ?_, ?_, ?_⟩
    · have pc : secondPC v + 12#64 + 77#64 = (traitLastTable v).head := by cases v <;> decide +kernel
      exact tailResult.rip.trans pc
    · rw [sp]; exact rspT
    · rw [Wrapper.prefixMessage_zero]
      change HasherAt t ((traitLastTable v).chunk.sp initial + 112#64) ByteArray.empty v.initialHash
      rw [sp]
      exact hasher.of_bytes (fun _ _ => by rw [memory])
    · change memLoad t.external ((traitLastTable v).chunk.sp initial + 104#64) 64 = _
      rw [memory, sp]; exact count
    · intro impossible; cases impossible
    · intro r hr
      change r ∈ (some (5 : BitVec 4)) at hr
      have eq : r = 5 := (Option.mem_some_iff.mp hr).symm
      subst r
      change t.regValue .rbp = (traitLastTable v).chunk.sp initial + 0#64
      rw [BitVec.add_zero, sp]
      exact writes.2.1.trans rspB
    · intro _
      change t.regValue .rdx = (traitLastTable v).chunk.sp initial + 112#64
      rw [sp, ← rspB]; exact writes.2.2
    · intro c hc r he
      change c ∈ [(Loop.traitLast.chunk v).smallCall,
        (Loop.traitLast.chunk v).fillCall, (Loop.traitLast.chunk v).tailCall] at hc
      cases v <;> simp only [Loop.chunk, List.mem_cons, List.not_mem_nil, or_false] at hc
      all_goals rcases hc with rfl | rfl | rfl
      all_goals cases he

theorem first_tableCode (v : Wrapper.Variant) : Table.CodeFacts (traitFirst v) := by
  apply table_codeFacts .traitFirst (traitFirst v) v
  · intro site member
    cases v <;> simp [traitFirst, Loop.sites] at member ⊢
    all_goals grind
  · constructor
    · cases v with
      | sha224 => exact inProgram_of_textOffset 0x15bc (by decide +kernel)
      | sha256 => exact inProgram_of_textOffset 0x320c (by decide +kernel)
    · cases v with
      | sha224 => exact inProgram_of_textOffset 0x168f (by decide +kernel)
      | sha256 => exact inProgram_of_textOffset 0x32df (by decide +kernel)

def table (first : Bool) (v : Wrapper.Variant) : Table.Layout :=
  if first then traitFirst v else traitLastTable v

theorem traversed [bindings : Bindings] (first : Bool) (v : Wrapper.Variant)
    {routine : Routine} {initial s : RamState} {inputs : Array Input}
    (stride : UnitStringStride bindings) (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall routine initial inputs) (stackSize : routine.minStackBytes = 832)
    (state : ExecutionState initial s (regions routine initial))
    (loop : Table.LoopState (table first v) ((table first v).chunk.sp initial) inputs 0 s)
    (data : Table.InputData (table first v) ((table first v).chunk.sp initial) inputs s)
    (separation : Table.Separation (table first v) initial s 832 inputs) :
    ∃ t, Table.Finished (table first v) initial s t (regions routine initial) inputs := by
  have stack : Stack.Valid initial 832 := by simpa only [stackSize] using call.stack
  have avoid : (Stack.region initial 832).Avoids (fun a => InProgram a ∨ InPageTables a) := by
    rw [← stackSize]
    exact (call.separation.2 _ (by simp)).2
  have outside := (valid_return_boundary machine call.stack call.returnAddress).2.2
  have wf : Table.WellFormed (table first v) 832 := by
    cases first
    · exact traitLastTable_wellFormed v
    · exact traitFirst_wellFormed v
  have chunk : (table first v).chunk = (if first then Loop.traitFirst else Loop.traitLast).chunk v := by
    cases first
    · rfl
    · exact (traitFirst_chunk v).symm
  have targets : CallTargets (table first v).chunk := by
    cases first
    · exact traitLastTable_callTargets v
    · exact traitFirst_callTargets v
  have code : Table.CodeFacts (table first v) := by
    cases first
    · exact traitLastTable_codeFacts v
    · exact first_tableCode v
  have blocks : Table.BlockContracts (table first v) (returnBoundary initial) := by
    cases first
    · exact traitLastTable_tableBlocks v _ stride outside
    · exact traitFirst_tableBlocks v _ stride outside
  have count : Table.CountAt (table first v) ((table first v).chunk.sp initial) s := by
    constructor
    intro offset eq
    have same : offset = 104 := by cases first <;> cases eq <;> rfl
    subst offset
    have frame : (table first v).chunk.frameBytes = 360 := by cases first <;> cases v <;> rfl
    rw [← loop.rsp]
    change MemReadable s (rspOf s + 104#64) 8
    have rsp : rspOf s = stackPtr initial - 360#64 := by
      change stackPtr s = _
      simpa only [Layout.sp, frame] using loop.rsp
    rw [rsp]
    exact stack_frame_readable stack (by decide) state.allocated (by decide)
  have within : ∀ region ∈ Table.footprint (table first v) ((table first v).chunk.sp initial),
      ∀ a, region.Contains a → ∃ outer ∈ regions routine initial, outer.Contains a := by
    intro region member a inside
    refine ⟨Stack.region initial 832, by simp [regions, stackSize], ?_⟩
    exact Table.footprint_subset_stack wf stack region member a inside
  exact Table.correct (table first v) wf
    (chunk ▸ Loop.flow _ v) (chunk ▸ Loop.codeFacts _ v) targets
    (chunk ▸ Loop.blockContracts _ v _ stride outside) (Absorb.correct _) code blocks
    stride machine stack avoid call.returnAddress state loop count data separation within

open Sha2.Proofs.Common.SHA256.Instances

def firstLoadPC (v : Wrapper.Variant) : BitVec 64 :=
  (Finalization.traitFirst.layout v).exit

def firstStorePC (v : Wrapper.Variant) : BitVec 64 :=
  if v = .sha224 then 0x101865 else 0x1034c0

theorem first_serialized [bindings : Bindings] (v : Wrapper.Variant)
    {routine : Routine} {initial s : RamState} {inputs : Array Input} {hash : Array UInt32}
    (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall routine initial inputs)
    (capacity : 360 ≤ routine.minStackBytes) (size : routine.outputBytes = v.outputBytes)
    (state : ExecutionState initial s (regions routine initial))
    (rsp : rspOf s = stackPtr initial - 360#64)
    (rip : s.RIP = firstLoadPC v)
    (words : HashStateAt s (rspOf s + 176#64) hash)
    (output : s.regValue .r12 = initial.regValue .rcx) :
    ∃ a t, ExecutionState initial t (regions routine initial) ∧
      (Serialize.effect (firstLoadPC v) (.loadSwap .at176 (v == .sha224)) s).Holds s a ∧
      (Serialize.effect (firstStorePC v) (.store .r12 (v == .sha224)) a).Holds a t ∧
      MemoryWriteFrame s t #v[TwoOutputs.outputRegion routine initial] ∧
      (TwoOutputs.outputRegion routine initial).HasBytes t.external (v.serializeHash hash) ∧
      rspOf t = rspOf s ∧ t.RIP = (Initialization.traitReset.layout v).start := by
  have loadInside : BlockInProgram (firstLoadPC v)
      (Serialize.bytes (.loadSwap .at176 (v == .sha224))).length := by
    cases v with
    | sha224 => exact blockInProgram_of_textOffset 0x1822 _ (by decide +kernel)
    | sha256 => exact blockInProgram_of_textOffset 0x3472 _ (by decide +kernel)
  have loadCode : CodeIn (codeRange (firstLoadPC v)
      (Serialize.bytes (.loadSwap .at176 (v == .sha224)))) s := by
    cases v with
    | sha224 =>
      exact programText_slice (programLoaded_codeIn state.loaded) 0x1822 _
        (by decide +kernel) (by decide +kernel)
    | sha256 =>
      exact programText_slice (programLoaded_codeIn state.loaded) 0x3472 _
        (by decide +kernel) (by decide +kernel)
  obtain ⟨a, stateA, load, swapped⟩ := serialize_load_generic v routine 360 .at176 capacity
    (by decide) (firstLoadPC v) machine call state rsp rip words loadInside loadCode
  have outputA : a.regValue .r12 = initial.regValue .rcx :=
    (load.agrees.read (n := 64) (r := 12)
      (by cases v <;> simp [Serialize.effect, Effect.components])).trans output
  have ripA : a.RIP = firstStorePC v := by
    rw [load.rip]
    change firstLoadPC v + BitVec.ofNat 64 (Serialize.bytes (.loadSwap .at176 (v == .sha224))).length = _
    cases v <;> decide +kernel
  have member : (⟨(initial.regValue .rcx).toNat, v.outputBytes⟩ : MemoryRegion) ∈
      [TwoOutputs.outputRegion routine initial, TwoOutputs.secondOutputRegion routine initial] := by
    simp [TwoOutputs.outputRegion, registerRegion, size]
  have storeInside : BlockInProgram (firstStorePC v)
      (Serialize.bytes (.store .r12 (v == .sha224))).length := by
    cases v with
    | sha224 => exact blockInProgram_of_textOffset 0x1865 _ (by decide +kernel)
    | sha256 => exact blockInProgram_of_textOffset 0x34c0 _ (by decide +kernel)
  have storeCode : CodeIn (codeRange (firstStorePC v)
      (Serialize.bytes (.store .r12 (v == .sha224)))) a := by
    cases v with
    | sha224 =>
      exact programText_slice (programLoaded_codeIn stateA.loaded) 0x1865 _
        (by decide +kernel) (by decide +kernel)
    | sha256 =>
      exact programText_slice (programLoaded_codeIn stateA.loaded) 0x34c0 _
        (by decide +kernel) (by decide +kernel)
  obtain ⟨t, stateT, store, frame, bytes⟩ := serialize_store_generic v routine (firstStorePC v)
    .r12 (initial.regValue .rcx) machine call stateA member outputA swapped ripA storeInside storeCode
  have memA : a.external = s.external := load.agrees.external (by
    cases v <;> simp [Serialize.effect, Effect.components, Component.Covers])
  refine ⟨a, t, stateT, load, store, ?_, ?_, ?_, ?_⟩
  · intro address outside
    rw [frame address]
    · rw [memA]
    · simpa only [TwoOutputs.outputRegion, registerRegion, size] using outside
  · cases v <;> simpa [Wrapper.Variant.serializeHash, serializeHash, TwoOutputs.outputRegion,
      registerRegion, size] using bytes
  · exact (store.agrees.read (n := 64) (r := 4)
      (by cases v <;> simp [Serialize.effect, Effect.components])).trans
      (load.agrees.read (n := 64) (r := 4)
        (by cases v <;> simp [Serialize.effect, Effect.components]))
  · rw [store.rip]
    change firstStorePC v + BitVec.ofNat 64 (Serialize.bytes (.store .r12 (v == .sha224))).length = _
    cases v <;> decide +kernel

theorem table_saved [Bindings] (first : Bool) (v : Wrapper.Variant)
    {initial s t : RamState} {n : Nat} {written : Vector MemoryRegion n}
    (stack : Stack.Valid initial 832) (state : ExecutionState initial s written)
    (frame : MemoryWriteFrame s t (Table.footprint (table first v) ((table first v).chunk.sp initial)))
    (slot : Nat) (low : 216 ≤ slot) (high : slot ≤ 360) :
    memLoad t.external (stackPtr initial - 360#64 + BitVec.ofNat 64 slot) 64 =
      memLoad s.external (stackPtr initial - 360#64 + BitVec.ofNat 64 slot) 64 := by
  have read : MemReadable s (stackPtr initial - 360#64 + BitVec.ofNat 64 slot) 8 := by
    rw [stack_frame_address initial high]
    exact Common.Encoding.Serialize.readable_of_grow
      (stack_valid_sub_readable stack (by omega) (by omega)) state.allocated
  apply Table.memLoad_of_frame frame read
  intro region member a ha hb
  have shape : Table.footprint (table first v) ((table first v).chunk.sp initial) =
      #v[⟨(stackPtr initial - 360#64).toNat,104⟩,
        ⟨(stackPtr initial - 360#64 + 112#64).toNat,104⟩,
        ⟨(stackPtr initial - 360#64 - 344#64).toNat,344⟩] := by
    cases first <;> cases v
    all_goals change (#v[⟨(stackPtr initial - 360#64 + 0#64).toNat,104⟩,
      ⟨(stackPtr initial - 360#64 + 112#64).toNat,104⟩,
      ⟨(stackPtr initial - 360#64 - 344#64).toNat,344⟩] : Vector MemoryRegion 3) = _
    all_goals simp only [BitVec.add_zero]
  rw [shape] at member
  simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at member
  change _ ≤ a ∧ a < _ at ha
  dsimp only at ha
  rw [stack_frame_toNat stack (by decide) high] at ha
  have bounds := stack_valid_bounds stack
  rcases member with rfl | rfl | rfl
  all_goals change _ ≤ a ∧ a < _ at hb
  all_goals dsimp only at hb
  · rw [stack_valid_sub_toNat stack (by decide)] at hb
    omega
  · rw [stack_frame_toNat stack (by decide) (by decide)] at hb
    omega
  · rw [stack_frame_below_toNat stack (by decide : 360 + 344 ≤ 832)] at hb
    omega

theorem finalized_saved [Bindings] (first : Bool) (v : Wrapper.Variant)
    {initial s t : RamState} {n : Nat} {written : Vector MemoryRegion n}
    (stack : Stack.Valid initial 832) (state : ExecutionState initial s written)
    (frame : MemoryWriteFrame s t (Finalize.footprint
      ((if first then Finalization.traitFirst else Finalization.traitLast).layout v)
      (stackPtr initial - 360#64)))
    (slot : Nat) (low : (first = true ∧ slot = 104) ∨ (if first then 216 else 296) ≤ slot) (high : slot ≤ 360) :
    memLoad t.external (stackPtr initial - 360#64 + BitVec.ofNat 64 slot) 64 =
      memLoad s.external (stackPtr initial - 360#64 + BitVec.ofNat 64 slot) 64 := by
  have read : MemReadable s (stackPtr initial - 360#64 + BitVec.ofNat 64 slot) 8 := by
    rw [stack_frame_address initial high]
    exact Common.Encoding.Serialize.readable_of_grow
      (stack_valid_sub_readable stack (by omega) (by omega)) state.allocated
  apply Table.memLoad_of_frame frame read
  intro region member a ha hb
  change _ ≤ a ∧ a < _ at ha
  dsimp only at ha
  rw [stack_frame_toNat stack (by decide) high] at ha
  have bounds := stack_valid_bounds stack
  cases first
  · change region ∈ #v[⟨(stackPtr initial - 360#64 + 0#64).toNat,64⟩,
      ⟨(stackPtr initial - 360#64 + 0#64 + 64#64).toNat,32⟩,
      ⟨(stackPtr initial - 360#64 + 232#64).toNat,64⟩,
      ⟨(stackPtr initial - 360#64 - 344#64).toNat,344⟩] at member
    simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals change _ ≤ a ∧ a < _ at hb
    all_goals dsimp only at hb
    · rw [BitVec.add_zero, stack_valid_sub_toNat stack (by decide)] at hb
      simp only [Bool.false_eq_true, ite_false] at low
      omega
    · rw [BitVec.add_zero, stack_frame_toNat stack (by decide) (by decide)] at hb
      simp only [Bool.false_eq_true, ite_false] at low
      omega
    · rw [stack_frame_toNat stack (by decide) (by decide)] at hb
      simp only [Bool.false_eq_true, ite_false] at low
      omega
    · rw [stack_frame_below_toNat stack (by decide : 360 + 344 ≤ 832)] at hb
      omega
  · change region ∈ #v[⟨(stackPtr initial - 360#64 + 112#64).toNat,64⟩,
      ⟨(stackPtr initial - 360#64 + 112#64 + 64#64).toNat,32⟩,
      ⟨(stackPtr initial - 360#64 + 0#64).toNat,64⟩,
      ⟨(stackPtr initial - 360#64 - 344#64).toNat,344⟩] at member
    simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals change _ ≤ a ∧ a < _ at hb
    all_goals dsimp only at hb
    · rw [stack_frame_toNat stack (by decide) (by decide)] at hb
      simp only [ite_true] at low
      omega
    · rw [BitVec.add_assoc] at hb
      change (stackPtr initial - 360#64 + 176#64).toNat ≤ a ∧ a < (stackPtr initial - 360#64 + 176#64).toNat + 32 at hb
      rw [stack_frame_toNat stack (by decide) (by decide)] at hb
      simp only [ite_true] at low
      omega
    · rw [BitVec.add_zero, stack_valid_sub_toNat stack (by decide)] at hb
      simp only [ite_true] at low
      omega
    · rw [stack_frame_below_toNat stack (by decide : 360 + 344 ≤ 832)] at hb
      omega

theorem first_ready [bindings : Bindings] (v : Wrapper.Variant)
    {routine : Routine} {initial s : RamState} {inputs : Array Input}
    (stride : UnitStringStride bindings) (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall routine initial inputs) (stackSize : routine.minStackBytes = 832)
    (state : ExecutionState initial s (regions routine initial))
    (rsp : rspOf s = stackPtr initial - 360#64)
    (data : Table.InputData (traitFirst v) ((traitFirst v).chunk.sp initial) inputs s)
    (separation : Table.Separation (traitFirst v) initial s 832 inputs)
    (count : memLoad s.external (rspOf s + 104#64) 64 = BitVec.ofNat 64 inputs.size)
    (branch :
      (inputs.size = 0 ∧ s.RIP = Normalize.emptyEntry v .trait ∧
        HasherAt s (rspOf s + 112#64) ByteArray.empty v.initialHash ∧
        s.regValue .r12 = initial.regValue .rcx) ∨
      (Table.LoopState (traitFirst v) ((traitFirst v).chunk.sp initial) inputs 0 s ∧
        memLoad s.external (rspOf s + 296#64) 64 = initial.regValue .rcx)) :
    ∃ n, ExecutionState initial n (regions routine initial) ∧
      Finalize.Prepared (Finalization.traitFirst.layout v)
        (stackPtr initial - 360#64) (message inputs) n ∧
      n.regValue .r12 = initial.regValue .rcx ∧
      (∀ slot, 216 ≤ slot → slot ≤ 360 →
        memLoad n.external (stackPtr initial - 360#64 + BitVec.ofNat 64 slot) 64 =
          memLoad s.external (stackPtr initial - 360#64 + BitVec.ofNat 64 slot) 64) ∧
      memLoad n.external (stackPtr initial - 360#64 + 104#64) 64 = BitVec.ofNat 64 inputs.size := by
  have stack : Stack.Valid initial 832 := by simpa only [stackSize] using call.stack
  rcases branch with ⟨empty, rip, hasher, output⟩ | ⟨loop, output⟩
  · obtain ⟨n, stateN, effect, prepared, memory⟩ := normalized_empty v .trait machine call state rip hasher
    have emptyInputs : inputs = #[] := Array.eq_empty_of_size_eq_zero empty
    have msg : message inputs = ByteArray.empty := by simp [emptyInputs, message]
    refine ⟨n, stateN, ?_, ?_, ?_, ?_⟩
    · simpa only [msg, rsp, Normalize.finalization] using prepared
    · exact (effect.agrees.read (n := 64) (r := 12)
        (by simp [Normalize.emptyEffect, Normalize.tailReg, Normalize.finalization,
          Finalization.variant, Finalize.Variant.registers, Blocks.Length.Registers.tail,
          Effect.components])).trans output
    · intro slot _ _; rw [memory]
    · rw [memory, ← rsp]; exact count
  · obtain ⟨t, done⟩ := traversed true v stride machine call stackSize state loop data separation
    have rspT : rspOf t = stackPtr initial - 360#64 := done.rsp
    have ripT : t.RIP = Normalize.entry true v .trait := by
      have eq : (traitFirst v).exit = Normalize.entry true v .trait := by cases v <;> decide +kernel
      exact done.rip.trans eq
    have hashT : HasherAt t (rspOf t + 112#64) (message inputs) v.initialHash := by
      rw [rspT]
      exact done.hasher
    obtain ⟨n, stateN, effect, prepared⟩ := normalized v true (form := .trait)
      machine call done.state done.rsp ripT hashT stackSize
    have memory : n.external = t.external := Normalize.memory effect
    have saved (slot : Nat) (low : 216 ≤ slot) (high : slot ≤ 360) :=
      table_saved true v stack state done.memory slot low high
    refine ⟨n, stateN, ?_, ?_, ?_, ?_⟩
    · simpa only [rspT, Normalize.finalization] using prepared
    · have out : n.regValue .r12 = memLoad t.external (rspOf t + 296#64) 64 :=
        Normalize.restored_output effect
      rw [out, rspT, saved 296 (by decide) (by decide), ← rsp]
      exact output
    · intro slot low high
      rw [memory, saved slot low high]
    · rw [memory]
      exact done.count

theorem reinitialized [bindings : Bindings] (v : Wrapper.Variant)
    {routine : Routine} {initial s : RamState} {inputs : Array Input} {first : ByteArray}
    (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall routine initial inputs) (capacity : 360 ≤ routine.minStackBytes)
    (state : ExecutionState initial s (regions routine initial))
    (rsp : rspOf s = stackPtr initial - 360#64)
    (rip : s.RIP = (Initialization.traitReset.layout v).start)
    (base : s.regValue .rbp = rspOf s + 176#64)
    (firstBytes : (TwoOutputs.outputRegion routine initial).HasBytes s.external first) :
    ∃ t, ExecutionState initial t (regions routine initial) ∧
      Initialize.Post (Initialization.traitReset.layout v) (rspOf s + 112#64) s t ∧
      rspOf t = rspOf s ∧ t.RIP = secondPC v ∧
      HasherAt t (rspOf t + 112#64) ByteArray.empty v.initialHash ∧
      (TwoOutputs.outputRegion routine initial).HasBytes t.external first := by
  obtain ⟨t, stateT, init⟩ := initialize_state_at v (occ := .traitReset)
    machine call state rsp rip capacity (by decide) (by intro _; exact base)
  have frame : MemoryWriteFrame s t
      #v[TwoOutputs.secondOutputRegion routine initial, Stack.region initial routine.minStackBytes] := by
    apply init.frame.memoryWriteFrame
    intro c hc a ha
    change c ∈ [.reg 0#5, .reg 0#5, .reg 0#5, .reg 0#5,
      .mem (rspOf s + 112#64 + 64#64) 32, .mem (rspOf s + 112#64 + 96#64) 8,
      .mem (rspOf s + 112#64 + 63#64) 1, .rip] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals refine ⟨Stack.region initial routine.minStackBytes, by simp, ?_⟩
    all_goals rw [rsp, BitVec.add_assoc] at ha
    · exact stack_frame_contains call.stack (frame := 360) (offset := 176) (len := 32)
        capacity (by decide) ha
    · exact stack_frame_contains call.stack (frame := 360) (offset := 208) (len := 8)
        capacity (by decide) ha
    · exact stack_frame_contains call.stack (frame := 360) (offset := 175) (len := 1)
        capacity (by decide) ha
  have rspT : rspOf t = rspOf s := init.rsp
  refine ⟨t, stateT, init, rspT, ?_, ?_, ?_⟩
  · rw [init.rip]
    change (Initialization.traitReset.layout v).finish = secondPC v
    cases v <;> decide +kernel
  · rw [rspT]; exact init.hasher
  · refine ⟨firstBytes.1, fun i => ?_⟩
    rw [firstOutput_unchanged call frame ?_]
    · exact firstBytes.2 i
    · have bound := (call.outputInMemory (TwoOutputs.outputRegion routine initial) (by simp)).2.1
      have size := firstBytes.1
      change first.size = (TwoOutputs.outputRegion routine initial).size at size
      change (TwoOutputs.outputRegion routine initial).start +
        (TwoOutputs.outputRegion routine initial).size < 2^32 at bound
      change _ ≤ (BitVec.ofNat 64 ((TwoOutputs.outputRegion routine initial).start + i.val)).toNat ∧ _
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega

theorem last_prepared [bindings : Bindings] (v : Wrapper.Variant)
    {routine : Routine} {initial s : RamState} {inputs : Array Input} {message : ByteArray}
    (stride : UnitStringStride bindings) (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall routine initial inputs) (stackSize : routine.minStackBytes = 832)
    (state : ExecutionState initial s (regions routine initial))
    (rsp : rspOf s = stackPtr initial - 360#64)
    (rip : s.RIP = (traitLastTable v).exit)
    (hasher : HasherAt s (rspOf s + 112#64) message v.initialHash) :
    ∃ n, ExecutionState initial n (regions routine initial) ∧
      Finalize.Prepared (Finalization.traitLast.layout v) (stackPtr initial - 360#64) message n ∧
      MemoryWriteFrame s n #v[⟨(stackPtr initial - 360#64).toNat, 104⟩] := by
  have inside : BlockInProgram (traitLastTable v).exit
      ((Blocks.Digest.CloneSetup.bytesFor .traitLast).length + 3) := by
    cases v with
    | sha224 => exact blockInProgram_of_textOffset 0x19fe _ (by decide +kernel)
    | sha256 => exact blockInProgram_of_textOffset 0x365e _ (by decide +kernel)
  have code : CodeIn (codeRange (traitLastTable v).exit
      (Blocks.Digest.CloneSetup.bytesFor .traitLast ++ [0xf3,0x48,0xa5])) s := by
    cases v with
    | sha224 =>
      exact programText_slice (programLoaded_codeIn state.loaded) 0x19fe _
        (by decide +kernel) (by decide +kernel)
    | sha256 =>
      exact programText_slice (programLoaded_codeIn state.loaded) 0x365e _
        (by decide +kernel) (by decide +kernel)
  obtain ⟨c,t,stateT,_,_,hashT,rspT,ripT,frame⟩ :=
    FinalizeIntoReset.cloned_stack .traitLast routine (traitLastTable v).exit
      stride machine call (by rw [stackSize]; decide) state rsp rip hasher inside code
  have entry : t.RIP = Normalize.entry false v .trait := ripT.trans (by cases v <;> decide +kernel)
  have hash : HasherAt t (rspOf t + 0#64) message v.initialHash := by
    simpa only [rspT, Blocks.Digest.CloneSetup.Kind.destination, BitVec.ofNat_eq_ofNat] using hashT
  obtain ⟨n,stateN,effect,prepared⟩ := normalized v false (form := .trait)
    machine call stateT (rspT.trans rsp) entry hash stackSize
  refine ⟨n,stateN,?_,?_⟩
  · simpa only [Normalize.finalization,rspT,rsp] using prepared
  · have memory := Normalize.memory effect
    intro a outside
    rw [memory]
    apply frame a
    simpa only [Blocks.Digest.CloneSetup.Kind.destination, BitVec.ofNat_eq_ofNat, BitVec.add_zero, rsp] using outside

def lastStorePC (v : Wrapper.Variant) : BitVec 64 :=
  if v = .sha224 then 0x101bc0 else 0x103828

def returnPC (v : Wrapper.Variant) : BitVec 64 :=
  if v = .sha224 then 0x101bdb else 0x103847

theorem last_serialized [bindings : Bindings] (v : Wrapper.Variant)
    {routine : Routine} {initial s : RamState} {inputs : Array Input} {hash : Array UInt32} {first : ByteArray}
    (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall routine initial inputs)
    (capacity : 360 ≤ routine.minStackBytes) (size : routine.outputBytes = v.outputBytes)
    (state : ExecutionState initial s (regions routine initial))
    (rsp : rspOf s = stackPtr initial - 360#64)
    (rip : s.RIP = (Finalization.traitLast.layout v).exit)
    (words : HashStateAt s (rspOf s + 64#64) hash)
    (saved : memLoad s.external (rspOf s + 304#64) 64 = initial.regValue .r8)
    (firstBytes : (TwoOutputs.outputRegion routine initial).HasBytes s.external first) :
    ∃ t, ExecutionState initial t (regions routine initial) ∧
      t.RIP = returnPC v ∧
      (TwoOutputs.outputRegion routine initial).HasBytes t.external first ∧
      (TwoOutputs.secondOutputRegion routine initial).HasBytes t.external (v.serializeHash hash) ∧
      rspOf t = rspOf s ∧
      MemoryWriteFrame s t #v[TwoOutputs.secondOutputRegion routine initial] := by
  have inside : BlockInProgram (lastStorePC v)
      (Serialize.bytes (.store (if v = .sha224 then .r10 else .r11) (v == .sha224))).length := by
    cases v with
    | sha224 => exact blockInProgram_of_textOffset 0x1bc0 _ (by decide +kernel)
    | sha256 => exact blockInProgram_of_textOffset 0x3828 _ (by decide +kernel)
  obtain ⟨t,stateT,ripT,firstT,secondT,rspT,frame⟩ := serialized_last_generic v routine 360 .at64 304
    (Finalization.traitLast.layout v).exit (lastStorePC v) capacity (by decide) (by decide)
    (by decide) size (by cases v <;> decide +kernel)
    (by
      cases v with
      | sha224 => exact blockInProgram_of_textOffset 0x1b8a _ (by decide +kernel)
      | sha256 => exact blockInProgram_of_textOffset 0x37ea _ (by decide +kernel))
    (by
      intro u loaded
      cases v with
      | sha224 =>
        exact programText_slice (programLoaded_codeIn loaded) 0x1b8a _ (by decide +kernel) (by decide +kernel)
      | sha256 =>
        exact programText_slice (programLoaded_codeIn loaded) 0x37ea _ (by decide +kernel) (by decide +kernel))
    (by
      intro u loaded
      cases v with
      | sha224 =>
        exact programText_slice (programLoaded_codeIn loaded) 0x1bb8 _ (by decide +kernel) (by decide +kernel)
      | sha256 =>
        exact programText_slice (programLoaded_codeIn loaded) 0x3820 _ (by decide +kernel) (by decide +kernel))
    (by simpa using inside 0 (by omega)) inside
    (by
      intro u loaded
      cases v with
      | sha224 =>
        exact programText_slice (programLoaded_codeIn loaded) 0x1bc0 _ (by decide +kernel) (by decide +kernel)
      | sha256 =>
        exact programText_slice (programLoaded_codeIn loaded) 0x3828 _ (by decide +kernel) (by decide +kernel))
    machine call state rsp rip words saved firstBytes
  refine ⟨t,stateT,?_,firstT,?_,rspT,frame⟩
  · exact ripT.trans (by cases v <;> decide +kernel)
  · cases v <;> exact secondT

theorem returned [bindings : Bindings] (v : Wrapper.Variant)
    {routine : Routine} {initial s : RamState} {inputs : Array Input}
    (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall routine initial inputs) (capacity : 360 ≤ routine.minStackBytes)
    (state : ExecutionState initial s (regions routine initial))
    (rsp : rspOf s = stackPtr initial - 360#64) (rip : s.RIP = returnPC v)
    (saved : ∀ (r : BitVec 5) (offset : Nat),
      (r,offset) ∈ [(3,0),(12,8),(13,16),(14,24),(15,32),(5,40)] →
      memLoad s.external (rspOf s + BitVec.ofNat 64 (312+offset)) 64 =
        (Operand.reg r : Operand 64).read initial)
    (ret : memLoad s.external (stackPtr initial) 64 = (returnBoundary initial).rip) :
    ∃ fuel final, UniqueExecution initial fuel final ∧ SupportedMachine bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧ DirectionFlagUnset final ∧
      MemoryWriteFrame initial final (regions routine initial) ∧ final.external = s.external := by
  apply returned_at routine .six312 (returnPC v) rfl capacity machine call state rsp rip
  · intro r offset member
    apply saved r offset
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    rcases member with h | h | h | h | h <;> simp [h]
  · exact saved 5 40 (by simp)
  · cases v with
    | sha224 => exact blockInProgram_of_textOffset 0x1bdb _ (by decide +kernel)
    | sha256 => exact blockInProgram_of_textOffset 0x3847 _ (by decide +kernel)
  · cases v with
    | sha224 =>
      exact programText_slice (programLoaded_codeIn state.loaded) 0x1bdb _ (by decide +kernel) (by decide +kernel)
    | sha256 =>
      exact programText_slice (programLoaded_codeIn state.loaded) 0x3847 _ (by decide +kernel) (by decide +kernel)
  · exact ret

theorem first_completed [bindings : Bindings] (v : Wrapper.Variant)
    {routine : Routine} {initial s : RamState} {inputs : Array Input}
    (stride : UnitStringStride bindings) (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall routine initial inputs) (stackSize : routine.minStackBytes = 832)
    (size : routine.outputBytes = v.outputBytes)
    (state : ExecutionState initial s (regions routine initial))
    (prepared : Finalize.Prepared (Finalization.traitFirst.layout v)
      (stackPtr initial - 360#64) (message inputs) s)
    (output : s.regValue .r12 = initial.regValue .rcx) :
    ∃ t, ExecutionState initial t (regions routine initial) ∧
      rspOf t = stackPtr initial - 360#64 ∧ t.RIP = secondPC v ∧
      HasherAt t (rspOf t + 112#64) ByteArray.empty v.initialHash ∧
      (TwoOutputs.outputRegion routine initial).HasBytes t.external (v.hash (message inputs)) ∧
      (∀ slot, (slot = 104 ∨ 216 ≤ slot) → slot ≤ 360 →
        memLoad t.external (stackPtr initial - 360#64 + BitVec.ofNat 64 slot) 64 =
          memLoad s.external (stackPtr initial - 360#64 + BitVec.ofNat 64 slot) 64) := by
  have capacity : 360 ≤ routine.minStackBytes := by rw [stackSize]; decide
  have stack : Stack.Valid initial 832 := by simpa only [stackSize] using call.stack
  obtain ⟨f,done⟩ := finalized v .traitFirst stackSize stride machine call state prepared
  have rspF : rspOf f = stackPtr initial - 360#64 := done.rsp
  obtain ⟨hash,words,digest⟩ := done.digest
  have wordsF : HashStateAt f (rspOf f + 176#64) hash := by
    rw [rspF]
    change HashStateAt f (stackPtr initial - 360#64 + 112#64 + 64#64) hash at words
    simpa only [BitVec.add_assoc, show 112#64 + 64#64 = 176#64 from by decide] using words
  have outputF : f.regValue .r12 = initial.regValue .rcx :=
    (done.frame.registers 12 (by decide) (by change ¬ 12#5 ∈ Finalize.Variant.traitFirst.clobbered; decide +kernel)).trans output
  have baseF : f.regValue .rbp = rspOf f + 176#64 := by
    rw [rspF]
    have hp := done.hashPointer
    change f.regValue .rbp = stackPtr initial - 360#64 + 112#64 + 64#64 at hp
    simpa only [BitVec.add_assoc, show 112#64 + 64#64 = 176#64 from by decide] using hp
  obtain ⟨a,b,stateB,load,store,frame,bytes,rspB,ripB⟩ := first_serialized v machine call
    capacity size done.state rspF done.rip wordsF outputF
  have baseB : b.regValue .rbp = rspOf b + 176#64 := by
    rw [rspB]
    exact ((store.agrees.read (n := 64) (r := 5)
      (by cases v <;> simp [Serialize.effect, Effect.components])).trans
      (load.agrees.read (n := 64) (r := 5)
        (by cases v <;> simp [Serialize.effect, Effect.components]))).trans baseF
  obtain ⟨t,stateT,init,rspT,ripT,hasher,first⟩ := reinitialized v machine call capacity
    stateB (rspB.trans rspF) ripB baseB bytes
  refine ⟨t,stateT,rspT.trans (rspB.trans rspF),ripT,hasher,?_,?_⟩
  · change v.serializeHash hash = v.hash (message inputs) at digest
    rw [← digest]; exact first
  · intro slot low high
    have initSaved := Reset.initialize_saved (occ := .traitReset) init slot (by
      change slot + 8 ≤ 175 ∨ 216 ≤ slot
      omega) high
    rw [rspB,rspF] at initSaved
    refine initSaved.trans ((Last.output_word call (by simp) frame capacity slot high).trans ?_)
    apply finalized_saved true v stack state done.frame.memory slot _ high
    rcases low with eq | ge
    · exact Or.inl ⟨rfl,eq⟩
    · exact Or.inr ge

set_option maxRecDepth 2048 in
theorem last_finalized [bindings : Bindings] (v : Wrapper.Variant)
    {routine : Routine} {initial s : RamState} {inputs : Array Input} {first : ByteArray}
    (stride : UnitStringStride bindings) (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall routine initial inputs) (stackSize : routine.minStackBytes = 832)
    (state : ExecutionState initial s (regions routine initial))
    (rsp : rspOf s = stackPtr initial - 360#64)
    (rip : s.RIP = (traitLastTable v).exit)
    (hasher : HasherAt s (rspOf s + 112#64) (message inputs) v.initialHash)
    (bytes : (TwoOutputs.outputRegion routine initial).HasBytes s.external first) :
    ∃ n t, Finalize.Finalized (Finalization.traitLast.layout v) initial n t
      (regions routine initial) (message inputs) ∧
      (TwoOutputs.outputRegion routine initial).HasBytes t.external first ∧
      (∀ slot, 296 ≤ slot → slot ≤ 360 →
        memLoad t.external (stackPtr initial - 360#64 + BitVec.ofNat 64 slot) 64 =
          memLoad s.external (stackPtr initial - 360#64 + BitVec.ofNat 64 slot) 64) := by
  have stack : Stack.Valid initial 832 := by simpa only [stackSize] using call.stack
  obtain ⟨n,stateN,prepared,frame⟩ := last_prepared v stride machine call stackSize state rsp rip hasher
  have within : ∀ region ∈ (#v[⟨(stackPtr initial - 360#64).toNat,104⟩] : Vector MemoryRegion 1),
      ∀ a, region.Contains a → (Stack.region initial routine.minStackBytes).Contains a := by
    intro region member a ha
    simp only [Vector.mem_mk, List.mem_toArray, List.mem_singleton] at member
    subst region
    change _ ≤ a ∧ a < _ at ha
    dsimp only at ha
    rw [stack_valid_sub_toNat stack (by decide)] at ha
    rw [stackSize]
    have bounds := stack_valid_bounds stack
    change (stackPtr initial).toNat - 832 ≤ a ∧ a < (stackPtr initial).toNat - 832 +
      ((stackPtr initial).toNat + 8 - ((stackPtr initial).toNat - 832))
    omega
  have below : ∀ region ∈ (#v[⟨(stackPtr initial - 360#64).toNat,104⟩] : Vector MemoryRegion 1),
      ∀ a, region.Contains a → a < (stackPtr initial).toNat - 64 := by
    intro region member a ha
    simp only [Vector.mem_mk, List.mem_toArray, List.mem_singleton] at member
    subst region
    change _ ≤ a ∧ a < _ at ha
    dsimp only at ha
    rw [stack_valid_sub_toNat stack (by decide)] at ha
    have bounds := stack_valid_bounds stack
    omega
  obtain ⟨bytesN,same⟩ := Last.frame_preserves call frame within below bytes
  obtain ⟨t,done⟩ := finalized v .traitLast stackSize stride machine call stateN prepared
  refine ⟨n,t,done,?_,?_⟩
  · apply Last.frame_preserves_output call done.frame.memory _ bytesN
    simpa only [stackSize, Finalization.reserve] using Finalize.footprint_subset_stack
      (Finalization.traitLast.wellFormed (v := v)) stack
  · intro slot low high
    exact (finalized_saved false v stack stateN done.frame.memory slot (Or.inr low) high).trans
      (Last.high_word stack (by decide) same slot (by omega) high)

theorem last_absorbed [bindings : Bindings] (v : Wrapper.Variant)
    {routine : Routine} {initial s : RamState} {inputs : Array Input} {first : ByteArray}
    (stride : UnitStringStride bindings) (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall routine initial inputs) (stackSize : routine.minStackBytes = 832)
    (state : ExecutionState initial s (regions routine initial))
    (rsp : rspOf s = stackPtr initial - 360#64)
    (bytes : (TwoOutputs.outputRegion routine initial).HasBytes s.external first)
    (branch : (inputs.size = 0 ∧ s.RIP = (traitLastTable v).exit ∧
        HasherAt s (rspOf s + 112#64) ByteArray.empty v.initialHash) ∨
      (Table.LoopState (traitLastTable v) ((traitLastTable v).chunk.sp initial) inputs 0 s ∧
        Table.InputData (traitLastTable v) ((traitLastTable v).chunk.sp initial) inputs s ∧
        Table.Separation (traitLastTable v) initial s routine.minStackBytes inputs)) :
    ∃ n t, Finalize.Finalized (Finalization.traitLast.layout v) initial n t
      (regions routine initial) (message inputs) ∧
      (TwoOutputs.outputRegion routine initial).HasBytes t.external first ∧
      (∀ slot, 296 ≤ slot → slot ≤ 360 →
        memLoad t.external (stackPtr initial - 360#64 + BitVec.ofNat 64 slot) 64 =
          memLoad s.external (stackPtr initial - 360#64 + BitVec.ofNat 64 slot) 64) := by
  rcases branch with ⟨empty,rip,hash⟩ | ⟨loop,data,separation⟩
  · have msg : message inputs = ByteArray.empty := by
      simp [Array.eq_empty_of_size_eq_zero empty, message]
    exact last_finalized v stride machine call stackSize state rsp rip (by rw [msg]; exact hash) bytes
  · have stack : Stack.Valid initial 832 := by simpa only [stackSize] using call.stack
    obtain ⟨a,done⟩ := traversed false v stride machine call stackSize state loop data
      (by simpa [stackSize, table] using separation)
    have rspA : rspOf a = stackPtr initial - 360#64 := done.rsp
    have bytesA := Last.frame_preserves_output call done.memory (by
      simpa [stackSize, table] using Table.footprint_subset_stack (traitLastTable_wellFormed v) stack) bytes
    obtain ⟨n,t,finalized,bytesT,saved⟩ := last_finalized v stride machine call stackSize done.state
      rspA done.rip (by rw [rspA]; exact done.hasher) bytesA
    refine ⟨n,t,finalized,bytesT,fun slot low high => (saved slot low high).trans ?_⟩
    exact table_saved false v stack state done.memory slot (by omega) high

theorem completed [bindings : Bindings] (v : Wrapper.Variant)
    {routine : Routine} {initial s : RamState} {inputs : Array Input}
    (stride : UnitStringStride bindings) (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall routine initial inputs) (stackSize : routine.minStackBytes = 832)
    (size : routine.outputBytes = v.outputBytes)
    (state : ExecutionState initial s (regions routine initial))
    (rsp : rspOf s = stackPtr initial - 360#64) (rip : s.RIP = secondPC v)
    (hasher : HasherAt s (rspOf s + 112#64) ByteArray.empty v.initialHash)
    (count : memLoad s.external (rspOf s + 104#64) 64 = BitVec.ofNat 64 inputs.size)
    (pointer : memLoad s.external (rspOf s + 216#64) 64 = initial.regValue .rdi)
    (length : memLoad s.external (rspOf s + 224#64) 64 = initial.regValue .rdx)
    (second : memLoad s.external (rspOf s + 304#64) 64 = initial.regValue .r8)
    (bytes : (TwoOutputs.outputRegion routine initial).HasBytes s.external (v.hash (message inputs)))
    (saved : ∀ (r : BitVec 5) (offset : Nat),
      (r,offset) ∈ [(3,0),(12,8),(13,16),(14,24),(15,32),(5,40)] →
      memLoad s.external (rspOf s + BitVec.ofNat 64 (312+offset)) 64 =
        (Operand.reg r : Operand 64).read initial)
    (ret : memLoad s.external (stackPtr initial) 64 = (returnBoundary initial).rip) :
    ∃ fuel final, UniqueExecution initial fuel final ∧ SupportedMachine bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧ DirectionFlagUnset final ∧
      MemoryWriteFrame initial final (regions routine initial) ∧
      (TwoOutputs.outputRegion routine initial).HasBytes final.external (v.hash (message inputs)) ∧
      (TwoOutputs.secondOutputRegion routine initial).HasBytes final.external (v.hash (message inputs)) := by
  have capacity : 360 ≤ routine.minStackBytes := by rw [stackSize]; decide
  obtain ⟨a,stateA,memoryA,rspA,branch⟩ := second_dispatched v machine call capacity state rsp rip hasher count pointer length
  obtain ⟨n,f,done,bytesF,slotsF⟩ := last_absorbed v stride machine call stackSize stateA (rspA.trans rsp)
    (by rw [memoryA]; exact bytes) branch
  have rspF : rspOf f = stackPtr initial - 360#64 := done.rsp
  obtain ⟨hash,words,digest⟩ := done.digest
  have wordsF : HashStateAt f (rspOf f + 64#64) hash := by
    rw [rspF]
    change HashStateAt f (stackPtr initial - 360#64 + 0#64 + 64#64) hash at words
    simpa only [BitVec.add_zero] using words
  have secondF : memLoad f.external (rspOf f + 304#64) 64 = initial.regValue .r8 := by
    rw [rspF,slotsF 304 (by decide) (by decide),memoryA,← rsp]
    exact second
  obtain ⟨t,stateT,ripT,firstT,secondT,rspT,frame⟩ := last_serialized v machine call capacity size
    done.state rspF done.rip wordsF secondF bytesF
  have same (slot : Nat) (low : 296 ≤ slot) (high : slot ≤ 360) :
      memLoad t.external (stackPtr initial - 360#64 + BitVec.ofNat 64 slot) 64 =
        memLoad s.external (stackPtr initial - 360#64 + BitVec.ofNat 64 slot) 64 := by
    rw [Last.output_word call (by simp) frame capacity slot high,slotsF slot low high,memoryA]
  have savedT (r : BitVec 5) (offset : Nat)
      (member : (r,offset) ∈ [(3,0),(12,8),(13,16),(14,24),(15,32),(5,40)]) :
      memLoad t.external (rspOf t + BitVec.ofNat 64 (312+offset)) 64 =
        (Operand.reg r : Operand 64).read initial := by
    have bound : offset ≤ 40 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
      omega
    rw [rspT,rspF,same (312+offset) (by omega) (by omega),← rsp]
    exact saved r offset member
  have retT : memLoad t.external (stackPtr initial) 64 = (returnBoundary initial).rip := by
    have eq := same 360 (by decide) (by decide)
    simpa only [BitVec.ofNat_eq_ofNat,BitVec.sub_add_cancel] using eq.trans (by
      simpa only [BitVec.ofNat_eq_ofNat,BitVec.sub_add_cancel] using ret)
  obtain ⟨fuel,final,unique,machineFinal,abi,df,frameFinal,memory⟩ := returned v machine call capacity
    stateT (rspT.trans rspF) ripT savedT retT
  refine ⟨fuel,final,unique,machineFinal,abi,df,frameFinal,?_,?_⟩
  · rw [memory]; exact firstT
  · rw [memory]
    change v.serializeHash hash = v.hash (message inputs) at digest
    rw [← digest]; exact secondT

theorem correct [bindings : Bindings] (v : Wrapper.Variant)
    {initial : RamState} {inputs : Array Input}
    (stride : UnitStringStride bindings) (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall (Header.Layout.trait.routine v) initial inputs) :
    ∃ fuel final, UniqueExecution initial fuel final ∧ SupportedMachine bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧ DirectionFlagUnset final ∧
      MemoryWriteFrame initial final (regions (Header.Layout.trait.routine v) initial) ∧
      (TwoOutputs.outputRegion (Header.Layout.trait.routine v) initial).HasBytes final.external
        (v.hash (message inputs)) ∧
      (TwoOutputs.secondOutputRegion (Header.Layout.trait.routine v) initial).HasBytes final.external
        (v.hash (message inputs)) := by
  have stackSize : (Header.Layout.trait.routine v).minStackBytes = 832 := by cases v <;> rfl
  have size : (Header.Layout.trait.routine v).outputBytes = v.outputBytes := by cases v <;> rfl
  obtain ⟨p,h,u,s,push,args,init,stateS,data,separation,rspS,frame,pointer,length,second,count,branch⟩ :=
    TraitPrefix.dispatched v machine call
  have spS : rspOf s = stackPtr initial - 360#64 := rspS
  have rspP : rspOf p = stackPtr initial - 360#64 := push.writes.2.2.2.2.2.2
  have rspH : rspOf h = rspOf p := args.agrees.read (n := 64) (r := 4)
    (by simp [Header.effectAt,Effect.components])
  have rspU : rspOf u = stackPtr initial - 360#64 := init.rsp.trans (rspH.trans rspP)
  have abi := TraitPrefix.dispatched_saved push args init (spS.trans rspU.symm)
    (by rw [rspU]; exact frame)
  have branchS :
      (inputs.size = 0 ∧ s.RIP = Normalize.emptyEntry v .trait ∧
        HasherAt s (rspOf s + 112#64) ByteArray.empty v.initialHash ∧ s.regValue .r12 = initial.regValue .rcx) ∨
      (Table.LoopState (traitFirst v) ((traitFirst v).chunk.sp initial) inputs 0 s ∧
        memLoad s.external (rspOf s + 296#64) 64 = initial.regValue .rcx) := by
    rw [spS]
    rcases branch with ⟨empty,rip,hash,output⟩ | ⟨loop,saved⟩
    · refine Or.inl ⟨empty,?_,hash,output⟩
      exact rip.trans (by cases v <;> decide +kernel)
    · exact Or.inr ⟨loop,saved⟩
  obtain ⟨n,stateN,prepared,outputN,slotsN,countN⟩ := first_ready v stride machine call stackSize stateS
    spS data (by simpa only [stackSize] using separation) (by rw [spS]; exact count) branchS
  obtain ⟨t,stateT,rspT,ripT,empty,first,slotsT⟩ := first_completed v stride machine call stackSize size
    stateN prepared outputN
  have same (slot : Nat) (low : 216 ≤ slot) (high : slot ≤ 360) :
      memLoad t.external (rspOf t + BitVec.ofNat 64 slot) 64 =
        memLoad s.external (rspOf s + BitVec.ofNat 64 slot) 64 := by
    rw [rspT,spS,slotsT slot (Or.inr low) high,slotsN slot low high]
  have countT : memLoad t.external (rspOf t + 104#64) 64 = BitVec.ofNat 64 inputs.size := by
    rw [rspT,slotsT 104 (Or.inl rfl) (by decide)]
    exact countN
  have pointerT : memLoad t.external (rspOf t + 216#64) 64 = initial.regValue .rdi := by
    rw [same 216 (by decide) (by decide),spS]; exact pointer
  have lengthT : memLoad t.external (rspOf t + 224#64) 64 = initial.regValue .rdx := by
    rw [same 224 (by decide) (by decide),spS]; exact length
  have secondT : memLoad t.external (rspOf t + 304#64) 64 = initial.regValue .r8 := by
    rw [same 304 (by decide) (by decide),spS]; exact second
  have savedT (r : BitVec 5) (offset : Nat)
      (member : (r,offset) ∈ [(3,0),(12,8),(13,16),(14,24),(15,32),(5,40)]) :
      memLoad t.external (rspOf t + BitVec.ofNat 64 (312+offset)) 64 =
        (Operand.reg r : Operand 64).read initial := by
    have bound : offset ≤ 40 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at member
      omega
    rw [same (312+offset) (by omega) (by omega)]
    exact abi.1 r offset member
  have retT : memLoad t.external (stackPtr initial) 64 = (returnBoundary initial).rip := by
    have eq := (same 360 (by decide) (by decide)).trans abi.2
    rw [rspT,BitVec.sub_add_cancel] at eq
    exact eq
  exact completed v stride machine call stackSize size stateT rspT ripT empty countT pointerT lengthT secondT first savedT retT

end Sha2.Proofs.Reset.TraitFinalizeIntoReset
