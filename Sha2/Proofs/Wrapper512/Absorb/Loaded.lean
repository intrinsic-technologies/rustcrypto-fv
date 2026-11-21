import Sha2.Proofs.Wrapper512.Absorb.Load
import Sha2.Proofs.Wrapper512.Absorb.State
import Sha2.Proofs.Wrapper512.Dispatch.Initialize
import Sha2.Proofs.Wrapper512.Finish.Copy

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Absorb
open Sha2.Proofs.Program Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA512
open Sha2.Proofs.Wrapper

theorem table_readable [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Input}
    {form : Form} (ctx : Context v initial inputs form) (nondigest : form ≠ .digest)
    (state : MemoryWriteFrame initial s (v.writeRegions initial form))
    {table : MemoryRegion} (read : table ∈ readRegions initial inputs)
    (bounded : table.Bounded) (size : table.size = 8*inputs.size)
    (i : Fin inputs.size) {value : BitVec 64}
    (word : (tableEntry table i).Word64At initial.external value) :
    MemReadable s (BitVec.ofNat 64 (table.start + 8*i.val)) 8 ∧
      memLoad s.external (BitVec.ofNat 64 (table.start + 8*i.val)) 64 = value := by
  have unchanged : ∀ region ∈ readRegions initial inputs, ∀ address : BitVec 64,
      region.Contains address.toNat → s.external[address]? = initial.external[address]? := by
    intro region hr address ha
    apply state address
    intro writable hw
    apply (ctx.separation.2 writable (by simpa using hw)).1 region _ address.toNat ha
    cases form <;> first | contradiction | exact hr
  have loaded := table_word_of_read_unchanged unchanged read bounded size i word
  refine ⟨⟨?_, Sha2.Proofs.Common.Memory.loadBytes_allocated loaded⟩,
    Sha2.Proofs.Common.Memory.memLoad_of_loadBytes64 loaded⟩
  have bound : table.start + table.size < 2^32 := bounded
  rw [size] at bound
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := i.isLt; omega)]
  have := i.isLt
  omega

theorem input_tables [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Input}
    {form : Form} (ctx : Context v initial inputs form) (nondigest : form ≠ .digest)
    (state : MemoryWriteFrame initial s (v.writeRegions initial form)) (i : Fin inputs.size) :
    (MemReadable s (initial.regValue .rdi + BitVec.ofNat 64 (8*i.val)) 8 ∧
      memLoad s.external (initial.regValue .rdi + BitVec.ofNat 64 (8*i.val)) 64 = inputs[i].address) ∧
    (MemReadable s (initial.regValue .rdx + BitVec.ofNat 64 (8*i.val)) 8 ∧
      memLoad s.external (initial.regValue .rdx + BitVec.ofNat 64 (8*i.val)) 64 =
        BitVec.ofNat 64 inputs[i].bytes.size) := by
  have hp : (pointerTable initial inputs.size).Bounded ∧
      (tableEntry (pointerTable initial inputs.size) i).Word64At initial.external inputs[i].address := by
    cases form with
    | digest => contradiction
    | slices | reset _ | finalizeIntoReset _ | traitFinalizeIntoReset _ =>
      exact ⟨ctx.call.pointerTableValid.2, (ctx.call.inputsInMemory i).2.1⟩
  have hl : (lengthTable initial inputs.size).Bounded ∧
      (tableEntry (lengthTable initial inputs.size) i).Word64At initial.external
        (BitVec.ofNat 64 inputs[i].bytes.size) := by
    cases form with
    | digest => contradiction
    | slices | reset _ | finalizeIntoReset _ | traitFinalizeIntoReset _ =>
      exact ⟨ctx.call.lengthTableValid.2, (ctx.call.inputsInMemory i).2.2.1⟩
  constructor
  · simpa only [pointerTable, registerRegion, BitVec.ofNat_add, BitVec.ofNat_toNat,
      BitVec.setWidth_eq] using table_readable ctx nondigest state
        (by simp [readRegions]) hp.1 rfl i hp.2
  · simpa only [lengthTable, registerRegion, BitVec.ofNat_add, BitVec.ofNat_toNat,
      BitVec.setWidth_eq] using table_readable ctx nondigest state
        (by simp [readRegions]) hl.1 rfl i hl.2
set_option maxRecDepth 2048 in
theorem load_pair_input [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Input}
    {index : Nat} {form : Form} (ctx : Context v initial inputs form)
    (nondigest : form ≠ .digest) (input : LoopState v initial s inputs index form) :
    Sha2.Proofs.Common.SHA256.Absorb.Blocks.Pre (v.pc (v.traversal form).head form)
      (Load.pair v form) s ∧
    memLoad s.external (memLoad s.external (rspOf s + (Load.pointerDisp form).value) 64 +
      (Sha2.Proofs.Common.SHA256.Absorb.Blocks.readReg s (BitVec.ofNat 4 (v.traversal form).indexReg) <<< 3)) 64 = (inputs[index]'input.remaining).address ∧
    memLoad s.external (memLoad s.external (rspOf s + (Load.lengthDisp form).value) 64 +
      (Sha2.Proofs.Common.SHA256.Absorb.Blocks.readReg s (BitVec.ofNat 4 (v.traversal form).indexReg) <<< 3)) 64 = BitVec.ofNat 64 (inputs[index]'input.remaining).bytes.size := by
  have values := input_tables ctx nondigest input.frame ⟨index, input.remaining⟩
  have index_eq : Sha2.Proofs.Common.SHA256.Absorb.Blocks.readReg s
      (BitVec.ofNat 4 (v.traversal form).indexReg) = BitVec.ofNat 64 index := by
    have eq : (BitVec.ofNat 4 (v.traversal form).indexReg).setWidth 5 =
        BitVec.ofNat 5 (v.traversal form).indexReg := by
      cases form with
      | slices | digest => rfl
      | reset stage =>
        rcases stage with ⟨_ | _ | _ | n, h⟩ <;> try omega
        all_goals cases v <;> rfl
      | finalizeIntoReset second | traitFinalizeIntoReset second =>
        cases second <;> cases v <;> rfl
    simpa only [Sha2.Proofs.Common.SHA256.Absorb.Blocks.readReg, eq, Variant.indexValue] using input.indexRegister
  have shifted : Sha2.Proofs.Common.SHA256.Absorb.Blocks.readReg s
      (BitVec.ofNat 4 (v.traversal form).indexReg) <<< 3 = BitVec.ofNat 64 (8*index) := by
    rw [index_eq, BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 64 index * BitVec.ofNat 64 8 = _
    rw [← BitVec.ofNat_mul, Nat.mul_comm]
  have slot (disp : Disp) (offset : Nat)
      (eq : disp.value = BitVec.ofNat 64 form.frameBytes - BitVec.ofNat 64 offset) :
      rspOf s + disp.value = stackPtr initial - BitVec.ofNat 64 offset := by
    change stackPtr s + disp.value = _
    rw [input.rsp, eq]
    rw [BitVec.sub_eq_add_neg (BitVec.ofNat 64 form.frameBytes), ← BitVec.add_assoc, BitVec.sub_add_cancel]
    exact (BitVec.sub_eq_add_neg _ _).symm
  have pointerAddr := slot (Load.pointerDisp form) form.pointerSlot (by
    cases form <;> first | contradiction | (dsimp only [Load.pair, Load.pointerDisp, Load.lengthDisp, Form.pointerSlot, Form.lengthSlot, Form.frameBytes, Form.stackBytes, Variant.traversal, ResetLayout.reset, ResetLayout.finalizeIntoReset, ResetLayout.traitFinalizeIntoReset]; all_goals decide +kernel))
  have lengthAddr := slot (Load.lengthDisp form) form.lengthSlot (by
    cases form <;> first | contradiction | (dsimp only [Load.pair, Load.pointerDisp, Load.lengthDisp, Form.pointerSlot, Form.lengthSlot, Form.frameBytes, Form.stackBytes, Variant.traversal, ResetLayout.reset, ResetLayout.finalizeIntoReset, ResetLayout.traitFinalizeIntoReset]; all_goals decide +kernel))
  have stack_readable {offset len : Nat} (low : offset ≤ form.stackBytes)
      (high : len ≤ offset + 8) :
      MemReadable s (stackPtr initial - BitVec.ofNat 64 offset) len := by
    have h := Dispatch.stack_sub_readable512 ctx low high
    exact ⟨h.low, fun i hi => input.allocated _ (h.mem i hi)⟩
  have pointerWord : memLoad s.external (rspOf s + (Load.pointerDisp form).value) 64 =
      initial.regValue .rdi := by
    rw [pointerAddr]
    cases form <;> first | contradiction | exact input.pointerTable
  have lengthWord : memLoad s.external (rspOf s + (Load.lengthDisp form).value) 64 =
      initial.regValue .rdx := by
    rw [lengthAddr]
    cases form <;> first | contradiction | exact input.lengthTable
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨input.rip, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · cases form with
      | slices | digest => (dsimp only [Load.pair, Load.pointerDisp, Load.lengthDisp, Form.pointerSlot, Form.lengthSlot, Form.frameBytes, Form.stackBytes, Variant.traversal, ResetLayout.reset, ResetLayout.finalizeIntoReset, ResetLayout.traitFinalizeIntoReset]; all_goals decide +kernel)
      | reset stage =>
        rcases stage with ⟨_ | _ | _ | n, h⟩ <;> try omega
        all_goals cases v <;> (dsimp only [Load.pair, Load.pointerDisp, Load.lengthDisp, Form.pointerSlot, Form.lengthSlot, Form.frameBytes, Form.stackBytes, Variant.traversal, ResetLayout.reset, ResetLayout.finalizeIntoReset, ResetLayout.traitFinalizeIntoReset]; all_goals decide +kernel)
      | finalizeIntoReset second | traitFinalizeIntoReset second =>
        cases second <;> cases v <;> (dsimp only [Load.pair, Load.pointerDisp, Load.lengthDisp, Form.pointerSlot, Form.lengthSlot, Form.frameBytes, Form.stackBytes, Variant.traversal, ResetLayout.reset, ResetLayout.finalizeIntoReset, ResetLayout.traitFinalizeIntoReset]; all_goals decide +kernel)
    · cases form <;> (dsimp only [Load.pair, Load.pointerDisp, Load.lengthDisp, Form.pointerSlot, Form.lengthSlot, Form.frameBytes, Form.stackBytes, Variant.traversal, ResetLayout.reset, ResetLayout.finalizeIntoReset, ResetLayout.traitFinalizeIntoReset]; all_goals decide +kernel)
    · cases form <;> (dsimp only [Load.pair, Load.pointerDisp, Load.lengthDisp, Form.pointerSlot, Form.lengthSlot, Form.frameBytes, Form.stackBytes, Variant.traversal, ResetLayout.reset, ResetLayout.finalizeIntoReset, ResetLayout.traitFinalizeIntoReset]; all_goals decide +kernel)
    · cases form with
      | slices | digest => (dsimp only [Load.pair, Load.pointerDisp, Load.lengthDisp, Form.pointerSlot, Form.lengthSlot, Form.frameBytes, Form.stackBytes, Variant.traversal, ResetLayout.reset, ResetLayout.finalizeIntoReset, ResetLayout.traitFinalizeIntoReset]; all_goals decide +kernel)
      | reset stage =>
        rcases stage with ⟨_ | _ | _ | n, h⟩ <;> try omega
        all_goals cases v <;> (dsimp only [Load.pair, Load.pointerDisp, Load.lengthDisp, Form.pointerSlot, Form.lengthSlot, Form.frameBytes, Form.stackBytes, Variant.traversal, ResetLayout.reset, ResetLayout.finalizeIntoReset, ResetLayout.traitFinalizeIntoReset]; all_goals decide +kernel)
      | finalizeIntoReset second | traitFinalizeIntoReset second =>
        cases second <;> cases v <;> (dsimp only [Load.pair, Load.pointerDisp, Load.lengthDisp, Form.pointerSlot, Form.lengthSlot, Form.frameBytes, Form.stackBytes, Variant.traversal, ResetLayout.reset, ResetLayout.finalizeIntoReset, ResetLayout.traitFinalizeIntoReset]; all_goals decide +kernel)
    · rw [pointerAddr]
      exact stack_readable (by cases form <;> (dsimp only [Load.pair, Load.pointerDisp, Load.lengthDisp, Form.pointerSlot, Form.lengthSlot, Form.frameBytes, Form.stackBytes, Variant.traversal, ResetLayout.reset, ResetLayout.finalizeIntoReset, ResetLayout.traitFinalizeIntoReset]; all_goals decide +kernel)) (by cases form <;> (dsimp only [Load.pair, Load.pointerDisp, Load.lengthDisp, Form.pointerSlot, Form.lengthSlot, Form.frameBytes, Form.stackBytes, Variant.traversal, ResetLayout.reset, ResetLayout.finalizeIntoReset, ResetLayout.traitFinalizeIntoReset]; all_goals decide +kernel))
    · rw [lengthAddr]
      exact stack_readable (by cases form <;> (dsimp only [Load.pair, Load.pointerDisp, Load.lengthDisp, Form.pointerSlot, Form.lengthSlot, Form.frameBytes, Form.stackBytes, Variant.traversal, ResetLayout.reset, ResetLayout.finalizeIntoReset, ResetLayout.traitFinalizeIntoReset]; all_goals decide +kernel)) (by cases form <;> (dsimp only [Load.pair, Load.pointerDisp, Load.lengthDisp, Form.pointerSlot, Form.lengthSlot, Form.frameBytes, Form.stackBytes, Variant.traversal, ResetLayout.reset, ResetLayout.finalizeIntoReset, ResetLayout.traitFinalizeIntoReset]; all_goals decide +kernel))
    · rw [pointerWord, shifted]
      exact values.1.1
    · rw [lengthWord, shifted]
      exact values.2.1
  · rw [pointerWord, shifted]
    exact values.1.2
  · rw [lengthWord, shifted]
    exact values.2.2

theorem load_pair [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Input}
    {index : Nat} {form : Form} (ctx : Context v initial inputs form)
    (nondigest : form ≠ .digest) (input : LoopState v initial s inputs index form) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ ReadyToStep t ∧
      (Sha2.Proofs.Common.SHA256.Absorb.Blocks.effect
        (v.pc (v.traversal form).head form) (Load.pair v form) s).Holds s t := by
  obtain ⟨fuel, t, run, ready, _, effect⟩ :=
    Load.pair_run (returnBoundary initial)
      (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2
      s (supportedMachine_readyToStep input.machine)
      (Load.pair_code nondigest input.loaded) (load_pair_input ctx nondigest input).1
  exact ⟨fuel, t, run, ready, effect⟩

set_option maxRecDepth 2048 in
theorem iteration_of_pair [Bindings] {v : Variant} {initial s t : RamState} {inputs : Array Input}
    {index fuel : Nat} {form : Form} (ctx : Context v initial inputs form)
    (nondigest : form ≠ .digest) (input : LoopState v initial s inputs index form)
    (run : Advances (returnBoundary initial) fuel s t) (ready : ReadyToStep t)
    (effect : (Sha2.Proofs.Common.SHA256.Absorb.Blocks.effect
      (v.pc (v.traversal form).head form) (Load.pair v form) s).Holds s t) :
    Iteration v initial t inputs index form := by
  let components : List Component := [.reg 0,
    .reg ((BitVec.ofNat 4 (v.traversal form).dataReg).setWidth 5),
    .reg ((BitVec.ofNat 4 (v.traversal form).lengthReg).setWidth 5), .rip]
  have frame : AgreesExcept components s t := effect.agrees
  have noMem : ∀ c ∈ components, ∀ a, ¬ c.Covers a := by simp [components, Component.Covers]
  have memory := frame.external noMem
  have kept4 : Component.reg 4 ∉ components := by
    cases form with
    | slices | digest => dsimp [components, Variant.traversal]; decide
    | reset stage =>
      rcases stage with ⟨_ | _ | _ | n, h⟩ <;> try omega
      all_goals cases v <;> dsimp [components, Variant.traversal, ResetLayout.reset] <;> decide
    | finalizeIntoReset second | traitFinalizeIntoReset second =>
      cases second <;> cases v <;>
        dsimp [components, Variant.traversal, ResetLayout.finalizeIntoReset,
          ResetLayout.traitFinalizeIntoReset] <;> decide
  have buffered := buffered_of_agrees ctx input.toBuffered run ready frame noMem kept4
    (by simp [components]) (fun h => (nondigest h).elim) (fun h => .inr (input.outputSaved h))
  have bufferControl : form = .reset 1 → t.regValue .rbx = bufferPointer initial form := by
    intro h
    subst form
    apply Eq.trans _ (input.bufferRegister rfl)
    cases v <;> exact frame.read (n := 64) (r := 3) (by
      dsimp [components, Variant.traversal, ResetLayout.reset]; decide)
  have memcpyControl : match form with
      | .reset stage => stage.val = 2 → t.regValue .rbx = 0x10dd60
      | .finalizeIntoReset true =>
        t.regValue (if v = .sha384 ∨ v = .sha512 then .rbx else .r12) = 0x10dd60
      | .traitFinalizeIntoReset second => t.regValue (if second then .rbp else .r13) = 0x10dd60
      | _ => True := by
    cases form with
    | slices | digest => trivial
    | reset stage =>
      intro h
      have eq : stage = 2 := Fin.ext h
      subst stage
      apply Eq.trans _ (input.memcpyTarget rfl)
      cases v <;> exact frame.read (n := 64) (r := 3) (by
        dsimp [components, Variant.traversal, ResetLayout.reset]; decide)
    | finalizeIntoReset second =>
      cases second with
      | false => trivial
      | true =>
        cases v <;> first
        | exact (frame.read (n := 64) (r := 3) (by
            dsimp [components, Variant.traversal, ResetLayout.finalizeIntoReset]; decide)).trans input.memcpyTarget
        | exact (frame.read (n := 64) (r := 12) (by
            dsimp [components, Variant.traversal, ResetLayout.finalizeIntoReset]; decide)).trans input.memcpyTarget
    | traitFinalizeIntoReset second =>
      cases second <;> cases v <;> first
      | exact (frame.read (n := 64) (r := 13) (by
          dsimp [components, Variant.traversal, ResetLayout.traitFinalizeIntoReset]; decide)).trans input.memcpyTarget
      | exact (frame.read (n := 64) (r := 5) (by
          dsimp [components, Variant.traversal, ResetLayout.traitFinalizeIntoReset]; decide)).trans input.memcpyTarget
  refine ⟨buffered, ?_, ?_, input.remaining, (fun h => by simpa only [memory] using input.outputSaved h), bufferControl, (by
      cases form with
      | finalizeIntoReset second => cases second <;> exact memcpyControl
      | _ => exact memcpyControl)⟩
  · apply Eq.trans (frame.read (n := 64) (r := BitVec.ofNat 5 (v.traversal form).indexReg) ?_) input.indexRegister
    cases form with
    | slices | digest => dsimp [components, Variant.traversal]; decide
    | reset stage =>
      rcases stage with ⟨_ | _ | _ | n, h⟩ <;> try omega
      all_goals cases v <;> dsimp [components, Variant.traversal, ResetLayout.reset] <;> decide
    | finalizeIntoReset second | traitFinalizeIntoReset second =>
      cases second <;> cases v <;>
        dsimp [components, Variant.traversal, ResetLayout.finalizeIntoReset,
          ResetLayout.traitFinalizeIntoReset] <;> decide
  · apply Eq.trans _ input.countRegister
    cases form with
    | slices | digest => exact frame.read (n := 64) (r := 15) (by dsimp [components, Variant.traversal]; decide)
    | reset stage =>
      rcases stage with ⟨_ | _ | _ | n, h⟩ <;> try omega
      all_goals cases v <;> exact frame.read (n := 64) (r := 12) (by
        dsimp [components, Variant.traversal, ResetLayout.reset]; decide)
    | finalizeIntoReset second =>
      cases second <;> cases v <;> first
      | exact frame.read (n := 64) (r := 12) (by dsimp [components, Variant.traversal, ResetLayout.finalizeIntoReset]; decide)
      | exact frame.read (n := 64) (r := 15) (by dsimp [components, Variant.traversal, ResetLayout.finalizeIntoReset]; decide)
    | traitFinalizeIntoReset second =>
      cases second <;> cases v <;>
        change memLoad t.external (stackPtr initial - 640) 64 =
          memLoad s.external (stackPtr initial - 640) 64
      all_goals rw [memory]
theorem values_of_pair [Bindings] {v : Variant} {initial s t : RamState} {inputs : Array Input}
    {index : Nat} {form : Form} (ctx : Context v initial inputs form)
    (nondigest : form ≠ .digest) (input : LoopState v initial s inputs index form)
    (effect : (Sha2.Proofs.Common.SHA256.Absorb.Blocks.effect
      (v.pc (v.traversal form).head form) (Load.pair v form) s).Holds s t) :
    v.sourceValue form t = (inputs[index]'input.remaining).address ∧
    v.lengthValue form t = BitVec.ofNat 64 (inputs[index]'input.remaining).bytes.size := by
  have values := load_pair_input ctx nondigest input
  have widths :
      (BitVec.ofNat 4 (v.traversal form).dataReg).setWidth 5 = BitVec.ofNat 5 (v.traversal form).dataReg ∧
      (BitVec.ofNat 4 (v.traversal form).lengthReg).setWidth 5 = BitVec.ofNat 5 (v.traversal form).lengthReg := by
    cases form with
    | slices | digest => exact ⟨rfl,rfl⟩
    | reset stage =>
      rcases stage with ⟨_ | _ | _ | n, h⟩ <;> try omega
      all_goals cases v <;> exact ⟨rfl,rfl⟩
    | finalizeIntoReset second | traitFinalizeIntoReset second =>
      cases second <;> cases v <;> exact ⟨rfl,rfl⟩
  have writes := effect.writes
  simp only [Sha2.Proofs.Common.SHA256.Absorb.Blocks.effect, Load.pair, Write.AllHold] at writes
  constructor
  · change (.reg (BitVec.ofNat 5 (v.traversal form).dataReg) : Operand 64).read t = _
    rw [← widths.1, writes.2.1]
    exact values.2.1
  · change (.reg (BitVec.ofNat 5 (v.traversal form).lengthReg) : Operand 64).read t = _
    rw [← widths.2, writes.2.2]
    exact values.2.2

end Sha2.Proofs.Wrapper512.Absorb

namespace Sha2.Proofs.Wrapper512.Absorb
open Sha2.Proofs.Program Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA512
open Sha2.Proofs.Wrapper

set_option maxRecDepth 2048 in
theorem load_tail [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Input}
    {index : Nat} {form : Form} (ctx : Context v initial inputs form)
    (nondigest : form ≠ .digest)
    (input : Iteration v initial s inputs index form form.activeMemory)
    (rip : s.RIP = v.pc (Load.tailOffset v form) form)
    (source : v.sourceValue form s = (inputs[index]'input.remaining).address)
    (length : v.lengthValue form s = BitVec.ofNat 64 (inputs[index]'input.remaining).bytes.size) :
    ∃ t, Loaded v initial t inputs index form ∧
      (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧
      MemoryWriteFrame s t #v[Stack.region initial (v.routine form).minStackBytes] := by
  have disp : (Load.tailDisp form).value =
      BitVec.ofNat 64 form.frameBytes - BitVec.ofNat 64 form.activeMemory.tail := by
    cases form <;> try contradiction
    all_goals dsimp [Load.tailDisp, Form.frameBytes, Form.activeMemory,
      Form.bufferedMemory, ResetLayout.resetMemory, ResetLayout.finalizeMemory,
      ResetLayout.cloneMemory] <;> decide
  have addr : rspOf s + (Load.tailDisp form).value = tailLengthPointer initial form form.activeMemory := by
    change stackPtr s + _ = _
    rw [input.rsp, disp, BitVec.sub_eq_add_neg (BitVec.ofNat 64 form.frameBytes),
      ← BitVec.add_assoc, BitVec.sub_add_cancel]
    exact (BitVec.sub_eq_add_neg _ _).symm
  have readable : MemReadable s (rspOf s + (Load.tailDisp form).value) 1 := by
    rw [addr]
    have bounds : form.activeMemory.tail ≤ form.stackBytes := by
      cases form <;> dsimp [Form.activeMemory, Form.bufferedMemory, Form.stackBytes,
        ResetLayout.resetMemory, ResetLayout.finalizeMemory, ResetLayout.cloneMemory] <;> decide
    have h := Dispatch.stack_sub_readable512 ctx bounds (show 1 ≤ form.activeMemory.tail + 8 by omega)
    exact ⟨h.low, fun i hi => input.allocated _ (h.mem i hi)⟩
  have pre : Sha2.Proofs.Common.SHA256.Absorb.Blocks.Pre
      (v.pc (Load.tailOffset v form) form) (Load.tail v form) s := by
    refine ⟨rip, ?_, ?_⟩
    · cases form <;> dsimp [Load.tailDisp] <;> decide
    · x86_norm
      exact readable
  obtain ⟨fuel, t, run, ready, _, effect⟩ := Load.tail_run (returnBoundary initial)
    (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2 s
    (supportedMachine_readyToStep input.machine) (Load.tail_code nondigest input.loaded) pre
  let components : List Component :=
    [.reg ((BitVec.ofNat 4 (v.traversal form).tailReg).setWidth 5), .rip]
  have frame : AgreesExcept components s t := effect.agrees
  have noMem : ∀ c ∈ components, ∀ a, ¬ c.Covers a := by simp [components, Component.Covers]
  have memory := frame.external noMem
  have width : (BitVec.ofNat 4 (v.traversal form).tailReg).setWidth 5 =
      BitVec.ofNat 5 (v.traversal form).tailReg := by
    cases form with
    | slices | digest => rfl
    | reset stage =>
      rcases stage with ⟨_ | _ | _ | n, h⟩ <;> try omega
      all_goals cases v <;> rfl
    | finalizeIntoReset second | traitFinalizeIntoReset second => cases second <;> cases v <;> rfl
  have pos : v.tailValue form t = BitVec.ofNat 64 ((prefixMessage inputs index).size % 128) := by
    have write := effect.writes
    x86_norm [Sha2.Proofs.Common.SHA256.Absorb.Blocks.effect, Load.tail] at write
    change ((.reg ((BitVec.ofNat 4 (v.traversal form).tailReg).setWidth 5) : Operand 64).read t =
      (memLoad s.external (rspOf s + (Load.tailDisp form).value) 8).setWidth 64) at write
    change (.reg (BitVec.ofNat 5 (v.traversal form).tailReg) : Operand 64).read t = _
    rw [← width, write, addr]
    have bytes : Bytes s.external (tailLengthPointer initial form form.activeMemory) 1
        (storedByte (BitVec.ofNat 8 ((prefixMessage inputs index).size % 128))) := by
      intro j hj
      have eq : j = 0 := by omega
      subst j
      simpa [storedByte, BitVec.toNat_ofNat, Nat.mod_eq_of_lt
        (show (prefixMessage inputs index).size % 128 < 256 by omega)] using input.tailLength
    rw [Bytes.memLoad (n := 8) bytes (by decide) (by decide)]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  have kept : ∀ r ∈ ([4, (BitVec.ofNat 5 (v.traversal form).indexReg),
      (BitVec.ofNat 5 ((v.traversal form).countReg.getD 0)),
      (BitVec.ofNat 5 (v.traversal form).dataReg),
      (BitVec.ofNat 5 (v.traversal form).lengthReg)] : List (BitVec 5)),
      Component.reg r ∉ components := by
    cases form with
    | slices | digest => dsimp [components, Variant.traversal]; decide
    | reset stage =>
      rcases stage with ⟨_ | _ | _ | n, h⟩ <;> try omega
      all_goals cases v <;> dsimp [components, Variant.traversal, ResetLayout.reset] <;> decide
    | finalizeIntoReset second | traitFinalizeIntoReset second =>
      cases second <;> cases v <;>
        dsimp [components, Variant.traversal, ResetLayout.finalizeIntoReset,
          ResetLayout.traitFinalizeIntoReset] <;> decide
  have buffered := buffered_of_agrees ctx input.toBuffered run ready frame noMem
    (kept 4 (by simp)) (by simp [components]) (fun h => (nondigest h).elim)
    (fun h => .inr (input.outputSaved h))
  have count : v.countValue form initial t = v.countValue form initial s := by
    unfold Variant.countValue
    split
    next reg hr =>
      exact frame.read (n := 64) (r := BitVec.ofNat 5 reg) (kept _ (by simp [hr]))
    next => rw [memory]
  have bufferControl : form = .reset 1 → t.regValue .rbx = bufferPointer initial form := by
    intro h
    subst form
    apply Eq.trans _ (input.bufferRegister rfl)
    cases v <;> exact frame.read (n := 64) (r := 3) (by
      dsimp [components, Variant.traversal, ResetLayout.reset]; decide)
  have memcpyControl : match form with
      | .reset stage => stage.val = 2 → t.regValue .rbx = 0x10dd60
      | .finalizeIntoReset true =>
        t.regValue (if v = .sha384 ∨ v = .sha512 then .rbx else .r12) = 0x10dd60
      | .traitFinalizeIntoReset second => t.regValue (if second then .rbp else .r13) = 0x10dd60
      | _ => True := by
    cases form with
    | slices | digest => trivial
    | reset stage =>
      intro h
      have eq : stage = 2 := Fin.ext h
      subst stage
      apply Eq.trans _ (input.memcpyTarget rfl)
      cases v <;> exact frame.read (n := 64) (r := 3) (by
        dsimp [components, Variant.traversal, ResetLayout.reset]; decide)
    | finalizeIntoReset second =>
      cases second with
      | false => trivial
      | true =>
        cases v <;> first
        | exact (frame.read (n := 64) (r := 3) (by
            dsimp [components, Variant.traversal, ResetLayout.finalizeIntoReset]; decide)).trans input.memcpyTarget
        | exact (frame.read (n := 64) (r := 12) (by
            dsimp [components, Variant.traversal, ResetLayout.finalizeIntoReset]; decide)).trans input.memcpyTarget
    | traitFinalizeIntoReset second =>
      cases second <;> cases v <;> first
      | exact (frame.read (n := 64) (r := 13) (by
          dsimp [components, Variant.traversal, ResetLayout.traitFinalizeIntoReset]; decide)).trans input.memcpyTarget
      | exact (frame.read (n := 64) (r := 5) (by
          dsimp [components, Variant.traversal, ResetLayout.traitFinalizeIntoReset]; decide)).trans input.memcpyTarget
  refine ⟨t, {
    toIteration := ⟨buffered,
    (frame.read (n := 64) (r := BitVec.ofNat 5 (v.traversal form).indexReg)
      (kept _ (by simp))).trans input.indexRegister,
    count.trans input.countRegister, input.remaining,
    (fun h => by simpa only [memory] using input.outputSaved h), bufferControl, (by
      cases form with
      | finalizeIntoReset second => cases second <;> exact memcpyControl
      | _ => exact memcpyControl)⟩
    source := (frame.read (n := 64) (r := BitVec.ofNat 5 (v.traversal form).dataReg)
      (kept _ (by simp))).trans source
    length := (frame.read (n := 64) (r := BitVec.ofNat 5 (v.traversal form).lengthReg)
      (kept _ (by simp))).trans length
    position := pos
    rip := ?_ }, ⟨fuel, run⟩, (by intro a _; rw [memory])⟩
  rw [effect.rip]
  change v.pc (Load.tailOffset v form) form + BitVec.ofNat 64
    (Sha2.Proofs.Common.SHA256.Absorb.Blocks.bytes (Load.tail v form)).length = _
  rw [Variant.pc_add v _ _ form]
  congr 1
  cases form with
  | slices => cases v <;> decide +kernel
  | digest => contradiction
  | reset stage =>
    rcases stage with ⟨_ | _ | _ | n, h⟩ <;> try omega
    all_goals cases v <;> dsimp [Load.tailOffset, Load.pair, Load.pointerDisp, Load.lengthDisp,
      Load.tail, Load.tailDisp, Variant.loadedOffset, Variant.traversal, ResetLayout.reset] <;> decide
  | finalizeIntoReset second | traitFinalizeIntoReset second =>
    cases second <;> cases v <;> decide +kernel
end Sha2.Proofs.Wrapper512.Absorb

namespace Sha2.Proofs.Wrapper512.Absorb
open Sha2.Proofs.Program Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA512
open Sha2.Proofs.Wrapper

set_option maxRecDepth 2048 in
theorem load_slice_direct [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Input}
    {index : Nat} {form : Form} (ctx : Context v initial inputs form)
    (input : LoopState v initial s inputs index form)
    (nondigest : form ≠ .digest := by simp)
    (nontrait : ∀ second, form ≠ .traitFinalizeIntoReset second := by simp) :
    ∃ t, Loaded v initial t inputs index form ∧
      (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧
      MemoryWriteFrame s t #v[Stack.region initial (v.routine form).minStackBytes] := by
  obtain ⟨fuel, t, run, ready, effect⟩ := load_pair ctx nondigest input
  have iter := iteration_of_pair ctx nondigest input run ready effect
  have values := values_of_pair ctx nondigest input effect
  have memory : form.activeMemory = form.bufferedMemory := by
    cases form with
    | traitFinalizeIntoReset second => exact (nontrait second rfl).elim
    | _ => rfl
  have tailResult : ∃ u, Loaded v initial u inputs index form ∧
      (∃ n, Advances (returnBoundary initial) n t u) ∧
      MemoryWriteFrame t u #v[Stack.region initial (v.routine form).minStackBytes] := by
    apply load_tail ctx nondigest (by simpa only [memory] using iter)
    · rw [effect.rip]
      change v.pc (v.traversal form).head form + BitVec.ofNat 64
        (Sha2.Proofs.Common.SHA256.Absorb.Blocks.bytes (Load.pair v form)).length = _
      rw [Variant.pc_add v _ _ form]
      congr 1
      cases form with
      | traitFinalizeIntoReset second => exact (nontrait second rfl).elim
      | _ => rfl
    · exact values.1
    · exact values.2
  obtain ⟨u, loaded, ⟨n, runTail⟩, frameTail⟩ := tailResult
  have same : t.external = s.external := effect.agrees.external (by
    simp [Common.SHA256.Absorb.Blocks.effect, Load.pair, Effect.components, Component.Covers])
  exact ⟨u, loaded, ⟨fuel + n, run.trans runTail⟩,
    memoryWriteFrame_trans (by intro a _; rw [same]) frameTail⟩
end Sha2.Proofs.Wrapper512.Absorb

namespace Sha2.Proofs.Wrapper512.Absorb
open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.Field

theorem clone_copy [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Input}
    {second : Bool} (ctx : Context v initial inputs (.traitFinalizeIntoReset second))
    (input : State v initial s (.traitFinalizeIntoReset second))
    (rip : s.RIP = (Load.cloneCallSite v second).pc)
    (target : s.regValue (if second then .rbp else .r13) = 0x10dd60)
    (destination : s.regValue .rdi = stackPtr initial - 616)
    (source : s.regValue .rsi = stackPtr initial - 392)
    (length : s.regValue .rdx = 208) :
    ∃ t, Finish.Copy.StackResult v initial s t 208 392 616
      (v.pc (Load.tailOffset v (.traitFinalizeIntoReset second)) (.traitFinalizeIntoReset second))
      (.traitFinalizeIntoReset second) := by
  obtain ⟨u, stateU, effect, rspU, returnU, callRun⟩ := Load.clone_call ctx input rip target
  have push : pushAddr s = stackPtr initial - 656 := by
    rw [pushAddr, input.rsp, BitVec.sub_sub]
    rfl
  have frame : AgreesExcept [.reg 4, .mem (stackPtr initial - 656) 8, .rip] s u := by
    simpa only [callEffect, pushEffect_components, push] using effect.agrees
  let layout : Wrapper.StackCallLayout 1200 208 208 0 :=
    ⟨656, 392, 616, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide⟩
  have returned : InProgram (returnBoundary u).rip := by
    rw [returnU]
    apply inProgram_of_textOffset
    cases second <;> cases v <;> decide +kernel
  exact Finish.Copy.copy_at ctx input stateU layout rfl (by change 208 + 48 ≤ 616; decide) (by change 616 ≤ 648; decide) (by decide)
    (by change OffsetsApart (-656) 8 (-392) 208; unfold OffsetsApart; decide +kernel) frame effect.rip rspU returnU returned destination source length ⟨1, callRun⟩
end Sha2.Proofs.Wrapper512.Absorb

namespace Sha2.Proofs.Wrapper512.Absorb
open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.Field

theorem clone_setup [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Input}
    {index : Nat} {second : Bool} (ctx : Context v initial inputs (.traitFinalizeIntoReset second))
    (input : Iteration v initial s inputs index (.traitFinalizeIntoReset second))
    (rip : s.RIP = v.pc ((v.traversal (.traitFinalizeIntoReset second)).head + 18)
      (.traitFinalizeIntoReset second))
    (target : s.regValue (if second then .rbp else .r13) = 0x10dd60)
    (destination : s.regValue .rbx = stackPtr initial - 616)
    (source : s.regValue (if second then .r14 else .r12) = stackPtr initial - 392) :
    ∃ t, Iteration v initial t inputs index (.traitFinalizeIntoReset second) ∧
      t.RIP = (Load.cloneCallSite v second).pc ∧
      t.regValue (if second then .rbp else .r13) = 0x10dd60 ∧
      t.regValue .rdi = stackPtr initial - 616 ∧
      t.regValue .rsi = stackPtr initial - 392 ∧ t.regValue .rdx = 208 ∧
      v.sourceValue (.traitFinalizeIntoReset second) t = v.sourceValue (.traitFinalizeIntoReset second) s ∧
      v.lengthValue (.traitFinalizeIntoReset second) t = v.lengthValue (.traitFinalizeIntoReset second) s ∧
      (∃ n, Advances (returnBoundary initial) n s t) ∧ t.external = s.external := by
  obtain ⟨fuel, t, run, ready, _, effect⟩ := Load.clone_setup_run (returnBoundary initial)
    (v.pc ((v.traversal (.traitFinalizeIntoReset second)).head + 18) (.traitFinalizeIntoReset second))
    second (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2
    (by apply blockInProgram_of_textOffset; cases second <;> cases v <;> decide +kernel)
    s (supportedMachine_readyToStep input.machine) (Load.clone_setup_code input.loaded) rip
  have frame : AgreesExcept [.reg 2, .reg 7, .reg 6, .rip] s t := effect.agrees
  have memory := frame.external (by simp [Component.Covers])
  have buffered := buffered_of_agrees ctx input.toBuffered run ready frame
    (by simp [Component.Covers]) (by simp) (by simp) (by simp)
    (fun h => .inr (input.outputSaved h))
  have iter : Iteration v initial t inputs index (.traitFinalizeIntoReset second) := by
    refine ⟨buffered, ?_, ?_, input.remaining, (fun h => by simpa only [memory] using input.outputSaved h), (by intro h; cases h), ?_⟩
    · apply Eq.trans _ input.indexRegister
      cases second <;> cases v <;> exact frame.read (n := 64) (r := 15) (by simp)
    · apply Eq.trans _ input.countRegister
      cases second <;> cases v <;>
        change memLoad t.external (stackPtr initial - 640) 64 = memLoad s.external (stackPtr initial - 640) 64
      all_goals rw [memory]
    · cases second
      · exact (frame.read (n := 64) (r := 13) (by simp)).trans input.memcpyTarget
      · exact (frame.read (n := 64) (r := 5) (by simp)).trans input.memcpyTarget
  have writes := effect.writes
  x86_norm [Load.cloneSetupEffect, Write.AllHold] at writes
  change t.regValue .rdx = 208 ∧ t.regValue .rdi = s.regValue .rbx ∧
    t.regValue .rsi = s.regValue (if second then .r14 else .r12) at writes
  refine ⟨t, iter, ?_, ?_, writes.2.1.trans destination, writes.2.2.trans source, writes.1, ?_, ?_, ⟨fuel, run⟩, memory⟩
  · rw [effect.rip]
    change v.pc ((v.traversal (.traitFinalizeIntoReset second)).head + 18) (.traitFinalizeIntoReset second) + BitVec.ofNat 64 11 = _
    rw [Variant.pc_add v _ 11 (.traitFinalizeIntoReset second)]
    simp only [Load.cloneCallSite, Nat.add_assoc]
  · apply Eq.trans _ target
    cases second
    · exact frame.read (n := 64) (r := 13) (by simp)
    · exact frame.read (n := 64) (r := 5) (by simp)
  · cases second <;> cases v
    all_goals first
    | exact frame.read (n := 64) (r := 5) (by simp)
    | exact frame.read (n := 64) (r := 13) (by simp)
  · cases second <;> cases v
    all_goals first
    | exact frame.read (n := 64) (r := 14) (by simp)
    | exact frame.read (n := 64) (r := 12) (by simp)
end Sha2.Proofs.Wrapper512.Absorb

namespace Sha2.Proofs.Wrapper512.Absorb
open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.Field

set_option maxRecDepth 2048 in
theorem load_slice_trait [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Input}
    {index : Nat} {second : Bool} (ctx : Context v initial inputs (.traitFinalizeIntoReset second))
    (input : LoopState v initial s inputs index (.traitFinalizeIntoReset second)) :
    ∃ t, Loaded v initial t inputs index (.traitFinalizeIntoReset second) ∧
      (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧
      MemoryWriteFrame s t #v[Stack.region initial (v.routine (.traitFinalizeIntoReset second)).minStackBytes] := by
  obtain ⟨fuel, t, run, ready, effect⟩ := load_pair ctx (by simp) input
  have iter := iteration_of_pair ctx (by simp) input run ready effect
  have values := values_of_pair ctx (by simp) input effect
  have frame : AgreesExcept [.reg 0,
    .reg ((BitVec.ofNat 4 (v.traversal (.traitFinalizeIntoReset second)).dataReg).setWidth 5),
    .reg ((BitVec.ofNat 4 (v.traversal (.traitFinalizeIntoReset second)).lengthReg).setWidth 5), .rip] s t := effect.agrees
  have rip : t.RIP = v.pc ((v.traversal (.traitFinalizeIntoReset second)).head + 18)
      (.traitFinalizeIntoReset second) := by
    rw [effect.rip]
    change v.pc (v.traversal (.traitFinalizeIntoReset second)).head (.traitFinalizeIntoReset second) +
      BitVec.ofNat 64 (Common.SHA256.Absorb.Blocks.bytes (Load.pair v (.traitFinalizeIntoReset second))).length = _
    rw [Variant.pc_add v _ _ (.traitFinalizeIntoReset second)]
    congr 1 <;> (cases second <;> cases v <;> rfl)
  have target : t.regValue (if second then .rbp else .r13) = 0x10dd60 := by
    apply Eq.trans _ input.memcpyTarget
    cases second <;> cases v
    all_goals first
    | exact frame.read (n := 64) (r := 13) (by decide)
    | exact frame.read (n := 64) (r := 5) (by decide)
  have dest : t.regValue .rbx = stackPtr initial - 616 := by
    apply Eq.trans _ (input.cloneRegisters second rfl).1
    cases second <;> cases v <;> exact frame.read (n := 64) (r := 3) (by decide)
  have src : t.regValue (if second then .r14 else .r12) = stackPtr initial - 392 := by
    apply Eq.trans _ (input.cloneRegisters second rfl).2
    cases second <;> cases v
    all_goals first
    | exact frame.read (n := 64) (r := 12) (by decide)
    | exact frame.read (n := 64) (r := 14) (by decide)
  obtain ⟨u, iterU, ripU, targetU, destU, srcU, lenU, sourceU, lengthU, ⟨setupFuel, setupRun⟩, setupMemory⟩ :=
    clone_setup ctx iter rip target dest src
  obtain ⟨w, copied⟩ := clone_copy ctx iterU.toState ripU targetU destU srcU lenU
  have buffered := copied.buffered (sourceMemory := (Form.traitFinalizeIntoReset second).bufferedMemory)
    (destinationMemory := (Form.traitFinalizeIntoReset second).activeMemory)
    rfl rfl (by decide) (by decide) iterU.toBuffered
    (copied.preserved_trait ctx iterU.toPreserved (Or.inr rfl))
  have word (offset : Nat) (ho : offset = 408 ∨ offset = 640) :
      memLoad w.external (stackPtr initial - BitVec.ofNat 64 offset) 64 =
        memLoad u.external (stackPtr initial - BitVec.ofNat 64 offset) 64 := by
    apply memLoad_congr
    intro j hj
    apply congrArg (fun b : Option UInt8 => b.getD 0)
    apply copied.kept_bytes ctx (by change 616 ≤ 648; decide) (by decide) ?_ ?_ ?_ j hj
    all_goals rcases ho with rfl | rfl <;> dsimp [Form.frameBytes] <;> decide
  have iterW : Iteration v initial w inputs index (.traitFinalizeIntoReset second)
      (Form.traitFinalizeIntoReset second).activeMemory := by
    refine ⟨buffered, ?_, ?_, input.remaining, ?_, (by intro h; cases h), ?_⟩
    · apply Eq.trans _ iterU.indexRegister
      cases second <;> cases v <;> exact copied.abi.1 .r15 (by simp)
    · apply Eq.trans _ iterU.countRegister
      cases second <;> cases v <;> exact word 640 (Or.inr rfl)
    · intro h
      have eq : second = false := Form.traitFinalizeIntoReset.inj h
      subst second
      exact (word 408 (Or.inl rfl)).trans (iterU.outputSaved rfl)
    · cases second
      · exact (copied.abi.1 .r13 (by simp)).trans iterU.memcpyTarget
      · exact (copied.abi.1 .rbp (by simp)).trans iterU.memcpyTarget
  have tailResult : ∃ z, Loaded v initial z inputs index (.traitFinalizeIntoReset second) ∧
      (∃ n, Advances (returnBoundary initial) n w z) ∧
      MemoryWriteFrame w z #v[Stack.region initial (v.routine (.traitFinalizeIntoReset second)).minStackBytes] := by
    apply load_tail ctx (by simp) iterW copied.rip
    · apply Eq.trans _ (sourceU.trans values.1)
      cases second <;> cases v
      all_goals first
      | exact copied.abi.1 .rbp (by simp)
      | exact copied.abi.1 .r13 (by simp)
    · apply Eq.trans _ (lengthU.trans values.2)
      cases second <;> cases v
      all_goals first
      | exact copied.abi.1 .r14 (by simp)
      | exact copied.abi.1 .r12 (by simp)
  obtain ⟨z, loaded, ⟨tailFuel, tailRun⟩, tailFrame⟩ := tailResult
  obtain ⟨copyFuel, copyRun⟩ := copied.execution
  have pairMemory : t.external = s.external := frame.external (by simp [Component.Covers])
  exact ⟨z, loaded, ⟨fuel + setupFuel + copyFuel + tailFuel,
    ((run.trans setupRun).trans copyRun).trans tailRun⟩,
    memoryWriteFrame_trans (by intro a _; rw [pairMemory])
      (memoryWriteFrame_trans (by intro a _; rw [setupMemory])
        (memoryWriteFrame_trans copied.stackFrame tailFrame))⟩
theorem load_slice [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Input}
    {index : Nat} {form : Form} (ctx : Context v initial inputs form)
    (input : LoopState v initial s inputs index form) (nondigest : form ≠ .digest := by simp) :
    ∃ t, Loaded v initial t inputs index form ∧
      (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧
      MemoryWriteFrame s t #v[Stack.region initial (v.routine form).minStackBytes] := by
  cases form with
  | digest => contradiction
  | traitFinalizeIntoReset second => exact load_slice_trait ctx input
  | slices | reset _ | finalizeIntoReset _ => exact load_slice_direct ctx input (by simp) (by simp)
end Sha2.Proofs.Wrapper512.Absorb
