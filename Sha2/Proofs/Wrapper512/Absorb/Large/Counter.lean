import Sha2.Proofs.Common.Instructions.MemoryAlu.Add
import Sha2.Proofs.Common.Machine.MemoryFrame
import Sha2.Proofs.Wrapper512.Absorb.Large.Counter.Effect
import Sha2.Proofs.Wrapper512.Absorb.Memory
import Sha2.Proofs.Wrapper512.Machine.Stages.Stack

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Absorb.Large.Counter

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.Instructions.MemoryAlu

def addLength (register : Bool) : Nat := if register then 8 else 9

def addOffset (register : Bool) (v : Variant := .sha384) (form : Form := .slices) : Nat :=
  if register then (v.traversal form).blocksCall - 28
  else (v.traversal form).fillCall - (match form with
    | .reset _ => 34
    | .finalizeIntoReset _ => 36
    | _ => 39)

def carryOffset (register : Bool) (v : Variant := .sha384) (form : Form := .slices) : Nat :=
  addOffset register v form + addLength register

def endOffset (register : Bool) (v : Variant := .sha384) (form : Form := .slices) : Nat :=
  carryOffset register v form + 9

def displacement (form : Form) (high : Bool) : Nat :=
  form.frameBytes - (if high then form.activeMemory.countHigh else form.activeMemory.countLow)

def addressMode (form : Form) (high : Bool) : AddrMode :=
  .sib 4 none 0 (.d32 (BitVec.ofNat 32 (displacement form high)))

set_option maxRecDepth 2048 in
theorem addressMode_addr (form : Form) (high : Bool) (s : RamState) (pc : BitVec 64) :
    (addressMode form high).addr s pc = rspOf s + BitVec.ofNat 64 (displacement form high) := by
  cases form <;> cases high <;> rfl

theorem addressMode_tail_length (form : Form) (high : Bool) :
    (addressMode form high).tail.length = 5 := rfl

def addValue (register : Bool) (s : RamState) : BitVec 64 :=
  if register then s.regValue .rdx else 1

def addCode (register : Bool) (form : Form := .slices) : List UInt8 :=
  if register then 0x48 :: 0x01 :: (addressMode form false).modrm 2 :: (addressMode form false).tail
  else 0x48 :: 0x83 :: (addressMode form false).modrm 0 :: ((addressMode form false).tail ++ [1])

theorem addCode_length (register : Bool) (form : Form) :
    (addCode register form).length = addLength register := by
  cases register <;> rfl

def carryCode (form : Form) : List UInt8 :=
  0x48 :: 0x83 :: (addressMode form true).modrm 2 :: ((addressMode form true).tail ++ [0])

def addEffect (v : Variant) (register : Bool) (s : RamState) (form : Form := .slices) : Effect :=
  let out := addSpec (memLoad s.external (rspOf s + BitVec.ofNat 64 (displacement form false)) 64) (addValue register s)
  { rip := v.pc (carryOffset register v form) form
    writes := [⟨(Operand.mem (rspOf s + BitVec.ofNat 64 (displacement form false)) : Operand 64), out.1⟩]
    flags := some (.ofStatusFlags out.2) }

set_option maxRecDepth 2048 in
theorem add_step [Bindings] (v : Variant) (register : Bool) (form : Form := .slices) :
    StepEffect (StorePre (v.pc (addOffset register v form) form) (addLength register)
      (fun s => rspOf s + BitVec.ofNat 64 (displacement form false)) 8)
      (codeRange (v.pc (addOffset register v form) form) (addCode register form))
      (fun s => addEffect v register s form) := by
  cases register
  · have eq : addM64Imm8Effect (v.pc (addOffset false v form) form) 9 (addressMode form false) 1 =
        (fun s => addEffect v false s form) := by
      funext s
      simp only [addM64Imm8Effect, addEffect, addValue, Bool.false_eq_true, ↓reduceIte]
      rw [Variant.pc_add (form := form)]
      cases form <;> rfl
    rw [← eq]
    simpa only [RmwPre, addressMode_tail_length, addressMode_addr, addCode, addLength, Bool.false_eq_true, ↓reduceIte, Nat.reduceAdd, UInt8.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, show gprNumber 0#1 (rexR 72#8) 2#3 = 2#5 from rfl] using add_m64_imm8_effect_step (v.pc (addOffset false v form) form) 0x48 (by simp [RexWPrefix])
      (addressMode form false) (by cases form <;> simp only [addressMode, displacement, Form.activeMemory, Form.bufferedMemory, Form.frameBytes] <;> decide +kernel) rfl rfl 1
  · have eq : addM64R64Effect (v.pc (addOffset true v form) form) 8 2 (addressMode form false) =
        (fun s => addEffect v true s form) := by
      funext s
      simp only [addM64R64Effect, addEffect, addValue, ↓reduceIte]
      rw [Variant.pc_add (form := form)]
      cases form <;> rfl
    rw [← eq]
    simpa only [RmwPre, addressMode_tail_length, addressMode_addr, addCode, addLength, Bool.false_eq_true, ↓reduceIte, Nat.reduceAdd, UInt8.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, show gprNumber 0#1 (rexR 72#8) 2#3 = 2#5 from rfl] using Sha2.Proofs.Common.Instructions.MemoryAlu.add_m64_r64_effect_step (v.pc (addOffset true v form) form) 0x48 (by simp [RexWPrefix]) 2
      (addressMode form false) (by cases form <;> simp only [addressMode, displacement, Form.activeMemory, Form.bufferedMemory, Form.frameBytes] <;> decide +kernel) rfl rfl

def carryEffect (v : Variant) (register : Bool) (s : RamState) (form : Form := .slices) : Effect :=
  let out := addSpec (memLoad s.external (rspOf s + BitVec.ofNat 64 (displacement form true)) 64)
    (BitVec.ofNat 64 (s.RFLAGS.getLsbD 0).toNat)
  { rip := v.pc (endOffset register v form) form
    writes := [⟨(Operand.mem (rspOf s + BitVec.ofNat 64 (displacement form true)) : Operand 64), out.1⟩]
    flags := some (.ofStatusFlags out.2) }

set_option maxRecDepth 2048 in
theorem carry_step [Bindings] (v : Variant) (register : Bool) (form : Form := .slices) :
    StepEffect (StorePre (v.pc (carryOffset register v form) form) 9
      (fun s => rspOf s + BitVec.ofNat 64 (displacement form true)) 8)
      (codeRange (v.pc (carryOffset register v form) form) (carryCode form))
      (fun s => carryEffect v register s form) := by
  have eq : adcM64Imm8Effect (v.pc (carryOffset register v form) form) 9 (addressMode form true) =
      (fun s => carryEffect v register s form) := by
    funext s
    simp only [adcM64Imm8Effect, carryEffect]
    rw [Variant.pc_add (form := form)]
    cases form <;> rfl
  rw [← eq]
  simpa only [RmwPre, addressMode_tail_length, addressMode_addr, carryCode, Nat.reduceAdd] using adc_m64_imm8_effect_step (v.pc (carryOffset register v form) form) 0x48
    (by simp [RexWPrefix]) (addressMode form true) (by cases form <;> simp only [addressMode, displacement, Form.activeMemory, Form.bufferedMemory, Form.frameBytes] <;> decide +kernel) rfl rfl

theorem counter_local {initial : RamState} (form : Form) (high : Bool) :
    LocalWrites initial [.mem (stackPtr initial - BitVec.ofNat 64
      (if high then form.activeMemory.countHigh else form.activeMemory.countLow)) 8, .flags, .rip] form := by
  have facts : ∀ (f : Form) (h : Bool),
      let offset := if h then f.activeMemory.countHigh else f.activeMemory.countLow
      offset ≤ f.stackBytes ∧ 56 ≤ offset ∧
      (match f with
      | .slices | .digest => 8 + 624 ≤ offset ∨ offset ≤ 600
      | _ => ∀ slot ∈ f.metadataSlots, OffsetsApart (-(BitVec.ofNat 64 offset)) 8 (-(BitVec.ofNat 64 slot)) 8) := by
    intro f h
    cases f <;> cases h <;> simp only [OffsetsApart, Form.metadataSlots, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] <;> decide +revert +kernel
  intro c hc a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · have hl := local_memory (facts form high).1 (facts form high).2.1 (by have hf := (facts form high).2.2; cases form <;> exact hf) a ha
    cases form <;> exact hl
  · exact ha.elim
  · exact ha.elim

theorem slot_facts (form : Form) :
    form.activeMemory.countLow ≤ form.stackBytes ∧ form.activeMemory.countLow % 8 = 0 ∧
    form.activeMemory.countHigh ≤ form.stackBytes ∧ form.activeMemory.countHigh % 8 = 0 ∧
    8 ≤ form.activeMemory.countLow ∧ 8 ≤ form.activeMemory.countHigh ∧
    OffsetsApart (-(BitVec.ofNat 64 form.activeMemory.countLow)) 8 (-(BitVec.ofNat 64 form.activeMemory.countHigh)) 8 ∧
    OffsetsApart (-(BitVec.ofNat 64 form.activeMemory.countHigh)) 8 (-(BitVec.ofNat 64 form.activeMemory.countLow)) 8 := by
  cases form <;> simp only [OffsetsApart] <;> decide +revert +kernel

theorem code_facts (v : Variant) (form : Form) (register : Bool) (nonDigest : form ≠ .digest) :
    v.textOffset form + addOffset register v form + addLength register ≤ 71757 ∧
    v.textOffset form + carryOffset register v form + 9 ≤ 71757 ∧
    Extracted.textBytes.toListFrom (v.textOffset form + addOffset register v form) (addCode register form).length = addCode register form ∧
    Extracted.textBytes.toListFrom (v.textOffset form + carryOffset register v form) (carryCode form).length = carryCode form ∧
    v.textOffset form + carryOffset register v form < 71757 ∧
    v.textOffset form + endOffset register v form < 71757 := by
  cases form <;> cases v <;> cases register <;> first | exact False.elim (nonDigest rfl) | decide +revert +kernel

set_option maxRecDepth 2048 in
theorem run [Bindings] {v : Variant} {form : Form} {initial s : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs form) (input : Preserved v initial s form) (register : Bool)
    (rip : s.RIP = v.pc (addOffset register v form) form)
    (nonDigest : form ≠ .digest := by decide) :
    ∃ t, Preserved v initial t form ∧ t.RIP = v.pc (endOffset register v form) form ∧
      memLoad t.external (stackPtr initial - BitVec.ofNat 64 form.activeMemory.countLow) 64 =
        memLoad s.external (stackPtr initial - BitVec.ofNat 64 form.activeMemory.countLow) 64 + addValue register s ∧
      memLoad t.external (stackPtr initial - BitVec.ofNat 64 form.activeMemory.countHigh) 64 =
        memLoad s.external (stackPtr initial - BitVec.ofNat 64 form.activeMemory.countHigh) 64 +
          BitVec.ofNat 64 ((addSpec (memLoad s.external (stackPtr initial - BitVec.ofNat 64 form.activeMemory.countLow) 64)
            (addValue register s)).2.CF).toNat ∧
      AgreesExcept [.mem (stackPtr initial - BitVec.ofNat 64 form.activeMemory.countLow) 8, .mem (stackPtr initial - BitVec.ofNat 64 form.activeMemory.countHigh) 8,
        .flags, .rip] s t ∧
      (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧
      MemoryWriteFrame s t #v[Stack.region initial (v.routine form).minStackBytes] := by
  have addressLow : rspOf s + BitVec.ofNat 64 (displacement form false) = stackPtr initial - BitVec.ofNat 64 form.activeMemory.countLow := by
    change stackPtr s + BitVec.ofNat 64 (displacement form false) = _
    rw [input.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    cases form <;> rfl
  have writableLow : MemWritable s (rspOf s + BitVec.ofNat 64 (displacement form false)) 8 := by
    rw [addressLow]
    exact Machine.Stages.stack_slot_writable ctx input.toState (by exact (slot_facts form).1) (by exact (slot_facts form).2.1)
  have apartLow : RangeApart (rspOf s + BitVec.ofNat 64 (displacement form false)) 8 (v.pc (addOffset register v form) form)
      (addLength register) := by
    rw [addressLow]
    exact Machine.Stages.stack_slot_codeApart ctx
      (codeOffset := v.textOffset form + addOffset register v form)
      (by exact (slot_facts form).1) (by exact (slot_facts form).2.2.2.2.1) (by exact (code_facts v form register nonDigest).1)
  have codeLow : CodeIn (codeRange (v.pc (addOffset register v form) form) (addCode register form)) s := by
    exact programText_slice (programLoaded_codeIn input.loaded)
      (v.textOffset form + addOffset register v form) _ (by simpa only [addCode_length] using (code_facts v form register nonDigest).1)
      (by exact (code_facts v form register nonDigest).2.2.1)
  have nextLow : (addEffect v register s form).rip ≠ (returnBoundary initial).rip :=
    boundary_ne_program ((valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2)
      (by
        apply inProgram_of_textOffset
        exact (by exact (code_facts v form register nonDigest).2.2.2.2.1 : v.textOffset form + carryOffset register v form < 71757))
  obtain ⟨u, runLow, readyLow, effectLow⟩ := (add_step v register form).advances
    (supportedMachine_readyToStep input.machine) codeLow ⟨rip, writableLow, apartLow⟩ nextLow
  have frameLow : AgreesExcept [.mem (stackPtr initial - BitVec.ofNat 64 form.activeMemory.countLow) 8, .flags, .rip] s u := by
    have h := effectLow.agrees
    simp only [addEffect, Effect.components, List.map_cons, List.map_nil, Write.component_mem,
      List.cons_append, List.nil_append, Nat.reduceDiv] at h
    rwa [addressLow] at h
  have preservedLow := preserved_of_agrees ctx input runLow readyLow frameLow
    (counter_local form false) (by simp)
  have valueLow : memLoad u.external (stackPtr initial - BitVec.ofNat 64 form.activeMemory.countLow) 64 =
      memLoad s.external (stackPtr initial - BitVec.ofNat 64 form.activeMemory.countLow) 64 + addValue register s := by
    have h := effectLow.writes
    change memLoad u.external (rspOf s + BitVec.ofNat 64 (displacement form false)) 64 =
      memLoad s.external (rspOf s + BitVec.ofNat 64 (displacement form false)) 64 + addValue register s at h
    rwa [addressLow] at h
  have carry : u.RFLAGS.getLsbD 0 =
      (addSpec (memLoad s.external (stackPtr initial - BitVec.ofNat 64 form.activeMemory.countLow) 64) (addValue register s)).2.CF := by
    have h := effectLow.flags.1
    change u.RFLAGS.getLsbD 0 =
      (addSpec (memLoad s.external (rspOf s + BitVec.ofNat 64 (displacement form false)) 64) (addValue register s)).2.CF at h
    rwa [addressLow] at h
  have unchangedHigh : memLoad u.external (stackPtr initial - BitVec.ofNat 64 form.activeMemory.countHigh) 64 =
      memLoad s.external (stackPtr initial - BitVec.ofNat 64 form.activeMemory.countHigh) 64 := by
    apply memLoad_congr
    intro i hi
    exact congrArg (fun value : Option UInt8 => value.getD 0)
      (bytes_of_mem_frame frameLow (by simp [Component.Covers])
        (by exact (slot_facts form).2.2.2.2.2.2.1) (by decide) i hi)
  have addressHigh : rspOf u + BitVec.ofNat 64 (displacement form true) = stackPtr initial - BitVec.ofNat 64 form.activeMemory.countHigh := by
    change stackPtr u + BitVec.ofNat 64 (displacement form true) = _
    rw [preservedLow.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    cases form <;> rfl
  have writableHigh : MemWritable u (rspOf u + BitVec.ofNat 64 (displacement form true)) 8 := by
    rw [addressHigh]
    exact Machine.Stages.stack_slot_writable ctx preservedLow.toState
      (by exact (slot_facts form).2.2.1) (by exact (slot_facts form).2.2.2.1)
  have apartHigh : RangeApart (rspOf u + BitVec.ofNat 64 (displacement form true)) 8 (v.pc (carryOffset register v form) form) 9 := by
    rw [addressHigh]
    exact Machine.Stages.stack_slot_codeApart ctx
      (codeOffset := v.textOffset form + carryOffset register v form)
      (by exact (slot_facts form).2.2.1) (by exact (slot_facts form).2.2.2.2.2.1) (by exact (code_facts v form register nonDigest).2.1)
  have codeHigh : CodeIn (codeRange (v.pc (carryOffset register v form) form)
      (carryCode form)) u := by
    exact programText_slice (programLoaded_codeIn preservedLow.loaded)
      (v.textOffset form + carryOffset register v form) _ (by exact (code_facts v form register nonDigest).2.1)
      (by exact (code_facts v form register nonDigest).2.2.2.1)
  have nextHigh : (carryEffect v register u form).rip ≠ (returnBoundary initial).rip :=
    boundary_ne_program ((valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2)
      (by
        apply inProgram_of_textOffset
        exact (by exact (code_facts v form register nonDigest).2.2.2.2.2 : v.textOffset form + endOffset register v form < 71757))
  obtain ⟨t, runHigh, readyHigh, effectHigh⟩ := (carry_step v register form).advances readyLow codeHigh
    ⟨effectLow.rip, writableHigh, apartHigh⟩ nextHigh
  have frameHigh : AgreesExcept [.mem (stackPtr initial - BitVec.ofNat 64 form.activeMemory.countHigh) 8, .flags, .rip] u t := by
    have h := effectHigh.agrees
    simp only [carryEffect, Effect.components, List.map_cons, List.map_nil, Write.component_mem,
      List.cons_append, List.nil_append, Nat.reduceDiv] at h
    rwa [addressHigh] at h
  refine ⟨t, preserved_of_agrees ctx preservedLow runHigh readyHigh frameHigh
    (counter_local form true) (by simp), effectHigh.rip, ?_, ?_, ?_,
    ⟨_, runLow.trans runHigh⟩, memoryWriteFrame_trans
      (frameLow.memoryWriteFrame ((counter_local form false).stack ctx))
      (frameHigh.memoryWriteFrame ((counter_local form true).stack ctx))⟩
  · rw [← valueLow]
    apply memLoad_congr
    intro i hi
    exact congrArg (fun value : Option UInt8 => value.getD 0)
      (bytes_of_mem_frame frameHigh (by simp [Component.Covers])
        (by exact (slot_facts form).2.2.2.2.2.2.2) (by decide) i hi)
  · have h := effectHigh.writes
    change memLoad t.external (rspOf u + BitVec.ofNat 64 (displacement form true)) 64 =
      memLoad u.external (rspOf u + BitVec.ofNat 64 (displacement form true)) 64 + BitVec.ofNat 64 (u.RFLAGS.getLsbD 0).toNat at h
    simpa only [addressHigh, unchangedHigh, carry] using h
  · exact (frameLow.trans frameHigh).mono (by simp)

theorem increment [Bindings] {v : Variant} {form : Form} {initial s : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs form) (input : Preserved v initial s form) (rip : s.RIP = v.pc (addOffset false v form) form)
    (nonDigest : form ≠ .digest := by decide) :
    ∃ t, Preserved v initial t form ∧ t.RIP = v.pc (endOffset false v form) form ∧
      memLoad t.external (stackPtr initial - BitVec.ofNat 64 form.activeMemory.countLow) 64 =
        memLoad s.external (stackPtr initial - BitVec.ofNat 64 form.activeMemory.countLow) 64 + 1 ∧
      memLoad t.external (stackPtr initial - BitVec.ofNat 64 form.activeMemory.countHigh) 64 =
        memLoad s.external (stackPtr initial - BitVec.ofNat 64 form.activeMemory.countHigh) 64 +
          BitVec.ofNat 64 ((addSpec (memLoad s.external (stackPtr initial - BitVec.ofNat 64 form.activeMemory.countLow) 64) 1).2.CF).toNat ∧
      AgreesExcept [.mem (stackPtr initial - BitVec.ofNat 64 form.activeMemory.countLow) 8, .mem (stackPtr initial - BitVec.ofNat 64 form.activeMemory.countHigh) 8,
        .flags, .rip] s t ∧
      (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧
      MemoryWriteFrame s t #v[Stack.region initial (v.routine form).minStackBytes] :=
  run ctx input false rip nonDigest

theorem add_count [Bindings] {v : Variant} {form : Form} {initial s : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs form) (input : Preserved v initial s form) (rip : s.RIP = v.pc (addOffset true v form) form)
    (nonDigest : form ≠ .digest := by decide) :
    ∃ t, Preserved v initial t form ∧ t.RIP = v.pc (endOffset true v form) form ∧
      memLoad t.external (stackPtr initial - BitVec.ofNat 64 form.activeMemory.countLow) 64 =
        memLoad s.external (stackPtr initial - BitVec.ofNat 64 form.activeMemory.countLow) 64 + s.regValue .rdx ∧
      memLoad t.external (stackPtr initial - BitVec.ofNat 64 form.activeMemory.countHigh) 64 =
        memLoad s.external (stackPtr initial - BitVec.ofNat 64 form.activeMemory.countHigh) 64 +
          BitVec.ofNat 64 ((addSpec (memLoad s.external (stackPtr initial - BitVec.ofNat 64 form.activeMemory.countLow) 64)
            (s.regValue .rdx)).2.CF).toNat ∧
      AgreesExcept [.mem (stackPtr initial - BitVec.ofNat 64 form.activeMemory.countLow) 8, .mem (stackPtr initial - BitVec.ofNat 64 form.activeMemory.countHigh) 8,
        .flags, .rip] s t ∧
      (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧
      MemoryWriteFrame s t #v[Stack.region initial (v.routine form).minStackBytes] :=
  run ctx input true rip nonDigest

end Sha2.Proofs.Wrapper512.Absorb.Large.Counter
