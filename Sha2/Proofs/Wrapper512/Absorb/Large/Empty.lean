import Sha2.Proofs.Wrapper512.Absorb.Branch
import Sha2.Proofs.Wrapper512.Absorb.Blocks.State
import Sha2.Proofs.Common.SHA256.Blocks.Absorb.Instruction
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Absorb.Large
open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.SHA256.Absorb.Blocks
open Sha2.Proofs.Common.Field (AdvanceTriple)

def emptyBytes (v : Variant) (form : Form := .slices) : List UInt8 :=
  encodeMovR64R64 ((v.restRegister form).setWidth 4)
    (BitVec.ofNat 4 (v.traversal form).lengthReg)

theorem empty_bytes (v : Variant) (form : Form) (h : form ≠ .digest) :
    Extracted.textBytes.toListFrom (v.textOffset form + v.emptyOffset form) 3 =
      emptyBytes v form := by
  cases v <;> cases form with
  | digest => exact (h rfl).elim
  | slices => decide +kernel
  | reset stage => revert stage; decide +kernel
  | finalizeIntoReset second | traitFinalizeIntoReset second => revert second; decide +kernel

theorem empty_move [Bindings] (v : Variant) (form : Form) :
    StepEffect (fun s => s.RIP = v.pc (v.emptyOffset form) form)
      (codeRange (v.pc (v.emptyOffset form) form) (emptyBytes v form))
      (movR64R64Effect (v.pc (v.emptyOffset form) form)
        ((v.restRegister form).setWidth 4 |>.setWidth 5)
        (BitVec.ofNat 5 (v.traversal form).lengthReg)) := by
  have width : (BitVec.ofNat 4 (v.traversal form).lengthReg).setWidth 5 =
      BitVec.ofNat 5 (v.traversal form).lengthReg := by
    cases v <;> cases form with
    | reset stage => revert stage; decide +kernel
    | finalizeIntoReset second | traitFinalizeIntoReset second => revert second; decide +kernel
    | _ => decide +kernel
  simpa only [emptyBytes, width] using
    move_step (v.pc (v.emptyOffset form) form) ((v.restRegister form).setWidth 4)
      (BitVec.ofNat 4 (v.traversal form).lengthReg)
end Sha2.Proofs.Wrapper512.Absorb.Large

namespace Sha2.Proofs.Wrapper512.Absorb.Large
open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Wrapper

def emptyChanges (v : Variant) (form : Form) : List Component :=
  [.reg (v.restRegister form), .rip] ++
    match form with | .traitFinalizeIntoReset _ => [.reg 3] | _ => []

set_option hygiene false in
local macro "finite_empty" : tactic => `(tactic| (
  try cases form
  all_goals try (
    rename_i stage
    have _ : Fin 3 := stage
    rcases stage with ⟨n, hn⟩
    have hs : n = 0 ∨ n = 1 ∨ n = 2 := by omega
    rcases hs with rfl | rfl | rfl)
  all_goals try (
    rename_i second
    have _ : Bool := second
    cases second)
  all_goals try cases v
  all_goals first | rfl | decide +kernel +revert | (simp_all [emptyChanges, Variant.restRegister, Variant.traversal, ResetLayout.reset, ResetLayout.finalizeIntoReset, ResetLayout.traitFinalizeIntoReset, Component.Covers, Variant.emptyOffset, Variant.textOffset, emptyBytes] <;> omega) | omega))

theorem empty_bound (v : Variant) (form : Form) :
    v.textOffset form + v.emptyOffset form + (emptyBytes v form).length ≤ 71757 := by
  cases v <;> cases form with
  | slices | digest => decide +kernel
  | reset stage => revert stage; decide +kernel
  | finalizeIntoReset second | traitFinalizeIntoReset second => revert second; decide +kernel

theorem empty_end (v : Variant) (form : Form) :
    v.pc (v.emptyOffset form) form + BitVec.ofNat 64 (match form with | .traitFinalizeIntoReset _ => 8 | _ => 3) =
      v.pc ((v.traversal form).exit - 11) form := by
  cases v <;> cases form with
  | slices | digest => decide +kernel
  | reset stage => revert stage; decide +kernel
  | finalizeIntoReset second | traitFinalizeIntoReset second => revert second; decide +kernel

set_option maxRecDepth 2048 in
set_option maxHeartbeats 2000000 in
theorem empty [Bindings] {v : Variant} {form : Form} {initial s : RamState}
    {inputs : Array Input} {index : Nat} (ctx : Context v initial inputs form)
    (input : Prepared v initial s inputs index form)
    (rip : s.RIP = v.pc (v.emptyOffset form) form)
    (position : (prefixMessage inputs index).size % 128 = 0)
    (table : form ≠ .digest := by simp) :
    ∃ t, Absorb.Blocks.Input v initial t inputs index 0 form ∧
      t.RIP = v.pc ((v.traversal form).exit - 11) form ∧
      (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧
      MemoryWriteFrame s t #v[Stack.region initial (v.routine form).minStackBytes] := by
  have width : ((v.restRegister form).setWidth 4).setWidth 5 = v.restRegister form := by
    finite_empty
  have outside := (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2
  have inside (n : Nat) (hn : n ≤ 8) : InProgram (v.pc (v.emptyOffset form) form + BitVec.ofNat 64 n) := by
    rw [Variant.pc_add v (v.emptyOffset form) n form]
    apply inProgram_of_textOffset
    finite_empty
  obtain ⟨u, run, ready, effect⟩ := (empty_move v form).advances
    (supportedMachine_readyToStep input.machine)
    (programText_slice (programLoaded_codeIn input.loaded) (v.textOffset form + v.emptyOffset form)
      (emptyBytes v form) (empty_bound v form) (empty_bytes v form table)) rip
    (boundary_ne_program outside (inside 3 (by decide)))
  have frame : AgreesExcept [.reg (v.restRegister form),.rip] s u := by
    simpa only [movR64R64Effect, Effect.components, width, List.map, Write.component, Operand.component, List.append_nil, List.cons_append, List.nil_append] using effect.agrees
  have length : (.reg (v.restRegister form) : Operand 64).read u =
      BitVec.ofNat 64 (inputs[index]'input.remaining).bytes.size := by
    have h := effect.writes
    simp only [movR64R64Effect, Write.AllHold, width] at h
    exact h.trans input.length
  have machine : ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ ReadyToStep t ∧
      AgreesExcept (emptyChanges v form) s t ∧
      (.reg (v.restRegister form) : Operand 64).read t = BitVec.ofNat 64 (inputs[index]'input.remaining).bytes.size ∧
      (∀ second, form = .traitFinalizeIntoReset second →
        t.regValue .rbx = bufferPointer initial form form.activeMemory) ∧
      t.RIP = v.pc ((v.traversal form).exit - 11) form := by
    cases form with
    | traitFinalizeIntoReset second =>
      obtain ⟨t, runT, readyT, eff⟩ :=
        (lea_r64_effect_step (v.pc (v.emptyOffset (.traitFinalizeIntoReset second)) (.traitFinalizeIntoReset second) + 3)
          0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 32))
          (by decide +kernel) rfl rfl).advances ready
          (by
            rw [show v.pc (v.emptyOffset (.traitFinalizeIntoReset second)) (.traitFinalizeIntoReset second) + 3 = Extracted.textAddress + BitVec.ofNat 64 (v.textOffset (.traitFinalizeIntoReset second) + v.emptyOffset (.traitFinalizeIntoReset second) + 3) by simp only [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat]]
            apply programText_slice (programLoaded_codeIn (buffered_of_agrees ctx input.toBuffered run ready frame
              (by simp [Component.Covers]) (by cases second <;> simp [Variant.restRegister])
              (by simp) (by simp) (fun h => .inr (input.outputSaved h))).loaded)
              (v.textOffset (.traitFinalizeIntoReset second) + v.emptyOffset (.traitFinalizeIntoReset second) + 3)
            all_goals cases v <;> cases second <;> decide +kernel)
          effect.rip (by
            change v.pc (v.emptyOffset (.traitFinalizeIntoReset second)) (.traitFinalizeIntoReset second) + 3 + 5 ≠ _
            simpa only [BitVec.add_assoc, BitVec.reduceAdd] using boundary_ne_program outside (inside 8 (by decide)))
      have frameT : AgreesExcept [.reg 3,.rip] u t := eff.agrees
      refine ⟨_,t,run.trans runT,readyT,(frame.trans frameT).mono (by simp [emptyChanges]),?_,?_,?_⟩
      · exact (frameT.read (n := 64) (r := v.restRegister _) (by cases second <;> simp [Variant.restRegister])).trans length
      · intro other eq; cases eq
        have rsp : stackPtr u = stackPtr initial - BitVec.ofNat 64 (Form.traitFinalizeIntoReset second).frameBytes :=
          (frame.read (n := 64) (r := 4) (by cases second <;> simp [Variant.restRegister])).trans input.rsp
        have h := eff.writes
        change t.regValue .rbx = stackPtr u + 32 at h
        rw [h, rsp]
        cases second <;> simp [bufferPointer, Form.activeMemory, Form.frameBytes, ResetLayout.finalizeMemory, BitVec.sub_eq_add_neg, BitVec.add_assoc]
      · rw [eff.rip]
        change v.pc (v.emptyOffset (.traitFinalizeIntoReset second)) (.traitFinalizeIntoReset second) + 3 + 5 = _
        cases v <;> cases second <;> decide +kernel
    | slices | digest | reset stage | finalizeIntoReset second =>
      refine ⟨_,u,run,ready,?_,length,?_,?_⟩
      · simpa only [emptyChanges, List.append_nil] using frame
      · intros; contradiction
      · rw [effect.rip]
        exact empty_end v _
  obtain ⟨fuel,t,runT,readyT,frameT,lengthT,bufferT,ripT⟩ := machine
  have noMem : ∀ c ∈ emptyChanges v form, ∀ a, ¬ c.Covers a := by
    finite_empty
  have memory := frameT.external noMem
  have buffered := buffered_of_agrees ctx input.toBuffered runT readyT frameT noMem
    (by finite_empty) (by finite_empty) (fun h => (table h).elim) (fun h => .inr (input.outputSaved h))
  refine ⟨t,⟨buffered.toPreserved,input.remaining,Nat.zero_le _,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,bufferT⟩,ripT,⟨fuel,runT⟩,frameT.memoryWriteFrame
    (fun c hc a ha => (noMem c hc a ha).elim)⟩
  · simpa using position
  · simpa using buffered.hashWords
  · simpa using buffered.blockCount
  · simpa using buffered.blockCountHigh
  · simpa only [Variant.sourceValue, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using (frameT.read (n := 64) (r := BitVec.ofNat 5 (v.traversal form).dataReg) (by finite_empty)).trans input.source
  · simpa using lengthT
  · exact (frameT.read (n := 64) (r := BitVec.ofNat 5 (v.traversal form).indexReg) (by finite_empty)).trans input.indexRegister
  · rw [← input.countRegister]
    have kept : Component.reg (BitVec.ofNat 5 ((v.traversal form).countReg.getD 0)) ∉ emptyChanges v form := by
      finite_empty
    unfold Variant.countValue
    split
    · rename_i reg heq
      apply frameT.read
      simpa only [heq, Option.getD_some] using kept
    · rw [memory]
  · intro h; rw [memory]; exact input.outputSaved h
  · intro h; subst form
    exact (frameT.read (n := 64) (r := 3) (by simp [emptyChanges, Variant.restRegister])).trans (input.bufferRegister rfl)
  · cases form with
    | slices | digest | traitFinalizeIntoReset _ => trivial
    | reset stage =>
      intro h
      exact (frameT.read (n := 64) (r := 3) (by simp [emptyChanges, Variant.restRegister, h])).trans (input.memcpyTarget h)
    | finalizeIntoReset second =>
      cases second with
      | false => trivial
      | true =>
        have h := frameT.read (n := 64) (r := if v = .sha384 ∨ v = .sha512 then 3 else 12) (by cases v <;> simp [emptyChanges, Variant.restRegister])
        cases v <;> exact h.trans input.memcpyTarget
end Sha2.Proofs.Wrapper512.Absorb.Large
