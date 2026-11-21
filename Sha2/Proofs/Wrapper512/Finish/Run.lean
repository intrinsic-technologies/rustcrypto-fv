import Sha2.Proofs.Wrapper512.Hash.Finalize.Run
import Sha2.Proofs.Wrapper512.Finish.Output

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Finish

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.SHA512

private theorem output_count_preserved [Bindings] {v : Variant} {form : Form}
    {initial s t : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs form)
    (agrees : AgreesExcept (Output.components v initial form) s t)
    (nonterminal : ¬form.isTerminal) :
    v.countValue form initial t = v.countValue form initial s := by
  have r12 := Output.r12_preserved agrees
  have r15 := Output.r15_preserved agrees
  have slot : form = .traitFinalizeIntoReset false →
      memLoad t.external (stackPtr initial - 640) 64 =
      memLoad s.external (stackPtr initial - 640) 64 := by
    intro hf
    subst form
    exact Output.slot_preserved ctx agrees 640
      (by cases v <;> decide +kernel) (by decide) (by decide)
  cases form with
  | slices | digest => exact (nonterminal trivial).elim
  | reset stage =>
    have counts : ∀ stage : Fin 3, (v.traversal (.reset stage)).countReg = some 12 := by
      cases v <;> decide +kernel
    simp only [Variant.countValue, counts]
    exact r12
  | finalizeIntoReset second =>
    cases second
    · cases v
      · exact r12
      · exact r12
      · exact r15
      · exact r15
    · exact (nonterminal rfl).elim
  | traitFinalizeIntoReset second =>
    cases second
    · cases v <;> exact slot rfl
    · exact (nonterminal rfl).elim

private theorem output_stack_frame [Bindings] {v : Variant} {form : Form} {initial s t : RamState}
    (frame : MemoryWriteFrame s t #v[Stack.region initial form.stackBytes]) :
    MemoryWriteFrame s t #v[v.outputRegion initial form,
      Stack.region initial (v.routine form).minStackBytes] := by
  intro a outside
  apply frame a
  intro region member
  have eq : region = Stack.region initial form.stackBytes := by simpa using member
  subst region
  exact outside _ (by simp [Variant.routine])

theorem stage [Bindings] (body : Compression.BlockCorrect) {v : Variant} {form : Form} {initial s : RamState}
    {inputs : Array Input} (ctx : Context v initial inputs form)
    (input : Buffered v initial s (message inputs) form)
    (rip : s.RIP = v.pc (v.dispatchOffset form inputs.isEmpty) form)
    (eligible : form.canFinalize)
    (resetEmptyPointer : form = .reset 1 → inputs.isEmpty = true →
      s.regValue .rax = hashPointer initial form form.finalMemory)
    (resetEmptyWords : form = .reset 1 → inputs.isEmpty = true → ∀ i < 8,
      (.reg (BitVec.ofNat 5 (Dispatch.Store.wordRegister v (.reset 1) i)) : Operand 64).read s = v.initialHash[i]!.toBitVec)
    (finalizeEmpty : form = .finalizeIntoReset false → inputs.isEmpty = true →
      (s.regValue .rax).setWidth 8 = 0 ∧ s.regValue .r14 = 0 ∧ s.regValue (Hash.Finalize.highCountRegister v form) = 0)
    (traitOutput : form = .traitFinalizeIntoReset false →
      if inputs.isEmpty then s.regValue (if v = .sha512 then .r13 else .rbp) = initial.regValue .rcx
      else memLoad s.external (outputSavePointer initial form) 64 = initial.regValue .rcx) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ Preserved v initial t form ∧
      t.RIP = v.pc (v.outputEndOffset form) form ∧
      (v.outputRegion initial form).HasBytes t.external (v.hash (message inputs)) ∧
      MemoryWriteFrame s t #v[v.outputRegion initial form,
        Stack.region initial (v.routine form).minStackBytes] ∧
      (¬form.isTerminal → v.countValue form initial t = v.countValue form initial s) ∧
      (form = .reset 1 → Write.AllHold t (Dispatch.Store.suffixEffect v t (.reset 2)).writes) ∧
      (form = .finalizeIntoReset false → t.regValue .r14 = stackPtr initial - 488) ∧
      (form = .traitFinalizeIntoReset false →
        t.regValue (if v = .sha512 then .rbp else .rbx) = stackPtr initial - 264) := by
  obtain ⟨fuelH, hashed, runH, compressed, frameH, countH, finalizePointerH, traitPointerH⟩ :=
    Hash.Finalize.stage body ctx input rip eligible resetEmptyPointer resetEmptyWords
      finalizeEmpty traitOutput
  obtain ⟨fuelO, finished, runO, preserved, finalRip, bytes, frameO, agrees, stores⟩ :=
    Output.stage ctx compressed
  refine ⟨fuelH + fuelO, finished, runH.trans runO, preserved, finalRip, bytes,
    memoryWriteFrame_trans (output_stack_frame frameH) frameO,
    fun nonterminal => (output_count_preserved ctx agrees nonterminal).trans (countH nonterminal),
    stores, ?_, ?_⟩
  · intro hf
    exact (agrees.read (n := 64) (r := 14) (by simp [Output.components])).trans
      (finalizePointerH hf)
  · intro hf
    have kept : finished.regValue (if v = .sha512 then .rbp else .rbx) =
        hashed.regValue (if v = .sha512 then .rbp else .rbx) := by
      split
      · exact agrees.read (n := 64) (r := 5) (by simp [Output.components])
      · exact agrees.read (n := 64) (r := 3) (by simp [Output.components])
    exact kept.trans (traitPointerH hf)

theorem run_stage [Bindings] (body : Compression.BlockCorrect)
    {v : Variant} {form : Form} {initial s : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs form) (input : Buffered v initial s (message inputs) form)
    (rip : s.RIP = v.pc (v.dispatchOffset form inputs.isEmpty) form)
    (terminal : form.isTerminal := by first | assumption | trivial) :
    ∃ final, FinishResult v initial final inputs form ∧
      MemoryWriteFrame s final #v[v.outputRegion initial form,
        Stack.region initial (v.routine form).minStackBytes] := by
  have eligible : form.canFinalize := by
    cases form <;> simp_all [Form.isTerminal, Form.canFinalize]
  have notReset : form ≠ .reset 1 := by
    intro h
    subst form
    simp [Form.isTerminal] at terminal
  have notFinalize : form ≠ .finalizeIntoReset false := by
    intro h
    subst form
    simp [Form.isTerminal] at terminal
  have notTrait : form ≠ .traitFinalizeIntoReset false := by
    intro h
    subst form
    simp [Form.isTerminal] at terminal
  obtain ⟨_, hashed, _, compressed, frameH, _⟩ := Hash.Finalize.stage body ctx input rip eligible
    (fun h => (notReset h).elim) (fun h => (notReset h).elim)
    (fun h => (notFinalize h).elim) (fun h => (notTrait h).elim)
  obtain ⟨final, result, frameO⟩ := Output.run_preserving_frame ctx compressed terminal
  exact ⟨final, result, memoryWriteFrame_trans (output_stack_frame frameH) frameO⟩

theorem run [Bindings] (body : Compression.BlockCorrect)
    {v : Variant} {form : Form} {initial s : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs form) (input : Buffered v initial s (message inputs) form)
    (rip : s.RIP = v.pc (v.dispatchOffset form inputs.isEmpty) form)
    (eligible : form = .slices ∨ form = .digest := by first | assumption | simp) :
    ∃ final, FinishResult v initial final inputs form := by
  obtain ⟨final, result, _⟩ := run_stage body ctx input rip
    (by rcases eligible with rfl | rfl <;> trivial)
  exact ⟨final, result⟩

end Sha2.Proofs.Wrapper512.Finish
