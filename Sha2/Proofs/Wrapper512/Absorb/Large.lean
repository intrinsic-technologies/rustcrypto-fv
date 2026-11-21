import Sha2.Proofs.Wrapper512.Absorb.Large.Empty
import Sha2.Proofs.Wrapper512.Absorb.Large.Fill
import Sha2.Proofs.Wrapper512.Absorb.Large.Blocks
import Sha2.Proofs.Wrapper512.Absorb.Next

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Absorb
open Sha2.Proofs.Wrapper (prefixMessage)
open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem large_flow (v : Variant) (form : Form) (hd : form ≠ .digest) :
    Large.FillSetup.startOffset v form = v.largeOffset form + 9 ∧
    Large.finishMoveOffset v form + 3 = Large.Blocks.countOffset v false form ∧
    Large.Blocks.tailEndPC v form = counterPC v true form := by
  cases v <;> cases form with
  | digest => exact (hd rfl).elim
  | reset stage => revert stage; decide +kernel
  | finalizeIntoReset second | traitFinalizeIntoReset second => revert second; decide +kernel
  | slices => decide +kernel

theorem large [Bindings] (body : Common.SHA512.Compression.BlockCorrect)
    {v : Variant} {form : Form} {initial s : RamState} {inputs : Array Input} {index : Nat}
    (ctx : Context v initial inputs form) (input : Prepared v initial s inputs index form)
    (rip : s.RIP = v.pc (v.largeOffset form) form)
    (enough : 128 - (prefixMessage inputs index).size % 128 ≤ (inputs[index]'input.remaining).bytes.size)
    (hd : form ≠ .digest := by decide) :
    ∃ t, Buffered v initial t (prefixMessage inputs (index + 1)) form form.activeMemory ∧
      t.RIP = counterPC v true form ∧
      v.indexValue form t = BitVec.ofNat 64 index ∧
      v.countValue form initial t = BitVec.ofNat 64 inputs.size ∧
      (form = .traitFinalizeIntoReset false →
        memLoad t.external (outputSavePointer initial form) 64 = initial.regValue .rcx) ∧
      (form = .reset 1 → t.regValue .rbx = bufferPointer initial form) ∧
      (match (generalizing := false) form with
        | .reset stage => stage.val = 2 → t.regValue .rbx = 0x10dd60
        | .finalizeIntoReset true =>
          t.regValue (if v = .sha384 ∨ v = .sha512 then .rbx else .r12) = 0x10dd60
        | .traitFinalizeIntoReset second =>
          t.regValue (if second then .rbp else .r13) = 0x10dd60
        | _ => True) ∧
      (∀ second, form = .traitFinalizeIntoReset second →
        t.regValue .rbx = bufferPointer initial form form.activeMemory) ∧
      (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧
      MemoryWriteFrame s t #v[Stack.region initial (v.routine form).minStackBytes] := by
  have flow := large_flow v form hd
  obtain ⟨a, selected, ripA,selectedRun,selectedFrame⟩ := select_empty ctx input rip hd
  have pending : ∃ u consumed, Blocks.Input v initial u inputs index consumed form ∧
      (u.RIP = Large.Blocks.countPC v false form ∨ u.RIP = Large.Blocks.countPC v true form) ∧
      (∃ fuel, Advances (returnBoundary initial) fuel a u) ∧
      MemoryWriteFrame a u #v[Stack.region initial (v.routine form).minStackBytes] := by
    by_cases zero : (prefixMessage inputs index).size % 128 = 0
    · obtain ⟨u, state, entry,localRun,localFrame⟩ := Large.empty ctx selected
        (by simpa only [zero, ite_true] using ripA) zero hd
      exact ⟨u, 0, state, Or.inr entry,localRun,localFrame⟩
    · have entryA : a.RIP = v.pc (Large.FillSetup.startOffset v form) form := by
        rw [flow.1]
        simpa only [zero, ite_false] using ripA
      obtain ⟨u, state, entry,localRun,localFrame⟩ := Large.fill body ctx selected entryA enough hd
        selected.bufferRegister (by
          cases form with
          | finalizeIntoReset second => cases second <;> exact selected.memcpyTarget
          | _ => exact selected.memcpyTarget)
      exact ⟨u, _, state, Or.inl (entry.trans (congrArg (fun n => v.pc n form) flow.2.1)),localRun,localFrame⟩
  obtain ⟨u, consumed, state, entry,pendingRun,pendingFrame⟩ := pending
  obtain ⟨t, result, exit,blocksRun,blocksFrame⟩ := Large.Blocks.run body ctx state entry hd
  obtain ⟨selectedFuel,selectedRun⟩ := selectedRun
  obtain ⟨pendingFuel,pendingRun⟩ := pendingRun
  obtain ⟨blocksFuel,blocksRun⟩ := blocksRun
  refine ⟨t, result.toBuffered, exit.trans flow.2.2, result.indexRegister,
    result.countRegister, result.outputSaved, result.bufferRegister, ?_, result.activeBufferRegister,
    ⟨_,selectedRun.trans (pendingRun.trans blocksRun)⟩,
    memoryWriteFrame_trans selectedFrame (memoryWriteFrame_trans pendingFrame blocksFrame)⟩
  cases form with
  | finalizeIntoReset second => cases second <;> exact result.memcpyTarget
  | _ => exact result.memcpyTarget
end Sha2.Proofs.Wrapper512.Absorb
