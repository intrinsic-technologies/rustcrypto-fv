import Sha2.Proofs.Wrapper512.Hash.Finalize.Compress.Setup
import Sha2.Proofs.Wrapper512.Hash.Finalize.Pad
import Sha2.Proofs.Wrapper512.Hash.Finalize.Branch
import Sha2.Proofs.Wrapper512.Hash.Finalize.Zero
import Sha2.Proofs.Wrapper512.Hash.Finalize.Length.Run
import Sha2.Proofs.Wrapper512.Hash.Finalize.Store.Run
import Sha2.Proofs.Wrapper512.Hash.Finalize.Mathematics
import Sha2.Proofs.Wrapper512.Model
import Sha2.Proofs.Common.Memory.Bytes

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Hash.Finalize

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.SHA512

theorem run_padded [Bindings] (body : Compression.BlockCorrect)
    {v : Variant} {form : Form} {initial s : RamState} {inputs : Array Input}
    {message : ByteArray} (ctx : Context v initial inputs form)
    (input : Padded v initial s message form) (eligible : form.canFinalize) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ Compressed v initial t message form ∧
      MemoryWriteFrame s t #v[Stack.region initial form.stackBytes] ∧
      (¬form.isTerminal → v.countValue form initial t = v.countValue form initial s) ∧
      (form = .finalizeIntoReset false → t.regValue .r14 = stackPtr initial - 488) ∧
      (form = .traitFinalizeIntoReset false →
        t.regValue (if v = .sha512 then .rbp else .rbx) = stackPtr initial - 264) := by
  obtain ⟨branched, branchRun, _, branchState, branchRip, branchBytes, branchFrame, branchCount⟩ :=
    branch_local ctx input
  have completed {t : RamState} (state : HashAt v initial t (finalHashFull v message) form)
      (rip : t.RIP = v.pc (Compress.callOffset v form true + 5) form)
      (pointer : form = .reset 1 → true = true → t.regValue .r14 = stackPtr initial - 296) :
      Compressed v initial t message form := by
    have offset : Compress.callOffset v form true + 5 = v.serializeOffset form := by
      cases form with
      | slices | digest => cases v <;> decide +kernel
      | reset stage =>
        have hs : stage = 0 ∨ stage = 1 ∨ stage = 2 := by omega
        rcases hs with rfl | rfl | rfl <;> cases v <;> decide +kernel
      | finalizeIntoReset b | traitFinalizeIntoReset b =>
        cases b <;> cases v <;> decide +kernel
    refine ⟨state.toPreserved, offset ▸ rip, ⟨_, state.hashWords, finalHash_hash v message⟩,
      eligible, fun h => pointer h rfl, ?_⟩
    intro hf
    subst form
    exact state.hashPointer.2
  have traitPointer {t : RamState} {hash : Array UInt64} (state : HashAt v initial t hash form) :
      form = .traitFinalizeIntoReset false →
        t.regValue (if v = .sha512 then .rbp else .rbx) = stackPtr initial - 264 := by
    intro hf
    subst form
    exact state.hashPointer.1
  have lastOffset : storeEndOffset v form = Compress.copySetupOffset v form true := by
    cases form with
    | slices | digest => cases v <;> decide +kernel
    | reset stage =>
      have hs : stage = 0 ∨ stage = 1 ∨ stage = 2 := by omega
      rcases hs with rfl | rfl | rfl <;> cases v <;> decide +kernel
    | finalizeIntoReset b | traitFinalizeIntoReset b =>
      cases b <;> cases v <;> decide +kernel
  by_cases small : message.size % 128 < 112
  · have nextRip : branched.RIP = v.pc (lengthOffset v form) form := by
      simpa only [small, ite_true] using branchRip
    have prefixBytes := Common.Memory.hasBytes_prefix branchBytes (count := 112) (by change 112 ≤ 128; decide)
    rw [paddedBuffer_prefix message small] at prefixBytes
    obtain ⟨nL, lengthReady, runL, _, lengthState, frameL, countL⟩ := Length.run_local ctx branchState nextRip prefixBytes
    obtain ⟨nS, stored, runS, _, storedState, storedRip, storedBytes, frameS, countS⟩ := Store.run_length_local ctx lengthState
    rw [lastOffset] at storedRip
    obtain ⟨nF, finished, runF, finalState, finalRip, frameF, _, pointer, countF, finalizePointer⟩ :=
      Compress.setup_call_local body true ctx storedState storedRip storedBytes
    refine ⟨2+nL+nS+nF, finished, ((branchRun.trans runL).trans runS).trans runF,
      completed ?_ finalRip pointer, memoryWriteFrame_trans (memoryWriteFrame_trans (memoryWriteFrame_trans branchFrame frameL) frameS) frameF,
      fun h => (countF h).trans ((countS h).trans ((countL h).trans (branchCount h))),
      (fun hf => finalizePointer hf rfl), traitPointer finalState⟩
    simpa only [finalHashFull, small, ite_true, finalBlock_eq_tailFirst _ small] using finalState
  · have firstOffset : branchOffset v form + 10 = Compress.copySetupOffset v form false := by
      cases form with
      | slices | digest => cases v <;> decide +kernel
      | reset stage =>
        have hs : stage = 0 ∨ stage = 1 ∨ stage = 2 := by omega
        rcases hs with rfl | rfl | rfl <;> cases v <;> decide +kernel
      | finalizeIntoReset b | traitFinalizeIntoReset b =>
        cases b <;> cases v <;> decide +kernel
    have nextRip : branched.RIP = v.pc (Compress.copySetupOffset v form false) form := by
      simpa only [small, ite_false, firstOffset] using branchRip
    obtain ⟨nC, first, runC, firstState, firstRip, frameC, kept, _, countC, _⟩ :=
      Compress.setup_call_local body false ctx branchState.toHashAt nextRip branchBytes
    have working : Working v initial first message
        (NIST.SHA512.compress (compressBlocks v.initialHash message)
          (NIST.Encoding.octetsToBits (paddedBuffer message))) form :=
      ⟨firstState, (kept rfl).1.trans branchState.blocks,
        (kept rfl).2.1.trans branchState.blocksHigh, (kept rfl).2.2.trans branchState.tailLength⟩
    have zeroOffset : Compress.callOffset v form false + 5 = Zero.offset false form v := by
      cases form with
      | slices | digest => cases v <;> decide +kernel
      | reset stage =>
        have hs : stage = 0 ∨ stage = 1 ∨ stage = 2 := by omega
        rcases hs with rfl | rfl | rfl <;> cases v <;> decide +kernel
      | finalizeIntoReset b | traitFinalizeIntoReset b =>
        cases b <;> cases v <;> decide +kernel
    rw [zeroOffset] at firstRip
    obtain ⟨nZ, zeroed, runZ, zeroState, zeroRip, zeroBytes, _, frameZ, countZ⟩ := zero_stage ctx working firstRip
    have lengthOffsetEq : Zero.nextOffset true form v = lengthOffset v form := by
      cases form with
      | slices | digest => cases v <;> decide +kernel
      | reset stage =>
        have hs : stage = 0 ∨ stage = 1 ∨ stage = 2 := by omega
        rcases hs with rfl | rfl | rfl <;> cases v <;> decide +kernel
      | finalizeIntoReset b | traitFinalizeIntoReset b =>
        cases b <;> cases v <;> decide +kernel
    rw [lengthOffsetEq] at zeroRip
    have prefixBytes : (⟨(stackPtr initial - BitVec.ofNat 64 form.finalMemory.buffer).toNat, 112⟩ : MemoryRegion).HasBytes
        zeroed.external (finalPrefix message) := by
      simpa only [finalPrefix, small, ite_false] using zeroBytes
    obtain ⟨nL, lengthReady, runL, _, lengthState, frameL, countL⟩ := Length.run_local ctx zeroState zeroRip prefixBytes
    obtain ⟨nS, stored, runS, _, storedState, storedRip, storedBytes, frameS, countS⟩ := Store.run_length_local ctx lengthState
    rw [lastOffset] at storedRip
    obtain ⟨nF, finished, runF, finalState, finalRip, frameF, _, pointer, countF, finalizePointer⟩ :=
      Compress.setup_call_local body true ctx storedState storedRip storedBytes
    refine ⟨2+nC+nZ+nL+nS+nF, finished,
      ((((branchRun.trans runC).trans runZ).trans runL).trans runS).trans runF,
      completed ?_ finalRip pointer,
      memoryWriteFrame_trans (memoryWriteFrame_trans (memoryWriteFrame_trans
        (memoryWriteFrame_trans (memoryWriteFrame_trans branchFrame frameC) frameZ) frameL) frameS) frameF,
      fun h => (countF h).trans ((countS h).trans ((countL h).trans
        ((countZ h).trans ((countC h).trans (branchCount h))))),
      (fun hf => finalizePointer hf rfl), traitPointer finalState⟩
    simpa only [finalHashFull, small, ite_false, finalBlock_eq_tailLast _ small,
      paddedBuffer, tailFirst] using finalState

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
      (s.regValue .rax).setWidth 8 = 0 ∧ s.regValue .r14 = 0 ∧ s.regValue (highCountRegister v form) = 0)
    (traitOutput : form = .traitFinalizeIntoReset false →
      if inputs.isEmpty then s.regValue (if v = .sha512 then .r13 else .rbp) = initial.regValue .rcx
      else memLoad s.external (outputSavePointer initial form) 64 = initial.regValue .rcx) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ Compressed v initial t (message inputs) form ∧
      MemoryWriteFrame s t #v[Stack.region initial form.stackBytes] ∧
      (¬form.isTerminal → v.countValue form initial t = v.countValue form initial s) ∧
      (form = .finalizeIntoReset false → t.regValue .r14 = stackPtr initial - 488) ∧
      (form = .traitFinalizeIntoReset false →
        t.regValue (if v = .sha512 then .rbp else .rbx) = stackPtr initial - 264) := by
  obtain ⟨fuelU, u, runU, padded, frameU, countU⟩ :=
    pad_stage ctx input rip eligible resetEmptyPointer resetEmptyWords finalizeEmpty traitOutput
  obtain ⟨fuelT, t, runT, compressed, frameT, countT, finalizePointer, traitPointer⟩ := run_padded body ctx padded eligible
  exact ⟨fuelU+fuelT, t, runU.trans runT, compressed, memoryWriteFrame_trans frameU frameT,
    fun h => (countT h).trans (countU h), finalizePointer, traitPointer⟩

theorem run [Bindings] (body : Compression.BlockCorrect)
    {v : Variant} {form : Form} {initial s : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs form) (input : Buffered v initial s (message inputs) form)
    (rip : s.RIP = v.pc (if form = .slices then 0x218 else 0x143) form)
    (eligible : form = .slices ∨ form = .digest := by first | assumption | simp) : ∃ t, Compressed v initial t (message inputs) form := by
  obtain ⟨_, t, _, compressed, _, _⟩ := stage body ctx input
    (by rcases eligible with rfl | rfl <;> exact rip)
    (by rcases eligible with rfl | rfl <;> trivial)
    (by rcases eligible with rfl | rfl <;> simp)
    (by rcases eligible with rfl | rfl <;> simp)
    (by rcases eligible with rfl | rfl <;> simp)
    (by rcases eligible with rfl | rfl <;> simp)
  exact ⟨t, compressed⟩

end Sha2.Proofs.Wrapper512.Hash.Finalize
