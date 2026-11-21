import Sha2.Proofs.Wrapper512.Hash.Finalize.Store.Machine
import Sha2.Proofs.Wrapper512.Hash.Finalize.Store.Bytes
import Sha2.Proofs.Wrapper512.Hash.Finalize.State
import Sha2.Proofs.Wrapper512.Machine.Initialize
import Sha2.Proofs.Wrapper512.Absorb.Memory

import Sha2.Proofs.Common.Machine.CallMemory

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Hash.Finalize.Store

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA512
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Wrapper.Hash (bswap64_ofNat_storedByte)

macro "store_form_cases" f:term:max : tactic => `(tactic|
  first |
    rcases ($f) with _ | _ | stage | second | second
    all_goals first
      | have h : stage = 0 ∨ stage = 1 ∨ stage = 2 := by omega
        rcases h with h | h | h <;> subst stage
      | cases second
      | skip)

set_option maxRecDepth 4096 in
theorem run_length_local [Bindings] {v : Variant} {form : Form} {initial s : RamState} {inputs : Array Input}
    {message : ByteArray} {hash : Array UInt64} (ctx : Context v initial inputs form)
    (input : LengthReady v initial s message hash form)
 :
    ∃ n t, Advances (returnBoundary initial) n s t ∧
      AgreesExcept [.mem (stackPtr initial - BitVec.ofNat 64 (form.finalMemory.buffer - 112)) 8,
        .mem (stackPtr initial - BitVec.ofNat 64 (form.finalMemory.buffer - 120)) 8, .rip] s t ∧ HashAt v initial t hash form ∧ t.RIP = v.pc (storeEndOffset v form) form ∧
      (⟨(stackPtr initial - BitVec.ofNat 64 form.finalMemory.buffer).toNat, 128⟩ : MemoryRegion).HasBytes
        t.external (finalBlock message) ∧
      MemoryWriteFrame s t #v[Stack.region initial form.stackBytes] ∧
      (¬ form.isTerminal → v.countValue form initial t = v.countValue form initial s) := by
  have writable (offset : Nat) (bound : offset ≤ (v.routine form).minStackBytes) (align : offset % 8 = 0) :
      MemWritable s (stackPtr initial - BitVec.ofNat 64 offset) 8 := by
    have w := Dispatch.stack_sub_writable8_512 ctx bound align
    exact ⟨w.low, fun i hi => input.allocated _ (w.mem i hi), w.tables⟩
  have pre : Pre v s form := by
    refine ⟨input.rip, ?_, ?_⟩
    · intro i member
      rw [Machine.Initialize.stack_address input.rsp]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      all_goals store_form_cases form <;> simp only [Nat.reduceSub, Nat.reduceAdd, Form.frameBytes, Form.finalMemory, ResetLayout.resetMemory, ResetLayout.finalizeMemory, BitVec.reduceSub]
      all_goals exact writable _ (by cases v <;> decide) (by decide)
    · intro i member offset len bound
      rw [Machine.Initialize.stack_address input.rsp]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      all_goals store_form_cases form <;> simp only [Nat.reduceSub, Nat.reduceAdd, Form.frameBytes, Form.finalMemory, ResetLayout.resetMemory, ResetLayout.finalizeMemory, BitVec.reduceSub]
      all_goals exact Machine.Stages.stack_slot_codeApart ctx (by cases v <;> decide) (by decide) bound
  obtain ⟨n, t, execution, ready, _, output⟩ := run (returnBoundary initial)
    ((valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2) s
    (supportedMachine_readyToStep input.machine) (code (form := form) input.loaded) pre
  have rsp : rspOf s = stackPtr initial - BitVec.ofNat 64 form.frameBytes := input.rsp
  have frame : AgreesExcept [.mem (stackPtr initial - BitVec.ofNat 64 (form.finalMemory.buffer - 112)) 8,
      .mem (stackPtr initial - BitVec.ofNat 64 (form.finalMemory.buffer - 120)) 8, .rip] s t := by
    store_form_cases form <;> simpa only [effect, Nat.reduceSub, Nat.reduceAdd, Form.frameBytes, Form.finalMemory, ResetLayout.resetMemory, ResetLayout.finalizeMemory, ResetLayout.cloneMemory, ↓reduceIte, reduceCtorEq, Effect.components, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Nat.reduceDiv, Write.component, Operand.component,
      rsp, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd,
      BitVec.ofNat_eq_ofNat] using output.agrees
  have localWrites : Absorb.LocalWrites initial
      [.mem (stackPtr initial - BitVec.ofNat 64 (form.finalMemory.buffer - 112)) 8,
       .mem (stackPtr initial - BitVec.ofNat 64 (form.finalMemory.buffer - 120)) 8, .rip] form := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · have locality :=  Absorb.local_memory (form := form) (offset := form.finalMemory.buffer - 112)
        (by store_form_cases form <;> decide)
        (by store_form_cases form <;> decide)
        (by
          store_form_cases form <;> first
            | exact .inr (by decide)
            | intro slot member
              simp only [Form.metadataSlots, List.mem_cons, List.not_mem_nil, or_false] at member
              rcases member with h | h | h | h <;> subst slot
              all_goals unfold OffsetsApart; decide +kernel) a ha
      store_form_cases form <;> exact locality
    · have locality :=  Absorb.local_memory (form := form) (offset := form.finalMemory.buffer - 120)
        (by store_form_cases form <;> decide)
        (by store_form_cases form <;> decide)
        (by
          store_form_cases form <;> first
            | exact .inr (by decide)
            | intro slot member
              simp only [Form.metadataSlots, List.mem_cons, List.not_mem_nil, or_false] at member
              rcases member with h | h | h | h <;> subst slot
              all_goals unfold OffsetsApart; decide +kernel) a ha
      store_form_cases form <;> exact locality
    · exact ha.elim
  have preserved := Absorb.preserved_of_agrees ctx input.toPreserved execution ready frame localWrites
    (by simp) (by simp) (by simp) (by intro _; exact .inl (by simp))
  have kept (offset len : Nat)
      (apartHigh : OffsetsApart (-BitVec.ofNat 64 (form.finalMemory.buffer - 112)) 8 (-BitVec.ofNat 64 offset) len)
      (apartLow : OffsetsApart (-BitVec.ofNat 64 (form.finalMemory.buffer - 120)) 8 (-BitVec.ofNat 64 offset) len)
      (size : 8 + len < 2^64) :
      ∀ i < len, t.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
        s.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
    intro i hi
    apply frame.byte
    intro c hc ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · obtain ⟨j, hj, he⟩ := ha
      exact OffsetsApart.ne apartHigh (stackPtr initial) hj hi size
        (by simpa only [BitVec.sub_eq_add_neg] using he.symm)
    · obtain ⟨j, hj, he⟩ := ha
      exact OffsetsApart.ne apartLow (stackPtr initial) hj hi size
        (by simpa only [BitVec.sub_eq_add_neg] using he.symm)
    · exact ha.elim
  have stackFrame : MemoryWriteFrame s t #v[Stack.region initial form.stackBytes] :=
    frame.memoryWriteFrame (localWrites.stack ctx)
  have countKept : ¬ form.isTerminal → v.countValue form initial t = v.countValue form initial s := by
    intro nonterminal
    cases form with
    | slices | digest => exact (nonterminal trivial).elim
    | reset stage =>
      have counts : ∀ stage : Fin 3, (v.traversal (.reset stage)).countReg = some 12 := by
        cases v <;> decide +kernel
      simp only [Variant.countValue, counts]
      exact frame.read (n := 64) (r := 12) (by simp)
    | finalizeIntoReset second =>
      cases second
      · cases v <;> first
          | exact frame.read (n := 64) (r := 12) (by simp)
          | exact frame.read (n := 64) (r := 15) (by simp)
      · exact (nonterminal rfl).elim
    | traitFinalizeIntoReset second =>
      cases second
      · have keptCount : memLoad t.external (stackPtr initial - 640) 64 =
            memLoad s.external (stackPtr initial - 640) 64 := by
          apply memLoad_congr
          intro i hi
          exact congrArg (fun x : Option UInt8 => x.getD 0)
            (kept 640 8 (by unfold OffsetsApart; decide +kernel)
              (by unfold OffsetsApart; decide +kernel) (by decide) i hi)
        cases v <;> exact keptCount
      · exact (nonterminal rfl).elim
  have hashT : HashAt v initial t hash form :=
    ⟨preserved, Absorb.hashState_of_bytes input.hashWords
      (kept form.finalMemory.hash 64 (by store_form_cases form <;> unfold OffsetsApart <;> decide +kernel)
        (by store_form_cases form <;> unfold OffsetsApart <;> decide +kernel) (by decide)),
      by
        store_form_cases form <;> cases v
        all_goals simp only [hashPointerState] at *
        all_goals first
          | trivial
          | exact (frame.read (n := 64) (r := 14) (by simp)).trans input.hashPointer
          | exact (frame.read (n := 64) (r := 3) (by simp)).trans input.hashPointer
          | exact ⟨(frame.read (n := 64) (r := 3) (by simp)).trans input.hashPointer.1,
              (frame.read (n := 64) (r := 5) (by simp)).trans input.hashPointer.2⟩
          | exact ⟨(frame.read (n := 64) (r := 5) (by simp)).trans input.hashPointer.1,
              (frame.read (n := 64) (r := 13) (by simp)).trans input.hashPointer.2⟩⟩
  have highWord : memLoad t.external (stackPtr initial - BitVec.ofNat 64 (form.finalMemory.buffer - 112)) 64 =
      bswap64 (BitVec.ofNat 64 ((8*message.size)/2^64)) := by
    have h : memLoad t.external (rspOf s + (BitVec.ofNat 64 (form.frameBytes - form.finalMemory.buffer + 112))) 64 = s.regValue (highCountRegister v form) := output.writes.1
    rw [input.lengthHigh] at h
    store_form_cases form <;> simpa only [Nat.reduceSub, Nat.reduceAdd, Form.frameBytes, Form.finalMemory, ResetLayout.resetMemory, ResetLayout.finalizeMemory, ResetLayout.cloneMemory, ↓reduceIte, reduceCtorEq, rsp, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      BitVec.reduceNeg, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using h
  have lowWord : memLoad t.external (stackPtr initial - BitVec.ofNat 64 (form.finalMemory.buffer - 120)) 64 =
      bswap64 (BitVec.ofNat 64 (8*message.size)) := by
    have h : memLoad t.external (rspOf s + (BitVec.ofNat 64 (form.frameBytes - form.finalMemory.buffer + 120))) 64 = s.regValue (lowLengthRegister v form) := output.writes.2
    store_form_cases form <;> simpa only [Nat.reduceSub, Nat.reduceAdd, Form.frameBytes, Form.finalMemory, ResetLayout.resetMemory, ResetLayout.finalizeMemory, ResetLayout.cloneMemory, ↓reduceIte, reduceCtorEq, rsp, input.lengthLow, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      BitVec.reduceNeg, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using h
  have lengthBytes (i : Nat) (hi : i < 16) :
      t.external[stackPtr initial - BitVec.ofNat 64 (form.finalMemory.buffer - 112) + BitVec.ofNat 64 i]? =
        some ((NIST.Encoding.natToOctets 16 (8*message.size)).data[i]'(by
          simpa only [ByteArray.size_data, Common.Encoding.natToOctets_size] using hi)) := by
    by_cases high : i < 8
    · have stored := Bytes.of_memLoad (n := 64)
        (Machine.Initialize.stack_readable ctx hashT.toState (offset := form.finalMemory.buffer - 112) (len := 8)
          (by store_form_cases form <;> cases v <;> decide) (by omega)).mem
      rw [highWord] at stored
      have byte := stored i high
      rw [bswap64_ofNat_storedByte _ high] at byte
      simpa only [BitVec.ofNat_eq_ofNat] using byte.trans (congrArg some (length_high_byte (8*message.size) i high))
    · have stored := Bytes.of_memLoad (n := 64)
        (Machine.Initialize.stack_readable ctx hashT.toState (offset := form.finalMemory.buffer - 120) (len := 8)
          (by store_form_cases form <;> cases v <;> decide) (by omega)).mem
      rw [lowWord] at stored
      have byte := stored (i-8) (by omega)
      rw [bswap64_ofNat_storedByte _ (by omega)] at byte
      have address : stackPtr initial - BitVec.ofNat 64 (form.finalMemory.buffer - 112) + BitVec.ofNat 64 i =
          stackPtr initial - BitVec.ofNat 64 (form.finalMemory.buffer - 120) + BitVec.ofNat 64 (i-8) := by
        conv => lhs; rw [show i = 8+(i-8) by omega, BitVec.ofNat_add]
        simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
        store_form_cases form <;> simp only [Form.finalMemory, ResetLayout.resetMemory, ResetLayout.finalizeMemory, Nat.reduceSub, BitVec.reduceNeg]
        all_goals simp only [← BitVec.add_assoc, BitVec.reduceAdd]
      rw [address]
      have value := length_low_byte (8*message.size) (i-8) (by omega)
      simp only [show 8 + (i-8) = i by omega] at value
      simpa only [BitVec.ofNat_eq_ofNat] using byte.trans (congrArg some value)
  refine ⟨n, t, execution, frame, hashT, output.rip, ⟨finalBlock_size message, ?_⟩, stackFrame, countKept⟩
  intro i
  have hi : i.val < 128 := by simpa only [finalBlock_size] using i.isLt
  change t.external[BitVec.ofNat 64 ((stackPtr initial - BitVec.ofNat 64 form.finalMemory.buffer).toNat + i.val)]? =
    some ((finalPrefix message ++ NIST.Encoding.natToOctets 16 (8*message.size))[i.val]'(by change i.val < (finalBlock message).size; exact i.isLt))
  rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  by_cases inPrefix : i.val < 112
  · rw [ByteArray.getElem_append_left (by rw [finalPrefix_size]; exact inPrefix)]
    have same := kept form.finalMemory.buffer 112 (by store_form_cases form <;> unfold OffsetsApart <;> decide +kernel)
      (by store_form_cases form <;> unfold OffsetsApart <;> decide +kernel) (by decide) i.val inPrefix
    have same' : t.external[stackPtr initial - BitVec.ofNat 64 form.finalMemory.buffer + BitVec.ofNat 64 i.val]? =
        s.external[stackPtr initial - BitVec.ofNat 64 form.finalMemory.buffer + BitVec.ofNat 64 i.val]? := by
      simpa only [BitVec.ofNat_eq_ofNat] using same
    rw [same']
    simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat]
      using input.prefixBytes.2 ⟨i.val, by rw [finalPrefix_size]; exact inPrefix⟩
  · rw [ByteArray.getElem_append_right (by rw [finalPrefix_size]; omega)]
    have address : stackPtr initial - BitVec.ofNat 64 form.finalMemory.buffer + BitVec.ofNat 64 i.val =
        stackPtr initial - BitVec.ofNat 64 (form.finalMemory.buffer - 112) + BitVec.ofNat 64 (i.val-112) := by
      conv => lhs; rw [show i.val = 112+(i.val-112) by omega, BitVec.ofNat_add]
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
      store_form_cases form <;> simp only [Form.finalMemory, ResetLayout.resetMemory, ResetLayout.finalizeMemory, Nat.reduceSub, BitVec.reduceNeg]
      all_goals simp only [← BitVec.add_assoc, BitVec.reduceAdd]
    rw [address]
    simpa only [finalPrefix_size, ByteArray.getElem_eq_getElem_data] using lengthBytes (i.val-112) (by omega)

theorem run_length [Bindings] {v : Variant} {form : Form} {initial s : RamState} {inputs : Array Input}
    {message : ByteArray} {hash : Array UInt64} (ctx : Context v initial inputs form)
    (input : LengthReady v initial s message hash form)
    (eligible : form = .slices ∨ form = .digest := by first | assumption | simp) :
    ∃ t, HashAt v initial t hash form ∧ t.RIP = v.pc (if form = .slices then 0x353 else 0x266) form ∧
      (⟨(stackPtr initial - 600).toNat, 128⟩ : MemoryRegion).HasBytes
        t.external (finalBlock message) := by
  obtain ⟨_, t, _, _, hashT, rip, bytes, _, _⟩ := run_length_local ctx input
  rcases eligible with rfl | rfl <;> exact ⟨t, hashT, rip, bytes⟩

end Sha2.Proofs.Wrapper512.Hash.Finalize.Store
