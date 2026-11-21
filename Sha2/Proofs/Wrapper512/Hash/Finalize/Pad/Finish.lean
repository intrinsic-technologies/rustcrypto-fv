import Sha2.Proofs.Wrapper512.Hash.Finalize.Pad.Setup
import Sha2.Proofs.Wrapper512.Hash.Finalize.Pad.Fill
import Sha2.Proofs.Wrapper512.Hash.Finalize.Pad.Bytes

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Hash.Finalize.Pad

open Sha2.Spec Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.SHA512

theorem finish_local [Bindings] {v : Variant} {form : Form} {initial s : RamState}
    {inputs : Array Input} {message : ByteArray}
    (ctx : Context v initial inputs form) (input : FillReady v initial s message form) :
    ∃ t, (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧
      Padded v initial t message form ∧ PreservesABI s t ∧
      MemoryWriteFrame s t #v[
        (⟨(stackPtr initial - BitVec.ofNat 64 (form.finalMemory.hash +
          (127 - message.size % 128))).toNat, 127 - message.size % 128⟩ : MemoryRegion),
        (⟨(stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8)).toNat, 8⟩ : MemoryRegion)] ∧
      MemoryWriteFrame s t #v[Stack.region initial form.stackBytes] ∧
      (¬ form.isTerminal → v.countValue form initial t = v.countValue form initial s) := by
  have tailBound : message.size % 128 < 128 := Nat.mod_lt _ (by decide)
  have layout : 64 ≤ form.finalMemory.hash ∧
      form.finalMemory.hash + 128 = form.finalMemory.buffer ∧
      form.finalMemory.buffer ≤ form.frameBytes := by
    cases form with
    | slices | digest => decide
    | reset _ => change 64 ≤ 296 ∧ 296 + 128 = 424 ∧ 424 ≤ 424; decide
    | finalizeIntoReset b | traitFinalizeIntoReset b => cases b <;> decide
  obtain ⟨t, run, state, rip, rsp, zero, abi, frame⟩ := fill_local ctx input.toState
    input.rip input.rsp input.destination input.zero input.count (by omega)
  have bytes {offset len : Nat} (low : offset ≤ form.frameBytes) (high : len ≤ offset)
      (apart : form.finalMemory.hash + (127 - message.size % 128) + len ≤ offset ∨
        offset + (127 - message.size % 128) ≤ form.finalMemory.hash + (127 - message.size % 128)) :
      ∀ i < len, t.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
        s.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? :=
    Absorb.frame_bytes (reserve := form.frameBytes + 8) ctx
      (by simpa only [Nat.add_sub_cancel_left] using frame)
      (by omega) (by omega) (by omega)
      (by cases form <;> dsimp only [Form.frameBytes, Form.stackBytes] <;> decide)
      low high apart
  have budget : form.frameBytes + 8 ≤ form.stackBytes := by
    cases form <;> dsimp only [Form.frameBytes, Form.stackBytes] <;> decide
  have stackFrame : MemoryWriteFrame s t #v[Stack.region initial form.stackBytes] := by
    have within (offset len : Nat) (lo : offset ≤ form.stackBytes) (hi : len ≤ offset + 8)
        (a : Nat) (ha : (⟨(stackPtr initial - BitVec.ofNat 64 offset).toNat, len⟩ : MemoryRegion).Contains a) :
        (Stack.region initial form.stackBytes).Contains a := by
      have stackLow : form.stackBytes ≤ (stackPtr initial).toNat := (Dispatch.stack_bounds512 ctx).1
      change (stackPtr initial - BitVec.ofNat 64 offset).toNat ≤ a ∧
        a < (stackPtr initial - BitVec.ofNat 64 offset).toNat + len at ha
      rw [Dispatch.stack_sub_toNat512 ctx lo] at ha
      exact Wrapper.stack_region_contains_of_bounds (by omega) (by omega)
    intro a outside
    apply frame a
    intro region member contains
    have choices : region = (⟨(stackPtr initial - BitVec.ofNat 64
          (form.finalMemory.hash + (127 - message.size % 128))).toNat,
          127 - message.size % 128⟩ : MemoryRegion) ∨
        region = (⟨(stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8)).toNat, 8⟩ : MemoryRegion) := by
      simpa using member
    apply outside (Stack.region initial form.stackBytes) (by simp)
    rcases choices with rfl | rfl
    · exact within _ _ (by omega) (by omega) _ contains
    · exact within _ _ budget (by omega) _ contains
  have countKept : ¬ form.isTerminal → v.countValue form initial t = v.countValue form initial s := by
    intro nonterminal
    cases form with
    | slices | digest => exact (nonterminal trivial).elim
    | reset stage =>
      have counts : ∀ stage : Fin 3, (v.traversal (.reset stage)).countReg = some 12 := by
        cases v <;> decide +kernel
      simp only [Variant.countValue, counts]
      exact abi.1 .r12 (by simp)
    | finalizeIntoReset second =>
      cases second
      · cases v
        · exact abi.1 .r12 (by simp)
        · exact abi.1 .r12 (by simp)
        · exact abi.1 .r15 (by simp)
        · exact abi.1 .r15 (by simp)
      · exact (nonterminal rfl).elim
    | traitFinalizeIntoReset second =>
      cases second
      · have kept := bytes (offset := 640) (len := 8) (by decide) (by decide)
          (.inl (by change 264 + (127 - message.size % 128) + 8 ≤ 640; omega))
        have slot : (v.traversal (.traitFinalizeIntoReset false)).countReg = none ∧
            (v.traversal (.traitFinalizeIntoReset false)).countSlot = some 640 := by
          cases v <;> decide
        simp only [Variant.countValue, slot.1, slot.2, Option.getD_some]
        apply memLoad_congr
        intro i hi
        exact congrArg (fun x : Option UInt8 => x.getD 0) (kept i hi)
      · exact (nonterminal rfl).elim
  have saves (eligible : form.twoOutputs = true) (slot : Nat)
      (member : slot ∈ [form.outputSlot, form.secondOutputSlot, form.pointerSlot, form.lengthSlot]) :
      slot ≤ form.frameBytes ∧ 8 ≤ slot ∧
        (form.finalMemory.buffer + 7 ≤ slot ∨ slot ≤ form.finalMemory.hash) := by
    cases form with
    | slices | digest => contradiction
    | reset _ | finalizeIntoReset _ | traitFinalizeIntoReset _ =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      all_goals
        simp only [Form.outputSlot, Form.secondOutputSlot, Form.pointerSlot, Form.lengthSlot,
          Form.frameBytes, Form.finalMemory, ResetLayout.resetMemory, ResetLayout.finalizeMemory,
          ResetLayout.cloneMemory]
        all_goals first | omega | (split <;> simp_all)
        all_goals omega
  have preserved : Preserved v initial t form := by
    refine Absorb.preserved_of_bytes input.toPreserved state ?_ ?_ ?_
    · cases form with
      | slices =>
        rintro a ⟨i, hi, rfl⟩
        exact bytes (offset := 624) (len := 24) (by decide) (by decide)
          (.inl (by dsimp [Form.finalMemory]; omega)) i hi
      | digest => trivial
      | reset stage | finalizeIntoReset second | traitFinalizeIntoReset second =>
        intro slot member a covers
        have hs := saves rfl slot member
        rcases covers with ⟨i, hi, rfl⟩
        exact bytes hs.1 hs.2.1 (by rcases hs.2.2 with h | h <;> omega) i hi
    · intro hd
      exact abi.1 .rbx (by simp)
    · intro hf
      left
      exact abi.1 _ (by cases v <;> simp)
  have hashBytes := bytes (offset := form.finalMemory.hash) (len := 64)
    (by omega) (by omega) (.inr (by omega))
  have tailBytes := bytes (offset := form.finalMemory.buffer) (len := message.size % 128 + 1)
    (by omega) (by omega) (.inl (by omega))
  refine ⟨t, run, ⟨⟨⟨preserved, Absorb.hashState_of_bytes input.hashWords hashBytes, ?_⟩,
    ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, abi, frame, stackFrame, countKept⟩
  · cases form with
    | slices | digest => exact (abi.1 .r14 (by simp)).trans input.hashPointer
    | reset _ => trivial
    | finalizeIntoReset b =>
      cases b
      · trivial
      · exact (abi.1 .rbx (by simp)).trans input.hashPointer
    | traitFinalizeIntoReset b =>
      cases b
      · exact ⟨(abi.1 _ (by cases v <;> simp)).trans input.hashPointer.1,
          (abi.1 _ (by cases v <;> simp)).trans input.hashPointer.2⟩
      · exact (abi.1 .rbx (by simp)).trans input.hashPointer
  · exact (abi.1 _ (by cases form <;> cases v <;> simp only [lowCountRegister] <;> (try split) <;> simp)).trans input.blocks
  · exact (abi.1 _ (by cases form <;> cases v <;> simp only [highCountRegister] <;> (try split) <;> simp)).trans input.blocksHigh
  · exact (abi.1 _ (by cases form <;> cases v <;> simp only [tailRegister] <;> (try split) <;> simp)).trans input.tailLength
  · have pc : branchOffset v form = fillOffset v form + 6 := by
      cases form <;> cases v <;> simp only [branchOffset, fillOffset] <;> (try split) <;> rfl
    simpa only [pc] using rip
  · apply padded_bytes
    · refine ⟨input.tailBytes.1, ?_⟩
      intro i
      have hi : i.val < message.size % 128 := by simpa only [remainderBytes_size] using i.isLt
      change t.external[BitVec.ofNat 64 ((stackPtr initial - BitVec.ofNat 64 form.finalMemory.buffer).toNat + i.val)]? = _
      rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, tailBytes i.val (by omega)]
      simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using input.tailBytes.2 i
    · exact (tailBytes _ (by omega)).trans input.marker
    · intro i hi
      have byte := zero i hi
      have h : form.finalMemory.buffer = (form.finalMemory.hash + (127 - message.size % 128)) +
          (message.size % 128 + 1) := by omega
      have address : stackPtr initial - BitVec.ofNat 64 (form.finalMemory.hash + (127 - message.size % 128)) =
          stackPtr initial - BitVec.ofNat 64 form.finalMemory.buffer + BitVec.ofNat 64 (message.size % 128 + 1) := by
        rw [h, BitVec.ofNat_add (form.finalMemory.hash + (127 - message.size % 128)) (message.size % 128 + 1)]
        simp only [← BitVec.sub_sub, BitVec.sub_add_cancel]
      rw [address] at byte
      simpa only [BitVec.ofNat_add, BitVec.add_assoc] using byte
  · exact (abi.1 _ (by cases form <;> cases v <;> simp only [paddingRegister] <;> (try split) <;> simp)).trans input.paddingLength

theorem finish [Bindings] {v : Variant} {form : Form} {initial s : RamState}
    {inputs : Array Input} {message : ByteArray}
    (ctx : Context v initial inputs form) (input : FillReady v initial s message form)
    (_eligible : form = .slices ∨ form = .digest := by first | assumption | simp) :
    ∃ t, Padded v initial t message form := by
  obtain ⟨t, _, padded, _, _⟩ := finish_local ctx input
  exact ⟨t, padded⟩

end Sha2.Proofs.Wrapper512.Hash.Finalize.Pad
