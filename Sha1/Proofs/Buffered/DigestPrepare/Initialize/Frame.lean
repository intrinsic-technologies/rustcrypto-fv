import Sha1.Proofs.Buffered.DigestPrepare.Contracts
import Sha1.Proofs.Buffered.DigestPrepare.Initialize.Store8
import Sha1.Proofs.Compress.Machine.Execution
import Sha1.Proofs.Compress.Machine.Code
import Sha1.Proofs.Common.Instructions.MovStore.Stack
import Sha1.Proofs.Common.Instructions.MovStore.Triple
import X86Proofs.Instructions.Sub.Generated.Imm32.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Triple

namespace Sha1.Proofs.Buffered.DigestPrepare.Initialize

open Sha1.Spec Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Compress.Machine

structure PrologueFrame (entry : BitVec 64) (budget : Nat) (s : RamState) : Prop where
  rip : s.RIP = entry
  stack : Stack.Valid s budget
  avoids : (Stack.region s budget).Avoids
    (fun address ↦ InProgram address ∨ InPageTables address)

theorem PrologueFrame.slot_toNat {entry : BitVec 64} {budget : Nat} {s : RamState}
    (h : PrologueFrame entry budget s) (offset : Nat) (ho : offset ≤ budget) :
    (stackPtr s - BitVec.ofNat 64 offset).toNat = (stackPtr s).toNat - offset := by
  have hstack := h.stack.2.2.1
  change budget ≤ (stackPtr s).toNat at hstack
  have hlt := (stackPtr s).isLt
  have hoffset : offset < 2^64 := Nat.lt_of_le_of_lt (Nat.le_trans ho hstack) hlt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoffset]
  omega

theorem PrologueFrame.slot_contains {entry : BitVec 64} {budget : Nat} {s : RamState}
    (h : PrologueFrame entry budget s) (offset len : Nat) (ho : offset ≤ budget)
    (hl : len ≤ offset + 8) (i : Nat) (hi : i < len) :
    (Stack.region s budget).Contains
      (stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat := by
  have hb := h.stack.1
  have hu := h.stack.2.2.1
  change budget ≤ (stackPtr s).toNat at hu
  change (stackPtr s).toNat - budget +
    ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - budget)) < 2^32 at hb
  rw [BitVec.toNat_add, h.slot_toNat offset ho, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  change (stackPtr s).toNat - budget ≤ _ ∧
    _ < (stackPtr s).toNat - budget +
      ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - budget))
  constructor <;> omega

theorem PrologueFrame.writable {entry : BitVec 64} {budget : Nat} {s : RamState}
    (h : PrologueFrame entry budget s) (offset len : Nat) (ho : offset ≤ budget)
    (hl : len ≤ offset + 8) :
    Sha1.Proofs.Common.Instructions.StorePre.MemWritable s
      (stackPtr s - BitVec.ofNat 64 offset) len := by
  refine ⟨?_, ?_, ?_⟩
  · have hb := h.stack.1
    have hu := h.stack.2.2.1
    change budget ≤ (stackPtr s).toNat at hu
    rw [h.slot_toNat offset ho]
    change (stackPtr s).toNat - budget +
      ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - budget)) < 2^32 at hb
    omega
  · intro i hi
    exact Option.isSome_iff_exists.mpr (h.stack.2.1 _ (h.slot_contains offset len ho hl i hi))
  · intro i hi hin
    exact h.avoids _ (h.slot_contains offset len ho hl i hi) (.inr hin)

theorem PrologueFrame.avoids_mem {entry : BitVec 64} {budget : Nat} {s : RamState}
    (h : PrologueFrame entry budget s) (offset len : Nat) (ho : offset ≤ budget)
    (hl : len ≤ offset + 8) :
    ∀ x ∈ Extracted.programImage,
      ¬ (Component.mem (stackPtr s - BitVec.ofNat 64 offset) len).Covers x.1 := by
  intro x hx ⟨i, hi, he⟩
  apply h.avoids x.1
  · rw [he]
    exact h.slot_contains offset len ho hl i hi
  · exact .inl ⟨x.2, hx⟩

theorem PrologueFrame.apart {entry : BitVec 64} {budget : Nat} {s : RamState}
    (h : PrologueFrame entry budget s) (offset len : Nat) (ho : offset ≤ budget)
    (hl : len ≤ offset + 8) (p : BitVec 64) (bytes : List UInt8)
    (hSub : ∀ x ∈ codeRange p bytes, x ∈ Extracted.programImage) :
    RangeApart (stackPtr s - BitVec.ofNat 64 offset) len p bytes.length := by
  intro i hi j hj he
  exact h.avoids_mem offset len ho hl _ (hSub _ (mem_codeRange p bytes j hj))
    ⟨i, hi, he.symm⟩

theorem PrologueFrame.covers_in_stack {entry : BitVec 64} {budget : Nat} {s : RamState}
    (h : PrologueFrame entry budget s) (offset len : Nat) (ho : offset ≤ budget)
    (hl : len ≤ offset) {address : BitVec 64}
    (hc : (Component.mem (stackPtr s - BitVec.ofNat 64 offset) len).Covers address) :
    (⟨(Stack.region s budget).start, budget⟩ : MemoryRegion).Contains address.toNat := by
  obtain ⟨i, hi, rfl⟩ := hc
  have hu := h.stack.2.2.1
  change budget ≤ (stackPtr s).toNat at hu
  have hb := h.stack.1
  change (stackPtr s).toNat - budget +
    ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - budget)) < 2^32 at hb
  rw [BitVec.toNat_add, h.slot_toNat offset ho, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  change (stackPtr s).toNat - budget ≤ _ ∧
    _ < (stackPtr s).toNat - budget + budget
  constructor <;> omega

theorem prologue_text_sub (offset count : Nat) (h : offset + count ≤ Extracted.textBytes.size) :
    ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 offset)
      (Extracted.textBytes.toListFrom offset count), x ∈ Extracted.programImage := by
  intro x hx
  rw [← chunked_toList_slice _ _ _ h] at hx
  exact List.mem_flatMap.mpr ⟨⟨Extracted.textAddress, Extracted.textBytes⟩,
    by simp only [Extracted.programSections, List.mem_cons, true_or],
    codeRange_slice_subset _ _ offset count x hx⟩

theorem text_address_ne_return {boundary : ReturnBoundary} (hOutside : ¬ InProgram boundary.rip)
    (offset : Nat) (h : offset < Extracted.textBytes.size) :
    Extracted.textAddress + BitVec.ofNat 64 offset ≠ boundary.rip := by
  intro hEq
  exact hOutside (hEq ▸ text_address_in_program offset h)

theorem prologue_covers_of_contains {region : MemoryRegion} {address : BitVec 64}
    (h : region.Contains address.toNat) :
    (Component.mem (BitVec.ofNat 64 region.start) region.size).Covers address := by
  refine ⟨address.toNat - region.start, ?_, ?_⟩
  · unfold MemoryRegion.Contains at h
    omega
  · rw [← BitVec.ofNat_add, Nat.add_sub_cancel' h.1,
      BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem memReadable_of_allocated {s : RamState} {region : MemoryRegion}
    {addr : BitVec 64} {len : Nat} (h : region.Allocated s.external)
    (hlow : addr.toNat + len ≤ userAddressLimit)
    (hstart : region.start ≤ addr.toNat)
    (hend : addr.toNat + len ≤ region.start + region.size) :
    MemReadable s addr len := by
  refine ⟨hlow, ?_⟩
  intro i hi
  apply Option.isSome_iff_exists.mpr
  apply h
  have hi64 : i < 2^64 := by unfold userAddressLimit at hlow; omega
  have hsum : addr.toNat + i < 2^64 := by unfold userAddressLimit at hlow; omega
  simp only [MemoryRegion.Contains, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hi64, Nat.mod_eq_of_lt hsum]
  omega

theorem stack_return_readable {s : RamState} {bytes : Nat}
    (h : Stack.Valid s bytes) : MemReadable s (stackPtr s) 8 := by
  rcases h with ⟨hb, ha, hn, _⟩
  have hstart : (Stack.region s bytes).start ≤ (stackPtr s).toNat := by
    change (s.regValue .rsp).toNat - bytes ≤ (s.regValue .rsp).toNat
    omega
  have hend : (Stack.region s bytes).start + (Stack.region s bytes).size =
      (stackPtr s).toNat + 8 := by
    change ((s.regValue .rsp).toNat - bytes) +
      ((s.regValue .rsp).toNat + 8 - ((s.regValue .rsp).toNat - bytes)) =
      (s.regValue .rsp).toNat + 8
    omega
  apply memReadable_of_allocated ha
  · change (Stack.region s bytes).start + (Stack.region s bytes).size < userAddressLimit at hb
    omega
  · exact hstart
  · omega

theorem absorbed_empty_of_initial_words {s : RamState} (base : BitVec 64)
    (hReadable : MemReadable s (base + 72) 20)
    (hLow : (Operand.mem (base + 72) : Operand 64).read s = 0xefcdab8967452301)
    (hMid : (Operand.mem (base + 80) : Operand 64).read s = 0x1032547698badcfe)
    (hHigh : (Operand.mem (base + 88) : Operand 32).read s = 0xc3d2e1f0)
    (hPosition : (Operand.mem (base + 63) : Operand 8).read s = 0)
    (hBlocks : (Operand.mem (base + 64) : Operand 64).read s = 0) :
    Absorbed base ByteArray.empty s := by
  have hA := Bytes.of_memLoad (n := 64) (m := s.external) (a := base + 72)
    (fun i hi ↦ hReadable.mem i (by omega))
  change Bytes s.external (base + 72) 8
    (storedByte ((Operand.mem (base + 72) : Operand 64).read s)) at hA
  rw [hLow] at hA
  have hBPresent : ∀ i < 64 / 8,
      (s.external[(base + 72) + BitVec.ofNat 64 8 + BitVec.ofNat 64 i]?).isSome := by
    intro i hi
    simpa only [BitVec.add_assoc, BitVec.ofNat_add] using hReadable.mem (8 + i) (by omega)
  have hB := Bytes.of_memLoad (n := 64) hBPresent
  change Bytes s.external ((base + 72) + BitVec.ofNat 64 8) 8
    (storedByte ((Operand.mem ((base + 72) + 8) : Operand 64).read s)) at hB
  rw [show (base + 72) + (8 : BitVec 64) = base + 80 by rw [BitVec.add_assoc]; rfl, hMid] at hB
  have hCPresent : ∀ i < 32 / 8,
      (s.external[(base + 72) + BitVec.ofNat 64 16 + BitVec.ofNat 64 i]?).isSome := by
    intro i hi
    simpa only [BitVec.add_assoc, BitVec.ofNat_add] using hReadable.mem (16 + i) (by omega)
  have hC := Bytes.of_memLoad (n := 32) hCPresent
  change Bytes s.external ((base + 72) + BitVec.ofNat 64 16) 4
    (storedByte ((Operand.mem ((base + 72) + 16) : Operand 32).read s)) at hC
  rw [show (base + 72) + (16 : BitVec 64) = base + 88 by rw [BitVec.add_assoc]; rfl, hHigh] at hC
  have hAB := hA.append (by
    simpa only [BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using hB)
  have hW := hAB.append (count := 4) (by
    simpa only [BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Nat.reduceAdd]
      using hC)
  have hValues : ∀ i : Fin 20,
      (if i.val < 8 + 8 then
          (if i.val < 8 then storedByte (0xefcdab8967452301 : BitVec 64) i.val
            else storedByte (0x1032547698badcfe : BitVec 64) (i.val - 8))
        else storedByte (0xc3d2e1f0 : BitVec 32) (i.val - (8 + 8))) =
      (absorbedStateBytes ByteArray.empty).data.toList.getD i.val 0 := by
    decide +kernel
  have hSize : (absorbedStateBytes ByteArray.empty).size = 20 :=
    Sha1.Proofs.Wrapper.Hash.Serialize.stateBytes_size _
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨by simp only [MemoryRegion.HasLength, hSize], ?_⟩
    intro i
    have hi : i.val < 20 := hSize ▸ i.isLt
    have hm := (hW i.val (by omega)).trans (congrArg some (hValues ⟨i.val, hi⟩))
    change s.external[BitVec.ofNat 64 ((base + 72).toNat + i.val)]? = _
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, hm]
    congr 1
    simp [ByteArray.getElem_eq_getElem_data, List.getD_eq_getElem?_getD]
  · change (⟨base.toNat, (tailBytes ByteArray.empty).size⟩ : MemoryRegion).HasBytes s.external
      (tailBytes ByteArray.empty)
    have h0 : (tailBytes ByteArray.empty).size = 0 := by simp
    refine ⟨h0, fun i ↦ absurd i.isLt (by omega)⟩
  · simpa using hPosition
  · simpa using hBlocks

end Sha1.Proofs.Buffered.DigestPrepare.Initialize
