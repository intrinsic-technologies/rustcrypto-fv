import P256.Proofs.Program.Compare.Frame.Prologue
import P256.Proofs.Program.Compare.Prefix
import P256.Proofs.Program.Compare.Length

namespace P256.Proofs.Program.Compare

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Spec.Program P256.Spec.Program.Routines

def workingChanges (s : RamState) : List Component :=
  callChanges s ++ [.reg 3, .reg 5, .reg 12, .reg 14, .reg 15]

theorem working_trans {initial s t : RamState}
    (h : AgreesExcept (workingChanges initial) initial s)
    (h' : AgreesExcept (workingChanges initial) s t) :
    AgreesExcept (workingChanges initial) initial t :=
  (h.trans h').mono (by simp)

theorem stack_slot_covers {sp x : BitVec 64} {offset len budget : Nat}
    (hoff : offset ≤ budget) (hlen : len ≤ offset)
    (h : (Component.mem (sp - BitVec.ofNat 64 offset) len).Covers x) :
    (Component.mem (sp - BitVec.ofNat 64 budget) budget).Covers x := by
  obtain ⟨i, hi, rfl⟩ := h
  refine ⟨budget - offset + i, by omega, ?_⟩
  have he : sp - BitVec.ofNat 64 budget + BitVec.ofNat 64 (budget - offset) =
      sp - BitVec.ofNat 64 offset := by
    have hb : BitVec.ofNat 64 budget =
        BitVec.ofNat 64 offset + BitVec.ofNat 64 (budget - offset) := by
      rw [← BitVec.ofNat_add, Nat.add_sub_of_le hoff]
    rw [hb, ← BitVec.sub_sub, BitVec.sub_add_cancel]
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, he]

theorem prologue_working {s t : RamState} (h : (Frame.prologueEffect s).Holds s t) :
    AgreesExcept (workingChanges s) s t := by
  apply h.agrees.widen
  · intro c hc hm
    simp only [Frame.prologueEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component_mem, Write.component_reg, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, or_assoc] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | contradiction | simp [workingChanges, callChanges]
  · intro x c hc hcov
    simp only [Frame.prologueEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component_mem, Write.component_reg, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, or_assoc] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcov.elim
    all_goals refine ⟨.mem (stackPtr s - 64) 64, by simp [workingChanges, callChanges], ?_⟩
    · exact stack_slot_covers (offset := 8) (by decide) (by decide) hcov
    · exact stack_slot_covers (offset := 16) (by decide) (by decide) hcov
    · exact stack_slot_covers (offset := 24) (by decide) (by decide) hcov
    · exact stack_slot_covers (offset := 32) (by decide) (by decide) hcov
    · exact stack_slot_covers (offset := 40) (by decide) (by decide) hcov

theorem input_byte_of_working {initial s t : RamState} {address : BitVec 64} {length : Nat}
    (h : AgreesExcept (workingChanges initial) s t)
    (ha : RangeApart (stackPtr initial - 64) 64 address length) {i : Nat} (hi : i < length) :
    t.external[address + BitVec.ofNat 64 i]? = s.external[address + BitVec.ofNat 64 i]? := by
  apply h.byte
  intro c hc hcov
  simp only [workingChanges, callChanges, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
    (rfl | rfl | rfl | rfl | rfl)
  all_goals try exact hcov.elim
  obtain ⟨j, hj, he⟩ := hcov
  exact ha j hj i hi he.symm

theorem bytesEqual_working_iff {initial s t : RamState} {left right : BitVec 64} {length : Nat}
    (h : AgreesExcept (workingChanges initial) s t)
    (hl : RangeApart (stackPtr initial - 64) 64 left length)
    (hr : RangeApart (stackPtr initial - 64) 64 right length) :
    BytesEqual t left right length ↔ BytesEqual s left right length := by
  unfold BytesEqual
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  change (t.external[left + BitVec.ofNat 64 i]?).getD 0 =
      (t.external[right + BitVec.ofNat 64 i]?).getD 0 ↔ _
  rw [input_byte_of_working h hl hi, input_byte_of_working h hr hi]
  rfl

theorem working_calleeSaved {s t : RamState} (h : AgreesExcept (workingChanges s) s t)
    (hs : CalleeSavedRegistersUnchanged s t) : AgreesExcept (callChanges s) s t := by
  apply h.narrow
  intro c hc hn
  simp only [workingChanges, List.mem_append] at hc
  rcases hc with hc | hc
  · exact False.elim (hn hc)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    · exact hs .rbx (by decide)
    · exact hs .rbp (by decide)
    · exact hs .r12 (by decide)
    · exact hs .r14 (by decide)
    · exact hs .r15 (by decide)

theorem working_return_word {s t : RamState} (h : AgreesExcept (workingChanges s) s t) :
    (Operand.mem (stackPtr s) : Operand 64).read t = (returnBoundary s).rip := by
  have apart : RangeApart (stackPtr s - 64) 64 (stackPtr s) 8 := by
    have ho : OffsetsApart (-64) 64 0 8 := by unfold OffsetsApart; decide +kernel
    intro i hi j hj
    simpa [BitVec.sub_eq_add_neg] using ho.ne (stackPtr s) hi hj (by decide +kernel)
  apply memLoad_congr
  intro i hi
  change (t.external[stackPtr s + BitVec.ofNat 64 i]?).getD 0 =
    (s.external[stackPtr s + BitVec.ofNat 64 i]?).getD 0
  rw [input_byte_of_working h apart hi]

theorem prefix_pre_of_prologue [Bindings] {s t : RamState} (hp : CallPre s)
    (h : (Frame.prologueEffect s).Holds s t) : PrefixPre t := by
  obtain ⟨_, _, _, _, _, _, _, h1, h2, h6, h8⟩ := h.writes
  have hlen : mainLength t = ((Operand.reg 2 : Operand 64).read s).toNat :=
    congrArg BitVec.toNat h1
  refine ⟨h.rip, ?_, ?_, ?_, ?_⟩
  · rw [h8]
    apply BitVec.eq_of_toNat_eq
    rw [aligned_length]
    change 16 * (((Operand.reg 2 : Operand 64).read s).toNat / 16) =
      prefixLength t % 2^64
    rw [prefixLength, hlen]
    have := hp.left.low
    omega
  · rw [h8]
    exact h.flags.2.2.2.1
  · rw [h6, hlen]
    exact hp.left.of_holds h
  · rw [h2, hlen]
    exact hp.right.of_holds h

theorem prologue_equal_iff [Bindings] {initial s : RamState} (hp : CallPre initial)
    (he : (Frame.prologueEffect initial).Holds initial s) :
    BytesEqual s ((Operand.reg 6 : Operand 64).read s)
      ((Operand.reg 2 : Operand 64).read s) (mainLength s) ↔
    BytesEqual initial ((Operand.reg 7 : Operand 64).read initial)
      ((Operand.reg 6 : Operand 64).read initial) ((Operand.reg 2 : Operand 64).read initial).toNat := by
  obtain ⟨_, _, _, _, _, _, _, h1, h2, h6, _⟩ := he.writes
  have hlen : mainLength s = ((Operand.reg 2 : Operand 64).read initial).toNat :=
    congrArg BitVec.toNat h1
  rw [h6, h2, hlen]
  exact bytesEqual_working_iff (prologue_working he) hp.stackLeft hp.stackRight

theorem tail_prepare_length {s t : RamState} (h : (tailPrepareEffect s).Holds s t) :
    mainLength t = mainLength s % 16 := by
  dsimp only [mainLength]
  rw [h.writes.1]
  have he : (Operand.reg 1 : Operand 32).read s =
      ((Operand.reg 1 : Operand 64).read s).setWidth 32 := by simp [Operand.read]
  rw [he]
  exact remaining_length _

end P256.Proofs.Program.Compare
