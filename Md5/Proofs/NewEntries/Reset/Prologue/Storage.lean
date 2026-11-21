import Md5.Proofs.NewEntries.Reset.Prologue.Init

namespace Md5.Proofs.NewEntries.Reset

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Md5.Proofs Md5.Proofs.Block Md5.Proofs.Streaming

private theorem stackPtr_read (s : RamState) :
    stackPtr s = (Operand.reg 4 : Operand 64).read s := rfl

attribute [local x86_compose] stackPtr_read BitVec.sub_eq_add_neg

def resetPrologueChanges (s : RamState) (budget : Nat) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 4, .reg 5, .reg 7, .reg 12, .reg 14, .reg 15, .flags, .rip,
    .mem (BitVec.ofNat 64 (Stack.region s budget).start) budget]

structure ResetInitialized (initial final : RamState) : Prop extends
    PrologueStorage 312 32 288 16 24 680 .r8 initial final where
  absorbed : Buffered.Absorbed (stackPtr final + 32) ByteArray.empty final
  agrees : AgreesExcept (resetPrologueChanges initial 680) initial final
  memoryFrame : MemoryWriteFrame initial final #v[Stack.region initial 680]

theorem reset_prologue_memoryFrame {entry : BitVec 64} {budget : Nat} {s t : RamState}
    (hFrame : PrologueFrame entry budget s)
    (h : AgreesExcept (resetPrologueChanges s budget) s t) :
    MemoryWriteFrame s t #v[Stack.region s budget] := by
  apply h.memoryWriteFrame
  intro c hc address hcov
  simp only [resetPrologueChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    try exact False.elim hcov
  have hContains := contains_of_mem_covers hFrame.tight_bounded hcov
  refine ⟨Stack.region s budget, by simp, ?_⟩
  have hu := hFrame.stack.2.2.1
  change budget ≤ (stackPtr s).toNat at hu
  change (stackPtr s).toNat - budget ≤ address.toNat ∧
    address.toNat < (stackPtr s).toNat - budget + budget at hContains
  change (stackPtr s).toNat - budget ≤ address.toNat ∧
    address.toNat < (stackPtr s).toNat - budget +
      ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - budget))
  constructor <;> omega

theorem reset_prologue_return_read {entry : BitVec 64} {budget : Nat} {s t : RamState}
    (hFrame : PrologueFrame entry budget s)
    (h : AgreesExcept (resetPrologueChanges s budget) s t) :
    (Operand.mem (stackPtr s) : Operand 64).read t =
      (Operand.mem (stackPtr s) : Operand 64).read s := by
  apply memLoad_congr
  intro i hi
  have hbyte : t.external[stackPtr s + BitVec.ofNat 64 i]? =
      s.external[stackPtr s + BitVec.ofNat 64 i]? := by
    apply h.byte
    intro c hc hcov
    simp only [resetPrologueChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      try exact False.elim hcov
    have hContains := contains_of_mem_covers hFrame.tight_bounded hcov
    have hu := hFrame.stack.2.2.1
    change budget ≤ (stackPtr s).toNat at hu
    have hb := hFrame.stack.1
    change (stackPtr s).toNat - budget +
      ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - budget)) < 2^32 at hb
    change (stackPtr s).toNat - budget ≤ _ ∧
      _ < (stackPtr s).toNat - budget + budget at hContains
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)] at hContains
    omega
  change (t.external[stackPtr s + BitVec.ofNat 64 i]?).getD 0 =
    (s.external[stackPtr s + BitVec.ofNat 64 i]?).getD 0
  rw [hbyte]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
theorem reset_initialized_common {s t : RamState}
    (hFrame : PrologueFrame 0x101340 680 s)
    (hE : (Effect.seq (prologuePushEffect 0x101340) resetInitEffect s).Holds s t) :
    ResetInitialized s t := by
  have hWrites := hE.writes
  x86_norm [prologuePushEffect, resetInitEffect] at hWrites
  rcases hWrites with ⟨h5, h15, h14, h13, h12, h3, hsp, hout, hbound, hlen, hptr, hdx,
    hhigh, hdi, hlow, hblocks, hposition⟩
  simp only [Write.AllHold] at hposition
  have hRsp : stackPtr t = stackPtr s - 360 := by
    simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
      BitVec.reduceNeg] using hsp
  have hAgrees : AgreesExcept (resetPrologueChanges s 680) s t := by
    apply hE.agrees.widen
    · intro c hc hm
      cases c with
      | reg r =>
        x86_norm [prologuePushEffect, resetInitEffect] at hc
        rcases hc with rfl | rfl | rfl | rfl <;> simp [resetPrologueChanges]
      | mem a len => cases hm
      | flags => simp [resetPrologueChanges]
      | rip => simp [resetPrologueChanges]
      | _ => x86_norm [prologuePushEffect, resetInitEffect] at hc
    · intro address c hc hcov
      have hContains : (⟨(Stack.region s 680).start,
          680⟩ : MemoryRegion).Contains address.toNat := by
        x86_norm [prologuePushEffect, resetInitEffect] at hc
        rcases hc with hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc <;> subst c
        · apply hFrame.covers_in_stack 8 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · apply hFrame.covers_in_stack 16 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · apply hFrame.covers_in_stack 24 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · apply hFrame.covers_in_stack 32 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · apply hFrame.covers_in_stack 40 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · apply hFrame.covers_in_stack 48 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · exact False.elim hcov
        · apply hFrame.covers_in_stack 72 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · exact False.elim hcov
        · apply hFrame.covers_in_stack 336 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · apply hFrame.covers_in_stack 344 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · exact False.elim hcov
        · apply hFrame.covers_in_stack 256 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · exact False.elim hcov
        · apply hFrame.covers_in_stack 264 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · apply hFrame.covers_in_stack 248 8 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · apply hFrame.covers_in_stack 265 1 (by decide +kernel) (by decide)
          simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
            BitVec.reduceNeg] using hcov
        · exact False.elim hcov
        · exact False.elim hcov
      exact ⟨.mem (BitVec.ofNat 64 (Stack.region s 680).start)
        680,
        by simp only [resetPrologueChanges, List.mem_cons, List.not_mem_nil, or_false, or_true],
        prologue_covers_of_contains
          (region := ⟨(Stack.region s 680).start,
            680⟩) hContains⟩
  refine {
    rsp := hRsp
    absorbed := ?absorbed
    saved := ?saved
    output := ?output
    pointer := ?pointer
    length := ?length
    returnSlot := ?returnSlot
    agrees := hAgrees
    memoryFrame := ?memoryFrame
  }
  case absorbed =>
    apply absorbed_empty_of_initial_words (stackPtr t + 32)
    · have hr := (hFrame.writable 264 16 (by decide +kernel) (by decide)).readable
      have ht : MemReadable t (stackPtr s - 264) 16 :=
        ⟨hr.low, fun i hi ↦ hE.agrees.grow _ (hr.mem i hi)⟩
      simpa only [hRsp, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using ht
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using hlow
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using hhigh
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using hposition
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using hblocks
  case saved =>
    intro i
    finite_cases i
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd, Fin.val_zero, Fin.val_succ,
        Nat.reduceAdd, Nat.reduceMul,
        show (#[3#5, 12#5, 13#5, 14#5, 15#5, 5#5] : Array (BitVec 5))[0] = 3#5 from by decide +kernel]
        using h3
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd, Fin.val_zero, Fin.val_succ,
        Nat.reduceAdd, Nat.reduceMul,
        show (#[3#5, 12#5, 13#5, 14#5, 15#5, 5#5] : Array (BitVec 5))[1] = 12#5 from by decide +kernel]
        using h12
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd, Fin.val_zero, Fin.val_succ,
        Nat.reduceAdd, Nat.reduceMul,
        show (#[3#5, 12#5, 13#5, 14#5, 15#5, 5#5] : Array (BitVec 5))[2] = 13#5 from by decide +kernel]
        using h13
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd, Fin.val_zero, Fin.val_succ,
        Nat.reduceAdd, Nat.reduceMul,
        show (#[3#5, 12#5, 13#5, 14#5, 15#5, 5#5] : Array (BitVec 5))[3] = 14#5 from by decide +kernel]
        using h14
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd, Fin.val_zero, Fin.val_succ,
        Nat.reduceAdd, Nat.reduceMul,
        show (#[3#5, 12#5, 13#5, 14#5, 15#5, 5#5] : Array (BitVec 5))[4] = 15#5 from by decide +kernel]
        using h15
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd, Fin.val_zero, Fin.val_succ,
        Nat.reduceAdd, Nat.reduceMul,
        show (#[3#5, 12#5, 13#5, 14#5, 15#5, 5#5] : Array (BitVec 5))[5] = 5#5 from by decide +kernel]
        using h5
  case output =>
    change (Operand.mem (stackPtr t + 288) : Operand 64).read t =
      (Operand.reg 8 : Operand 64).read s
    simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
      BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using hout
  case pointer =>
    change (Operand.mem (stackPtr t + 16) : Operand 64).read t =
      (Operand.reg 7 : Operand 64).read s
    simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
      BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using hptr
  case length =>
    change (Operand.mem (stackPtr t + 24) : Operand 64).read t =
      (Operand.reg 2 : Operand 64).read s
    simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
      BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using hlen
  case returnSlot =>
    simpa only [hRsp, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
      BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd, BitVec.add_zero, Nat.reduceAdd]
      using reset_prologue_return_read hFrame hAgrees
  case memoryFrame => exact reset_prologue_memoryFrame hFrame hAgrees


theorem reset_branch_storage {initial s t : RamState}
    (hFrame : PrologueFrame 0x101340 680 initial)
    (h : ResetInitialized initial s)
    (hTail : AgreesExcept [.reg 0, .reg 1, .reg 12, .reg 15, .flags, .mem (stackPtr s + 8) 8, .rip] s t) :
    ResetInitialized initial t := by
  have hNat : (stackPtr s).toNat = (stackPtr initial).toNat - 360 := by
    rw [h.rsp]
    exact hFrame.slot_toNat 360 (by decide +kernel)
  have hUpper : (stackPtr s).toNat + 368 < 2^32 := by
    have hb := hFrame.stack.1
    have hu := hFrame.stack.2.2.1
    change 680 ≤ (stackPtr initial).toNat at hu
    change (stackPtr initial).toNat - 680 +
      ((stackPtr initial).toNat + 8 -
        ((stackPtr initial).toNat - 680)) < 2^32 at hb
    omega
  have hAddress (offset : Nat) (ho : offset ≤ 368) :
      (stackPtr s + BitVec.ofNat 64 offset).toNat = (stackPtr s).toNat + offset := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show offset < 2^64 by omega),
      Nat.mod_eq_of_lt (show (stackPtr s).toNat + offset < 2^64 by omega)]
  have hContext : (stackPtr s + 32).toNat = (stackPtr s).toNat + 32 := by
    simpa only [BitVec.ofNat_eq_ofNat] using hAddress 32 (by decide)
  have hRsp : stackPtr t = stackPtr s := hTail.read (n := 64) (r := 4) (by simp)
  have hStoreFrame : MemoryWriteFrame s t #v[⟨(stackPtr s).toNat + 8, 8⟩] := by
    apply hTail.memoryWriteFrame
    intro c hc address hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try exact False.elim hcov
    · refine ⟨⟨(stackPtr s).toNat + 8, 8⟩, by simp, ?_⟩
      apply contains_of_mem_covers (by
        change (stackPtr s).toNat + 8 + 8 < 2^32
        omega)
      simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
        BitVec.ofNat_eq_ofNat] using hcov
  have hRead (offset bits : Nat) (ho : offset + bits / 8 ≤ 368)
      (hgap : offset + bits / 8 ≤ 8 ∨ 16 ≤ offset) :
      (Operand.mem (stackPtr s + BitVec.ofNat 64 offset) : Operand bits).read t =
        (Operand.mem (stackPtr s + BitVec.ofNat 64 offset) : Operand bits).read s := by
    apply memoryRead_of_memoryWriteFrame (region := ⟨(stackPtr s).toNat + offset, bits / 8⟩)
      hStoreFrame
    · change (stackPtr s).toNat + offset + bits / 8 < 2^32
      omega
    · rw [hAddress offset (by omega)]
      exact Nat.le_refl _
    · rw [hAddress offset (by omega)]
      exact Nat.le_refl _
    · intro r hr address ha hc
      have he : r = ⟨(stackPtr s).toNat + 8, 8⟩ := by simpa using hr
      subst r
      change (stackPtr s).toNat + offset ≤ address ∧
        address < (stackPtr s).toNat + offset + bits / 8 at ha
      change (stackPtr s).toNat + 8 ≤ address ∧
        address < (stackPtr s).toNat + 8 + 8 at hc
      omega
  have hTailWide : AgreesExcept (resetPrologueChanges initial 680) s t := by
    apply hTail.widen
    · intro c hc hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try cases hm
      all_goals simp [resetPrologueChanges]
    · intro address c hc hcov
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try exact False.elim hcov
      · have hcov' : (Component.mem (stackPtr initial - 352) 8).Covers address := by
          simpa only [h.rsp, BitVec.sub_eq_add_neg, BitVec.add_assoc,
            BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd, Nat.reduceAdd] using hcov
        exact ⟨.mem (BitVec.ofNat 64 (Stack.region initial 680).start)
          680, by simp [resetPrologueChanges],
          prologue_covers_of_contains (region :=
            ⟨(Stack.region initial 680).start,
              680⟩)
            (hFrame.covers_in_stack 352 8 (by decide +kernel) (by decide) hcov')⟩
  have hAgrees : AgreesExcept (resetPrologueChanges initial 680) initial t :=
    (h.agrees.trans hTailWide).mono (by simp)
  refine {
    rsp := hRsp.trans h.rsp
    saved := ?saved
    output := ?output
    pointer := ?pointer
    length := ?length
    returnSlot := ?returnSlot
    absorbed := ?absorbed
    agrees := hAgrees
    memoryFrame := reset_prologue_memoryFrame hFrame hAgrees
  }
  case saved =>
    intro i
    rw [hRsp]
    exact (hRead (312 + 8 * i.val) 64 (by have := i.isLt; omega) (by omega)).trans (h.saved i)
  case output =>
    rw [hRsp]
    exact (hRead 288 64 (by decide) (by decide)).trans h.output
  case pointer =>
    rw [hRsp]
    exact (hRead 16 64 (by decide) (by decide)).trans h.pointer
  case length =>
    rw [hRsp]
    exact (hRead 24 64 (by decide) (by decide)).trans h.length
  case returnSlot =>
    rw [hRsp]
    exact (hRead 360 64 (by decide) (by decide)).trans h.returnSlot
  case absorbed =>
    rw [hRsp]
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply Md5.Proofs.hasBytes_of_memoryWriteFrame hStoreFrame h.absorbed.buffer
      · change (stackPtr s + 32).toNat + 64 + 16 < 2^32
        rw [hContext]
        omega
      · intro r hr address ha hc
        have he : r = ⟨(stackPtr s).toNat + 8, 8⟩ := by simpa using hr
        subst r
        change (stackPtr s + 32).toNat + 64 ≤ address ∧
          address < (stackPtr s + 32).toNat + 64 + 16 at ha
        rw [hContext] at ha
        change (stackPtr s).toNat + 8 ≤ address ∧
          address < (stackPtr s).toNat + 8 + 8 at hc
        omega
    · change (⟨(stackPtr s + 32).toNat, 0⟩ : MemoryRegion).HasBytes t.external ByteArray.empty
      exact ⟨rfl, fun i ↦ Fin.elim0 i⟩
    · calc
        (Operand.mem (stackPtr s + 32 + 63) : Operand 8).read t =
            (Operand.mem (stackPtr s + 32 + 63) : Operand 8).read s := by
          simpa only [BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using
            hRead 95 8 (by decide) (by decide)
        _ = _ := h.absorbed.position
    · calc
        (Operand.mem (stackPtr s + 32 + 80) : Operand 64).read t =
            (Operand.mem (stackPtr s + 32 + 80) : Operand 64).read s := by
          simpa only [BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using
            hRead 112 64 (by decide) (by decide)
        _ = _ := h.absorbed.blocks


end Md5.Proofs.NewEntries.Reset
