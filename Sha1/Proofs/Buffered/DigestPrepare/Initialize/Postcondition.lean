import Sha1.Proofs.Buffered.DigestPrepare.Initialize.Model

namespace Sha1.Proofs.Buffered.DigestPrepare.Initialize

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

private theorem stackPtr_read (s : RamState) :
    stackPtr s = (Operand.reg 4 : Operand 64).read s := rfl

attribute [local x86_compose] stackPtr_read

theorem contains_of_mem_covers {region : MemoryRegion} (hBounded : region.Bounded)
    {address : BitVec 64}
    (hCovers : Component.Covers (.mem (BitVec.ofNat 64 region.start) region.size) address) :
    region.Contains address.toNat := by
  obtain ⟨i, hi, rfl⟩ := hCovers
  have hStart : region.start < 2^64 := by
    unfold MemoryRegion.Bounded userAddressLimit at hBounded
    omega
  have hIndex : i < 2^64 := by
    unfold MemoryRegion.Bounded userAddressLimit at hBounded
    omega
  have hSum : region.start + i < 2^64 := by
    unfold MemoryRegion.Bounded userAddressLimit at hBounded
    omega
  simp only [MemoryRegion.Contains, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hStart, Nat.mod_eq_of_lt hIndex, Nat.mod_eq_of_lt hSum]
  omega

theorem input_bytes_of_agrees [bindings : Bindings] {initial s : RamState} {input : ByteArray}
    (hCall : Digest.ValidCall bindings initial input)
    (hag : AgreesExcept (digestPreparationChanges initial) initial s) :
    (Digest.inputRegion initial input).HasBytes s.external input := by
  refine ⟨rfl, fun i ↦ ?_⟩
  apply Eq.trans _ (hCall.inputInMemory.2.2.2 i)
  apply hag.byte
  intro c hc hcov
  simp only [digestPreparationChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcov.elim
  have hx := contains_of_mem_covers hCall.stackAvailable.1 hcov
  have hd : (Digest.inputRegion initial input).Disjoint
      (Stack.region initial Digest.minStackBytes) :=
    (hCall.separation.2 _ (by simp)).1 _ (by simp)
  apply hd _ _ hx
  have hb : (Digest.inputRegion initial input).start + input.size < 2^32 :=
    hCall.inputInMemory.2.1
  change (Digest.inputRegion initial input).start ≤ _ ∧
    _ < (Digest.inputRegion initial input).start + input.size
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem effect_agrees {s t : RamState}
    (h : PrologueFrame 0x100010 Digest.minStackBytes s) (he : (effect s).Holds s t) :
    AgreesExcept (digestPreparationChanges s) s t := by
  apply he.agrees.widen
  · intro c hc hm
    cases c with
    | reg r =>
      simp only [effect, Effect.components, List.map_cons, List.map_nil,
        Write.component_reg, Write.component_mem, List.mem_cons, List.mem_append,
        List.not_mem_nil, or_false, false_or, Nat.reduceDiv, Component.reg.injEq,
        reduceCtorEq] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [digestPreparationChanges]
    | mem a len => cases hm
    | flags => simp [digestPreparationChanges]
    | rip => simp [digestPreparationChanges]
    | _ =>
      x86_norm [effect] at hc
  · intro address c hc hcov
    have hx := effect_covers h hc hcov
    have hs : (Stack.region s Digest.minStackBytes).Contains address.toNat := by
      have hn : 656 ≤ (stackPtr s).toNat := h.stack.2.2.1
      change (stackPtr s).toNat - 656 ≤ _ ∧ _ < (stackPtr s).toNat - 656 + 656 at hx
      change (stackPtr s).toNat - 656 ≤ _ ∧ _ < (stackPtr s).toNat - 656 +
        ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - 656))
      omega
    exact ⟨_, by simp [digestPreparationChanges], prologue_covers_of_contains hs⟩

theorem return_read {s t : RamState}
    (h : PrologueFrame 0x100010 Digest.minStackBytes s) (he : (effect s).Holds s t) :
    (Operand.mem (stackPtr s) : Operand 64).read t = (returnBoundary s).rip := by
  change memLoad t.external (stackPtr s) 64 = memLoad s.external (stackPtr s) 64
  apply memLoad_congr
  intro i hi
  apply congrArg (fun v : Option UInt8 ↦ v.getD 0)
  apply he.agrees.byte
  intro c hc hcov
  have hx := effect_covers h hc hcov
  have hl : 656 ≤ (stackPtr s).toNat := h.stack.2.2.1
  have hb : (stackPtr s).toNat - 656 +
      ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - 656)) < 2^32 := h.stack.1
  change (stackPtr s).toNat - 656 ≤ _ ∧ _ < (stackPtr s).toNat - 656 + 656 at hx
  rw [toNat_add_ofNat _ _ (by omega)] at hx
  omega

private theorem frame_offsets (x : BitVec 64) :
    x - 312 + 0xb8 = x - 128 ∧ x - 128 + 72 = x - 56 ∧ x - 128 + 80 = x - 48 ∧
      x - 128 + 88 = x - 40 ∧ x - 128 + 63 = x - 65 ∧ x - 128 + 64 = x - 64 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_omega

set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
theorem postcondition [bindings : Bindings] {s t : RamState} {input : ByteArray}
    (hCall : Digest.ValidCall bindings s input)
    (hFrame : PrologueFrame 0x100010 Digest.minStackBytes s)
    (hOutside : ¬ InProgram (returnBoundary s).rip)
    (hReady : ReadyToStep t) (hCode : CodeIn Extracted.programImage t)
    (he : (effect s).Holds s t) : Initialized s (returnBoundary s) input t := by
  have hw := he.writes
  x86_norm [effect] at hw
  rcases hw with ⟨h15, h14, h12, h3, hsp, hout, hlen, hptr, hblocks, hstate,
    hlow, hax, hmid, hhigh, hposition⟩
  simp only [Write.AllHold] at hposition
  have hRsp : stackPtr t = stackPtr s - 312 := by
    simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
      BitVec.reduceNeg] using hsp
  have hag := effect_agrees hFrame he
  have hf : Frame s (returnBoundary s) t := by
    refine ⟨hReady, hCode,
      hag.directionFlagClear (by simp [digestPreparationChanges]) hCall.directionFlagUnset,
      hOutside, hRsp, ?_, hout, ?_, ?_, ?_, ?_, ?_, hag⟩
    · rw [hRsp]
      simpa only [stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using hstate
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using
        (show (Operand.mem (stackPtr s - 32) : Operand 64).read t = s.regValue .rbx from h3)
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using
        (show (Operand.mem (stackPtr s - 24) : Operand 64).read t = s.regValue .r12 from h12)
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using
        (show (Operand.mem (stackPtr s - 16) : Operand 64).read t = s.regValue .r14 from h14)
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using
        (show (Operand.mem (stackPtr s - 8) : Operand 64).read t = s.regValue .r15 from h15)
    · simpa only [hRsp, BitVec.add_assoc, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
        BitVec.reduceNeg, BitVec.reduceAdd, BitVec.add_zero] using return_read hFrame he
  refine ⟨hf, he.rip, ?_, hptr, ?_, input_bytes_of_agrees hCall hag⟩
  · have hbase : stackPtr t + 0xb8 = stackPtr s - 128 := by
      rw [hRsp]; exact (frame_offsets _).1
    have ho := frame_offsets (stackPtr s)
    rw [hbase]
    apply absorbed_empty_of_initial_words
    · have hr := (hFrame.writable 56 20 (by decide +kernel) (by decide)).readable
      have ht : MemReadable t (stackPtr s - 56) 20 :=
        ⟨hr.low, fun i hi ↦ he.agrees.grow _ (hr.mem i hi)⟩
      rw [ho.2.1]
      exact ht
    · rw [ho.2.1]
      simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
        BitVec.reduceNeg] using hlow
    · rw [ho.2.2.1]
      simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
        BitVec.reduceNeg] using hmid
    · rw [ho.2.2.2.1]
      simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
        BitVec.reduceNeg] using hhigh
    · rw [ho.2.2.2.2.1]
      simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
        BitVec.reduceNeg] using hposition
    · rw [ho.2.2.2.2.2]
      simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
        BitVec.reduceNeg] using hblocks
  · change (Operand.reg 15 : Operand 64).read t = BitVec.ofNat 64 input.size
    calc
      _ = s.regValue .rsi := hlen
      _ = _ := ?_
    have hsize : input.size = (s.regValue .rsi).toNat :=
      hCall.inputLengthArgumentMatchesInput.symm
    rw [hsize, BitVec.ofNat_toNat]
    rfl

end Sha1.Proofs.Buffered.DigestPrepare.Initialize
