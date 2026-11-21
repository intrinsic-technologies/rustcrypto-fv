import Md5.Proofs.Buffered.DigestPrepare.Initialize.Model
import Md5.Proofs.Buffered.DigestPrepare.Copy

namespace Md5.Proofs.Buffered.DigestPrepare.Initialize

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Streaming

private theorem stackPtr_read (s : RamState) :
    stackPtr s = (Operand.reg 4 : Operand 64).read s := rfl

attribute [local x86_compose] stackPtr_read

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
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [digestPreparationChanges]
    | mem a len => cases hm
    | flags => simp [digestPreparationChanges]
    | rip => simp [digestPreparationChanges]
    | _ =>
      x86_norm [effect] at hc
  · intro address c hc hcov
    have hx := effect_covers h hc hcov
    have hs : (Stack.region s Digest.minStackBytes).Contains address.toNat := by
      have hn : 616 ≤ (stackPtr s).toNat := h.stack.2.2.1
      change (stackPtr s).toNat - 616 ≤ _ ∧ _ < (stackPtr s).toNat - 616 + 616 at hx
      change (stackPtr s).toNat - 616 ≤ _ ∧ _ < (stackPtr s).toNat - 616 +
        ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - 616))
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
  have hl : 616 ≤ (stackPtr s).toNat := h.stack.2.2.1
  have hb : (stackPtr s).toNat - 616 +
      ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - 616)) < 2^32 := h.stack.1
  change (stackPtr s).toNat - 616 ≤ _ ∧ _ < (stackPtr s).toNat - 616 + 616 at hx
  rw [toNat_add_ofNat _ _ (by omega)] at hx
  omega

set_option maxRecDepth 2048 in
theorem postcondition [bindings : Bindings] {s t : RamState} {input : ByteArray}
    (hCall : Digest.ValidCall bindings s input)
    (hFrame : PrologueFrame 0x100010 Digest.minStackBytes s)
    (hOutside : ¬ InProgram (returnBoundary s).rip)
    (hReady : ReadyToStep t) (hCode : CodeIn Extracted.programImage t)
    (he : (effect s).Holds s t) : Initialized s (returnBoundary s) input t := by
  have hw := he.writes
  x86_norm [effect] at hw
  rcases hw with ⟨h15, h14, h12, h3, hsp, hout, hlen, hptr, hstate,
    hhigh, hax, hlow, hblocks, hposition⟩
  simp only [Write.AllHold] at hposition
  have hRsp : stackPtr t = stackPtr s - 296 := by
    simpa only [stackPtr_read, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
      BitVec.reduceNeg] using hsp
  have hNat : (stackPtr t).toNat = (stackPtr s).toNat - 296 := by
    rw [hRsp]
    exact hFrame.slot_toNat 296 (by decide +kernel)
  have hLow : 616 ≤ (stackPtr s).toNat := hFrame.stack.2.2.1
  have hHigh : (stackPtr s).toNat - 616 +
      ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - 616)) < userAddressLimit := hFrame.stack.1
  have hSubset : ∀ a, (Finalize.Kind.digest.stackRegion t).Contains a →
      (Stack.region s Digest.minStackBytes).Contains a := by
    intro a ha
    change (stackPtr t).toNat - 320 ≤ a ∧ a < (stackPtr t).toNat - 320 + 584 at ha
    change (stackPtr s).toNat - 616 ≤ a ∧ a < (stackPtr s).toNat - 616 +
      ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - 616))
    rw [hNat] at ha
    omega
  have hag := effect_agrees hFrame he
  have hf : Frame s (returnBoundary s) t := by
    refine ⟨hReady, hCode,
      hag.directionFlagClear (by simp [digestPreparationChanges]) hCall.directionFlagUnset,
      hOutside,
      hRsp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hag⟩
    · rw [hNat]
      omega
    · rw [hNat]
      omega
    · have halign : (stackPtr s).toNat % 16 = 8 := hFrame.stack.2.2.2
      rw [hNat]
      omega
    · intro a ha
      exact Option.isSome_iff_exists.mp
        (he.agrees.grow _ (Option.isSome_iff_exists.mpr (hFrame.stack.2.1 a (hSubset a.toNat ha))))
    · intro a ha
      exact hFrame.avoids a (hSubset a.toNat ha)
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using hstate
    · exact hout
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using (show (Operand.mem (stackPtr s - 32) : Operand 64).read t =
        s.regValue .rbx from h3)
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using (show (Operand.mem (stackPtr s - 24) : Operand 64).read t =
        s.regValue .r12 from h12)
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using (show (Operand.mem (stackPtr s - 16) : Operand 64).read t =
        s.regValue .r14 from h14)
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using (show (Operand.mem (stackPtr s - 8) : Operand 64).read t =
        s.regValue .r15 from h15)
    · simpa only [hRsp, BitVec.add_assoc, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
        BitVec.reduceNeg, BitVec.reduceAdd, BitVec.add_zero] using return_read hFrame he
  refine ⟨hf, he.rip, ?_, hptr, ?_, hf.inputBytes hCall⟩
  · change Absorbed (stackPtr t + 176) ByteArray.empty t
    apply absorbed_empty_of_initial_words
    · have hr := (hFrame.writable 56 16 (by decide +kernel) (by decide)).readable
      have ht : MemReadable t (stackPtr s - 56) 16 :=
        ⟨hr.low, fun i hi ↦ he.agrees.grow _ (hr.mem i hi)⟩
      simpa only [hRsp, BitVec.add_assoc, BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat,
        BitVec.reduceNeg, BitVec.reduceAdd] using ht
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using hlow
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using hhigh
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using hposition
    · simpa only [hRsp, stackPtr_read, BitVec.add_assoc, BitVec.sub_eq_add_neg,
        BitVec.ofNat_eq_ofNat, BitVec.reduceNeg, BitVec.reduceAdd] using hblocks
  · change (Operand.reg 15 : Operand 64).read t = BitVec.ofNat 64 input.size
    calc
      _ = s.regValue .rsi := hlen
      _ = _ := ?_
    have hsize : input.size = (s.regValue .rsi).toNat := hCall.inputLengthArgumentMatchesInput.symm
    rw [hsize, BitVec.ofNat_toNat]
    rfl

end Md5.Proofs.Buffered.DigestPrepare.Initialize
