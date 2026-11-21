import Sha1.Proofs.Buffered.Finalize.Family.Contracts
import Sha1.Proofs.Buffered.Finalize.Family.Pad.Setup
import Sha1.Proofs.Buffered.Finalize.Family.Pad.Branch
import Sha1.Proofs.Buffered.Finalize.Digest.Prepare

namespace Sha1.Proofs.Buffered.Finalize.Family

open Sha1.Spec Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

private def paddingChanges (s : RamState) (position : Nat) : List Component :=
  [.mem (stackPtr s + BitVec.ofNat 64 (position + 32)) 1,
    .mem (stackPtr s + BitVec.ofNat 64 (position + 33)) (63 - position),
    .mem (pushAddr s) 8,
    .reg 0, .reg 1, .reg 2, .reg 3, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11,
    .flags, .rip]

private theorem padding_cover {s : RamState} {position : Nat} {c : Component} {a : BitVec 64}
    (hc : c ∈ paddingChanges s position) (ha : c.Covers a) :
    Component.Covers (.mem (stackPtr s + BitVec.ofNat 64 (position + 32)) 1) a ∨
    Component.Covers (.mem (stackPtr s + BitVec.ofNat 64 (position + 33)) (63 - position)) a ∨
    Component.Covers (.mem (pushAddr s) 8) a := by
  simp only [paddingChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact .inl ha | exact .inr (.inl ha) | exact .inr (.inr ha) | exact ha.elim

private theorem fill_and_slot_apart {s : RamState} (hs : Storage .updateFinalizeCopy s)
    {p : Nat} (hp : p < 64) {k : Nat} (hk : k < 312) (hoffset : k < p + 33 ∨ 96 ≤ k) :
    ¬ Component.Covers (.mem (stackPtr s + BitVec.ofNat 64 (p + 33)) (63 - p))
        (stackPtr s + BitVec.ofNat 64 k) ∧
    ¬ Component.Covers (.mem (pushAddr s) 8) (stackPtr s + BitVec.ofNat 64 k) := by
  constructor
  · exact Digest.covers_apart (b := k) (count := 1) (i := 0) (by rw [BitVec.add_zero])
      (by decide) (by omega) (by omega) (by omega)
  · rintro ⟨j, hj, he⟩
    apply hs.stackApartPush (offset := k) (len := 1) (by simp only [Kind.stackBytes]; omega)
      0 (by decide) j hj
    simpa only [BitVec.add_zero] using he

private theorem padding_frame {s t : RamState} {p : Nat} (hs : Storage .updateFinalizeCopy s)
    (hp : p < 64) (hAgree : AgreesExcept (paddingChanges s p) s t) :
    AgreesExcept (Kind.updateFinalizeCopy.changes s) s t := by
  apply agrees_changes hAgree
  · intro c hc hn
    simp only [paddingChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [Component.isMem, Kind.changes, Kind.workRegisters] at hn ⊢
  · intro a c hc ha
    rcases padding_cover hc ha with hMarker | hFill | hSlot
    · exact hs.localWithin (offset := p + 32) (len := 1)
        (by simp only [Kind.stackBytes]; omega) hMarker
    · exact hs.localWithin (offset := p + 33) (len := 63 - p)
        (by simp only [Kind.stackBytes]; omega) hFill
    · obtain ⟨j, hj, rfl⟩ := hSlot
      refine ⟨336 + j, by simp only [Kind.stackBytes, Kind.frameBytes]; omega, ?_⟩
      simp only [pushAddr, BitVec.sub_eq_add_neg, BitVec.add_assoc]
      congr 1
      rw [BitVec.ofNat_add, ← BitVec.add_assoc]
      congr 1

theorem pad [bindings : Bindings] {b : ReturnBoundary} {m : ByteArray} {s : RamState}
    (hStride : UnitStringStride bindings) (hOutside : ¬ InProgram b.rip)
    (storage : Storage .updateFinalizeCopy s) (ready : ReadyToStep s)
    (code : CodeIn Extracted.programImage s)
    (h : Prepared m s) : ∃ t, Run b s t ∧ Padded m t := by
  let p := m.size % 64
  have hp : p < 64 := Nat.mod_lt _ (by decide)
  obtain ⟨n₁, u, hRun₁, hReady₁, hCode₁, hPrefix⟩ := Prefix.run ready code hOutside h.rip
  have hRsp₁ : stackPtr u = stackPtr s := hPrefix.agrees.read (n := 64) (r := 4) (by
    simp [Prefix.effect, Effect.components])
  have hPos₁ : (Operand.reg 14 : Operand 64).read u = BitVec.ofNat 64 p :=
    (hPrefix.agrees.read (by simp [Prefix.effect, Effect.components])).trans h.position
  have hRemain₁ : (Operand.reg 3 : Operand 64).read u = BitVec.ofNat 64 (63 - p) := by
    have hw := hPrefix.writes
    simp only [Prefix.effect, Write.AllHold] at hw
    rw [hw, h.position]
    exact Digest.remaining_xor p hp
  have hStorage₁ := storage.of_agrees hPrefix.agrees hRsp₁
  obtain ⟨n₂, v, hRun₂, hReady₂, hCode₂, hSetup⟩ := Padding.run hReady₁ hCode₁ hOutside
    ⟨hStorage₁, hPrefix.rip, by rw [hPos₁, BitVec.toNat_ofNat]; omega⟩
  have hRsp₂ := (Padding.effect_rsp hSetup).trans hRsp₁
  have hStorage₂ := hStorage₁.of_agrees hSetup.agrees (Padding.effect_rsp hSetup)
  have hDf₁ := (hPrefix.agrees.directionFlagClear
    (by simp [Prefix.effect, Effect.components]) ⟨h.df⟩).df
  have hDf₂ := (hSetup.agrees.directionFlagClear
    (by simp [Padding.effect, Effect.components]) ⟨hDf₁⟩).df
  have hMarker : stackPtr u + (Operand.reg 14 : Operand 64).read u + 32 =
      stackPtr s + BitVec.ofNat 64 (p + 32) := by
    rw [hRsp₁, hPos₁, BitVec.add_assoc, BitVec.ofNat_add]
    rfl
  have hw := hSetup.writes
  simp only [Padding.effect, Write.AllHold] at hw
  rw [hMarker] at hw
  have hDst : rdi.read v = stackPtr v + BitVec.ofNat 64 (p + 33) := by
    change (Operand.reg 7 : Operand 64).read v = _
    rw [hw.2.1, hRsp₂, hRsp₁, hPos₁, BitVec.add_assoc, BitVec.ofNat_add]
    rfl
  have hLen : MemoryRoutines.rdx.read v = BitVec.ofNat 64 (63 - p) :=
    hw.2.2.2.trans hRemain₁
  obtain ⟨w, hCall⟩ := Padding.memset hStride hReady₂ hCode₂ hOutside hStorage₂ hSetup.rip
    hDf₂ hp hDst hLen
  have hRemain : (Operand.reg 3 : Operand 64).read w = BitVec.ofNat 64 (63 - p) :=
    (hCall.agrees.read (by simp [callSiteChanges])).trans
      ((hSetup.agrees.read (by simp [Padding.effect, Effect.components])).trans hRemain₁)
  obtain ⟨t, hBranch, hReady, hCode, hRip, hBranchFrame⟩ :=
    padding_branch hCall.ready hCall.code hOutside hCall.rip hp hRemain
  have hAfterCall : AgreesExcept (callSiteChanges v) v t :=
    (hCall.agrees.trans hBranchFrame).mono (by simp [callSiteChanges])
  have hLenNat : (MemoryRoutines.rdx.read v).toNat = 63 - p := by
    rw [hLen, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hPush : pushAddr v = pushAddr s := by simp only [pushAddr, hRsp₂]
  have hAgree : AgreesExcept (paddingChanges s p) s t :=
    ((hPrefix.agrees.trans hSetup.agrees).trans hAfterCall).mono (by
      intro c hc
      simp only [Prefix.effect, Padding.effect, Effect.components, hMarker, callSiteChanges,
        hDst, hRsp₂, hLenNat, hPush, paddingChanges, List.map_cons,
        List.map_nil, List.cons_append, List.nil_append, Write.component, Operand.component,
        List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
      grind only)
  have hRsp : stackPtr t = stackPtr s := hAgree.read (n := 64) (r := 4) (by simp [paddingChanges])
  have hKeep (k : Nat) (hk : k < 312) (hoffset : k < p + 32 ∨ 96 ≤ k) :
      t.external[stackPtr s + BitVec.ofNat 64 k]? =
        s.external[stackPtr s + BitVec.ofNat 64 k]? := by
    apply hAgree.byte
    intro c hc hCovered
    have ⟨hFill, hSlot⟩ := fill_and_slot_apart storage hp hk (by omega)
    rcases padding_cover hc hCovered with hAtMarker | hAtFill | hAtSlot
    · exact Digest.covers_apart (b := k) (count := 1) (i := 0) (by rw [BitVec.add_zero])
        (by decide) (by omega) (by omega) (by omega) hAtMarker
    · exact hFill hAtFill
    · exact hSlot hAtSlot
  have hSaved : savedOutput t = savedOutput s := by
    unfold savedOutput
    rw [hRsp]
    change memLoad t.external (stackPtr s + 192) 64 =
      memLoad s.external (stackPtr s + 192) 64
    apply memLoad_congr
    intro i hi
    change (t.external[stackPtr s + BitVec.ofNat 64 192 + BitVec.ofNat 64 i]?).getD 0 =
      (s.external[stackPtr s + BitVec.ofNat 64 192 + BitVec.ofNat 64 i]?).getD 0
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, hKeep (192 + i) (by omega) (by omega)]
  have hState : StateBytes t (absorbedHash m) := by
    unfold StateBytes
    change (⟨(stackPtr t + 8).toNat, 20⟩ : MemoryRegion).HasBytes t.external
      (absorbedStateBytes m)
    rw [hRsp, ← absorbedStateBytes_size m]
    apply hasBytes_of_copy _ (show
      (⟨(stackPtr s + 8).toNat, (absorbedStateBytes m).size⟩ : MemoryRegion).HasBytes
        s.external (absorbedStateBytes m) by rw [absorbedStateBytes_size]; exact h.state)
    intro i hi
    rw [absorbedStateBytes_size] at hi
    change t.external[stackPtr s + BitVec.ofNat 64 8 + BitVec.ofNat 64 i]? =
      s.external[stackPtr s + BitVec.ofNat 64 8 + BitVec.ofNat 64 i]?
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, hKeep (8 + i) (by omega) (by omega)]
  have hPadded : Bytes t.external (stackPtr t + 32) 64 (fun i ↦ (Digest.firstBlock m)[i]!) := by
    rw [hRsp]
    apply Digest.firstBlock_bytes m
    · intro i hi
      have hTail := Digest.bytes_of_hasBytes h.tail i (by rw [size_tailBytes]; exact hi)
      simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hTail
      change t.external[stackPtr s + BitVec.ofNat 64 32 + BitVec.ofNat 64 i]? = _
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, hKeep (32 + i) (by omega) (by omega)]
      change s.external[stackPtr s + BitVec.ofNat 64 32 + BitVec.ofNat 64 i]? = _ at hTail
      rw [BitVec.add_assoc, ← BitVec.ofNat_add] at hTail
      exact hTail
    · change t.external[stackPtr s + BitVec.ofNat 64 32 + BitVec.ofNat 64 p]? = _
      have hadd : stackPtr s + BitVec.ofNat 64 32 + BitVec.ofNat 64 p =
          stackPtr s + BitVec.ofNat 64 (p + 32) := by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm]
      rw [hadd]
      have ⟨hFill, hSlot⟩ := fill_and_slot_apart storage hp (k := p + 32) (by omega) (by omega)
      rw [hAfterCall.byte (by
        intro c hc hcov
        simp only [callSiteChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals try exact hcov.elim
        · rw [hDst, hRsp₂, hLenNat] at hcov
          exact hFill hcov
        · rw [hPush] at hcov
          exact hSlot hcov)]
      have hr : ∀ i < 8 / 8, (v.external[stackPtr s + BitVec.ofNat 64 (p + 32) +
          BitVec.ofNat 64 i]?).isSome := by
        intro i hi
        have hWritable := (hStorage₂.stackWritable (p + 32) 1
          (by simp only [Kind.stackBytes]; omega)).mem i hi
        rwa [hRsp₂] at hWritable
      have hb := Bytes.of_memLoad hr 0 (by decide)
      have hm := hw.1
      change memLoad v.external _ 8 = _ at hm
      rw [hm, BitVec.add_zero] at hb
      exact hb
    · intro i hlo hhi
      change t.external[stackPtr s + BitVec.ofNat 64 32 + BitVec.ofNat 64 i]? = _
      have hh := hCall.fill (i - (p + 1)) (by rw [hLenNat]; omega)
      have hByte := hBranchFrame.byte (x := rdi.read v + BitVec.ofNat 64 (i - (p + 1))) (by
        simp [Component.Covers])
      have hZero : rsi.read v = 0 := hw.2.2.1
      rw [← hByte, hDst, hRsp₂, hZero, BitVec.add_assoc, ← BitVec.ofNat_add,
        show p + 33 + (i - (p + 1)) = 32 + i by omega] at hh
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact hh
  obtain ⟨n₃, hRun₃⟩ := hCall.advances
  refine ⟨t, ⟨⟨n₁ + n₂ + n₃ + 2, ((hRun₁.trans hRun₂).trans hRun₃).trans hBranch⟩,
    hReady, hCode, hRsp, hSaved, padding_frame storage hp hAgree⟩, ?_⟩
  exact ⟨⟨(hAgree.read (by simp [paddingChanges])).trans h.position,
    (hAgree.read (by simp [paddingChanges])).trans h.blocks⟩, hRip,
    (hAgree.directionFlagClear (by simp [paddingChanges]) ⟨h.df⟩).df,
    hState, hPadded⟩

end Sha1.Proofs.Buffered.Finalize.Family
