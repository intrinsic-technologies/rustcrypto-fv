import AesGcm.Proofs.Machine.CTR.BatchFull

namespace AesGcm.Proofs.Machine.CTR.Loop

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift
  X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

variable {use256 : Bool} {code : CodeMap} {fr : Activation} {args : Values Value Reg.count}
  {mem : Ram} {sp : BitVec 64} {words : Vector (BitVec 16) (keyWords use256)}
  {before after : LIR.lifted.Location}

theorem native_slot_outside (hw : CipherWorkingState use256 code fr args mem sp words before)
    (a : BitVec 64) (ha : 0x201208 ≤ a.toNat) (hb : a.toNat ≤ 0x201230) :
    Outside [span (sp - 296) 512, span (sp + 224) 8] a 8 := by
  have low := hw.stack.readable.low
  have sub : (sp - 296).toNat + 296 = sp.toNat := by bv_omega
  have add : (sp + 224).toNat = sp.toNat + 224 := by bv_omega
  have apart := hw.slotsApart
  refine ⟨by omega, ?_⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> simp only [span]
  all_goals cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at apart <;> omega

theorem native_frame_of_scratch (hw : CipherWorkingState use256 code fr args mem sp words before)
    {m : Ram} (hf : RamWriteFrame before.store m [span (sp - 296) 512]) :
    RamWriteFrame before.store m [span (sp - 296) 512, span (sp + 224) 8] ∧
    memLoad m (sp + 224) 64 = memLoad before.store (sp + 224) 64 := by
  refine ⟨(RamWriteFrame.refl _ _).trans hf ?_, hf.memLoad_eq ?_⟩
  · intro r hr
    exact ⟨r, List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hr)), Nat.le_refl _, Nat.le_refl _⟩
  · have hl := hw.stack.readable.low
    constructor
    · change (sp + 224).toNat + 8 ≤ 2^64
      bv_omega
    · intro r hr
      obtain rfl := List.mem_singleton.mp hr
      right
      change (sp - 296).toNat + 512 ≤ (sp + 224).toNat
      bv_omega

theorem native_frame (hw : CipherWorkingState use256 code fr args mem sp words before)
    (ht : GPRsTyped after.arguments)
    (hs : after.arguments[4]'(by change 4 < 53; decide) = ⟨64, sp⟩)
    (hr : ∀ r : Fin 53, r.val ∈ [22,39,50,51] → after.arguments[r] = before.arguments[r])
    (hf : RamWriteFrame before.store after.store [span (sp - 296) 512, span (sp + 224) 8])
    (hc : memLoad after.store (sp + 224) 64 = memLoad before.store (sp + 224) 64) :
    CipherWorkingState use256 code fr args mem sp words after := by
  have ho : Outside [span (sp - 296) 512, span (sp + 224) 8]
      (sp + 344) (64 / 8 * keyWords use256) := by
    have low := hw.stack.readable.low
    have sub : (sp - 296).toNat + 296 = sp.toNat := by bv_omega
    have add : (sp + 344).toNat = sp.toNat + 344 := by bv_omega
    have count : (sp + 224).toNat = sp.toNat + 224 := by bv_omega
    refine ⟨by cases use256 <;> simp only [keyWords, Bool.false_eq_true, ↓reduceIte] <;> omega, ?_⟩
    intro r h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> right <;> simp only [span] <;> omega
  have hr39 : after.arguments[39]'(by change 39 < 53; decide) = before.arguments[39]'(by change 39 < 53; decide) := hr 39 (by decide)
  have hr50 : after.arguments[50]'(by change 50 < 53; decide) = before.arguments[50]'(by change 50 < 53; decide) := hr 50 (by decide)
  have hr51 : after.arguments[51]'(by change 51 < 53; decide) = before.arguments[51]'(by change 51 < 53; decide) := hr 51 (by decide)
  exact
    { typed := ht
      df := (hr 22 (by decide)).trans hw.df
      x87 := by rw [hr39, hr50, hr51]; exact hw.x87
      regFrame := fun r h => (hr r h).trans (hw.regFrame r h)
      aligned := hw.aligned
      stackPointer := hs
      countWord := hc.trans hw.countWord
      stack := hw.stack.of_frame hf
      stackTail := hw.stackTail.of_frame hf
      keyRead := hw.keyRead.of_frame hf
      keys := hw.keys.of_frame hf (by decide) ho
      slot0Readable := hw.slot0Readable.of_frame hf
      slot0Value := (hf.memLoad_eq (native_slot_outside hw _ (by decide) (by decide))).trans hw.slot0Value
      slot1Readable := hw.slot1Readable.of_frame hf
      slot1Value := (hf.memLoad_eq (native_slot_outside hw _ (by decide) (by decide))).trans hw.slot1Value
      slot2Readable := hw.slot2Readable.of_frame hf
      slot2Value := (hf.memLoad_eq (native_slot_outside hw _ (by decide) (by decide))).trans hw.slot2Value
      slotsApart := hw.slotsApart
      written := hw.written.trans hf fun r h => ⟨r, h, Nat.le_refl _, Nat.le_refl _⟩ }

end AesGcm.Proofs.Machine.CTR.Loop
