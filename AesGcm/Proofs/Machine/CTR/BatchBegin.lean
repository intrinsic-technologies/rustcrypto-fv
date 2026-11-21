import AesGcm.Proofs.Machine.CTR.BatchInput
import AesGcm.Proofs.Machine.Runtime.Preservation
import AesGcm.Proofs.Machine.LIR
import AesGcm.Proofs.Machine.Runtime.Tactics

namespace AesGcm.Proofs.Machine.CTR
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

set_option maxHeartbeats 400000 in
theorem batch_begin (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (sp destination : BitVec 64)
    (hTypes : GPRsTyped args) (hsp : args[4].get 64 = sp)
    (hdst : args[2].get 64 = destination)
    (hStack : Writable code mem (sp + 216) 16) :
    ∃ next : LIR.lifted.Location,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l1085da else .l10714a), args, mem⟩ = .jump next ∧
      next.label = (if use256 then .l108e98 else .l107a08) ∧
      next.store = memStore (memStore mem (sp + 224) (0#64)) (sp + 216) destination ∧
      (∀ r : Fin 53, r.val ∈ [2,3,4,5,9,12,13,14,15,22,39,50,51] →
        next.arguments[r] = args[r]) ∧
      GPRsTyped next.arguments ∧
      RamWriteFrame mem next.store [span (sp + 216) 16] := by
  have hStackRead := hStack.readable
  have hStackLow := hStackRead.low
  runtime_context [hsp, hdst]
  have hRange {m : Ram} {a : BitVec 64} {n : Nat}
      (h : Writable code m a n) : RangeApart a n
        (if use256 then 0x1085da else 0x10714a) 25 := by
    cases use256
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l10714a x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l1085da x hx))).apart
  cases use256
  all_goals
    have hhelperApart := @hRange
    simp only [Bool.false_eq_true, ↓reduceIte] at hhelperApart
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    rotate_left
    · first
      | change LIR.program.runBlock (dialect code) ⟨.l10714a, args, mem⟩ = _
      | change LIR.program.runBlock (dialect code) ⟨.l1085da, args, mem⟩ = _
      cfg_eval [LIR.program, hsp, hdst]
      runtime_guards transfer
      rfl
    · rfl
    · rfl
    · rintro ⟨r, hr⟩ hin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
      rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · runtime_typed
    · runtime_finish [span]

set_option maxHeartbeats 1200000 in
theorem batch_begin_input_reaches (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (sp counter destination : BitVec 64)
    (hTypes : GPRsTyped args) (hsp : args[4].get 64 = sp)
    (hcounter : args[9].get 64 = counter) (hdestination : args[2].get 64 = destination)
    (hroom : 80 ≤ sp.toNat) (halign : sp.toNat % 16 = 0)
    (hw : Writable code mem (sp - 80) 400) (hc : Writable code mem counter 20)
    (hApart : sp.toNat + 320 ≤ counter.toNat ∨ counter.toNat + 20 ≤ sp.toNat - 80)
    (hdf : args[22] = ⟨1, 0⟩)
    (h39 : args[39] = ⟨32, args[39].get 32⟩)
    (h50 : args[50] = ⟨16, args[50].get 16⟩)
    (h51 : args[51] = ⟨16, args[51].get 16⟩) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches
        ⟨⟨if use256 then .l1085da else .l10714a, args, mem⟩, []⟩ ⟨next, []⟩ ∧
      next.label = batchReturnLabel use256 ∧ GPRsTyped next.arguments ∧
      (∀ r : Fin 53, r.val ∈ [3,4,5,12,13,14,15,22,39,50,51] → next.arguments[r] = args[r]) ∧
      (∀ p : Fin 8, memLoad next.store (sp + 8 + BitVec.ofNat 64 (8 * p.val)) 64 =
        Fixslice.encode (counterBlocks mem counter) p) ∧
      memLoad next.store (sp + 216) 64 = destination ∧
      memLoad next.store (sp + 224) 64 = 0 ∧
      memLoad next.store (counter + 16) 32 = memLoad mem (counter + 16) 32 + 4 ∧
      RamWriteFrame mem next.store
        [span (sp - 80) 80, span (sp + 8) 64, span (sp + 216) 16,
          span (sp + 256) 64, span (counter + 16) 4] := by
  have hs80 : (sp - 80).toNat = sp.toNat - 80 := by bv_omega
  have hlow : sp.toNat + 320 ≤ 2^32 := by have hh := hw.readable.low; rw [hs80] at hh; omega
  have hadd (n : Nat) (hn : n ≤ 320) : (sp + BitVec.ofNat 64 n).toNat = sp.toNat + n := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have ha8 : (sp + 8).toNat = sp.toNat + 8 := by simpa only [BitVec.ofNat_eq_ofNat] using hadd 8 (by decide)
  have ha216 : (sp + 216).toNat = sp.toNat + 216 := by simpa only [BitVec.ofNat_eq_ofNat] using hadd 216 (by decide)
  have ha224 : (sp + 224).toNat = sp.toNat + 224 := by simpa only [BitVec.ofNat_eq_ofNat] using hadd 224 (by decide)
  have ha256 : (sp + 256).toNat = sp.toNat + 256 := by simpa only [BitVec.ofNat_eq_ofNat] using hadd 256 (by decide)
  have hc16 : (counter + 16).toNat = counter.toNat + 16 := by have hh := hc.readable.low; bv_omega
  obtain ⟨mid, hstep, hlabel, hmem, hkeep, htyped, hf⟩ :=
    batch_begin use256 code hcode args mem sp destination hTypes hsp hdestination
      (hw.sub (by rw [hs80, ha216]; omega) (by rw [hs80, ha216]; omega))
  have hmid4 : (mid.arguments[4]'(by change 4 < 53; decide)).get 64 = sp :=
    (congrArg (Value.get 64) (hkeep 4 (by decide))).trans hsp
  have hmid9 : (mid.arguments[9]'(by change 9 < 53; decide)).get 64 = counter :=
    (congrArg (Value.get 64) (hkeep 9 (by decide))).trans hcounter
  have hmid39 : mid.arguments[39]'(by change 39 < 53; decide) = args[39] := hkeep 39 (by decide)
  have hmid50 : mid.arguments[50]'(by change 50 < 53; decide) = args[50] := hkeep 50 (by decide)
  have hmid51 : mid.arguments[51]'(by change 51 < 53; decide) = args[51] := hkeep 51 (by decide)
  obtain ⟨next, hreach, hnext, hnextTypes, hnextKeep, hwords, hd, hnextFrame⟩ :=
    batch_input_reaches use256 code hcode mid.arguments mid.store sp counter htyped hmid4 hmid9
      hroom halign (hw.of_frame hf) (hc.of_frame hf) hApart
      ((hkeep 22 (by decide)).trans hdf)
      (by rw [hmid39,h39]; rfl) (by rw [hmid50,h50]; rfl) (by rw [hmid51,h51]; rfl)
  have counterOutside : Outside [span (sp + 216) 16] counter 20 := by
    refine ⟨Nat.le_trans hc.readable.low (by decide), ?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    simp only [span, ha216]
    omega
  have loadCounter (n : Nat) (hn : n + 4 ≤ 20) :
      memLoad mid.store (counter + BitVec.ofNat 64 n) 32 = memLoad mem (counter + BitVec.ofNat 64 n) 32 :=
    hf.memLoad_eq (outside_subregion counterOutside (by omega) hn)
  have blocks : counterBlocks mid.store counter = counterBlocks mem counter := by
    funext b j
    simp only [counterBlocks, counterWord]
    split
    · rw [loadCounter _ (by omega)]
    · have h12 : memLoad mid.store (counter + 12) 32 = memLoad mem (counter + 12) 32 := loadCounter 12 (by decide)
      have h16 : memLoad mid.store (counter + 16) 32 = memLoad mem (counter + 16) 32 := loadCounter 16 (by decide)
      rw [h12,h16]
  have slotsOutside (n : Nat) (hn : n = 216 ∨ n = 224) :
      Outside [span (sp - 80) 80, span (sp + 8) 64, span (sp + 256) 64, span (counter + 16) 4]
        (sp + BitVec.ofNat 64 n) 8 := by
    have ha := hadd n (by omega)
    refine ⟨by rw [ha]; omega, ?_⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    all_goals simp only [span, hs80, ha8, ha256, hc16, ha]
    all_goals omega
  have hdst : memLoad next.store (sp + 216) 64 = destination := by
    have ho : Outside _ (sp + 216) 8 := slotsOutside 216 (Or.inl rfl)
    rw [hnextFrame.memLoad_eq ho, hmem]
    exact memLoad_memStore_same _ _ _ (by decide) (by decide)
  have hzero : memLoad next.store (sp + 224) 64 = 0 := by
    have ho : Outside _ (sp + 224) 8 := slotsOutside 224 (Or.inr rfl)
    rw [hnextFrame.memLoad_eq ho, hmem]
    runtime_finish []
  have hframe0 : RamWriteFrame mem mid.store
      [span (sp - 80) 80, span (sp + 8) 64, span (sp + 216) 16,
        span (sp + 256) 64, span (counter + 16) 4] := by
    apply (RamWriteFrame.refl _ _).trans hf
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, by simp, Nat.le_refl _, Nat.le_refl _⟩
  have hframeAll := hframe0.trans hnextFrame (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    all_goals exact ⟨_, by simp, Nat.le_refl _, Nat.le_refl _⟩)
  have hs : LIR.program.step (dialect code)
      ⟨⟨if use256 then .l1085da else .l10714a, args, mem⟩, []⟩ = .next ⟨mid, []⟩ := by
    rw [Program.step,hstep]; rfl
  have hmreach : (LIR.program.sem (dialect code)).Reaches ⟨mid, []⟩ ⟨next, []⟩ := by
    change (LIR.program.sem (dialect code)).Reaches ⟨⟨mid.label, mid.arguments, mid.store⟩, []⟩ _
    rw [hlabel]
    exact hreach
  refine ⟨next, (Semantics.Reaches.single hs).trans hmreach, hnext, hnextTypes, ?_, ?_, hdst, hzero, ?_, hframeAll⟩
  · intro r hr
    exact (hnextKeep r hr).trans (hkeep r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      omega))
  · simpa only [blocks] using hwords
  · have h16 : memLoad mid.store (counter + 16) 32 = memLoad mem (counter + 16) 32 := loadCounter 16 (by decide)
    exact hd.trans (congrArg (fun w : BitVec 32 ↦ w + 4) h16)

end AesGcm.Proofs.Machine.CTR
