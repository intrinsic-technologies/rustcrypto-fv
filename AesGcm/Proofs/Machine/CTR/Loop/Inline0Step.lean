import AesGcm.Proofs.Machine.CTR.Loop.Frame

import AesGcm.Proofs.Machine.AESCore.Rounds
namespace AesGcm.Proofs.Machine.CTR.Loop

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime
open AesGcm.Proofs.Machine.Fixslice

open AesGcm.Proofs.Machine.AESCore
open Standards.NIST.AES

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
theorem inline0_step
    (use256 : Bool) (code : CodeMap) (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (fr : Activation) (args : Values Value Reg.count) (mem : Ram)
    (sp : BitVec 64) (scheduleWords : Vector (BitVec 16) (keyWords use256))
    (index : BitVec 64) (planes keys : Planes) (loc : LIR.lifted.Location)
    (hwork : CipherWorkingState use256 code fr args mem sp scheduleWords loc)
    (hlabel : loc.label = (if use256 then .l1093a3 else .l107f13))
    (hindex : loc.arguments[5]'(by change 5 < 53; decide) = ⟨64, index⟩)
    (hKeyRead : Readable loc.store
      (sp + (index <<< 3) + (if use256 then 536 else 600)) 64)
    (hApart : (sp + 8).toNat + (if use256 then 128 else 64) ≤
        (sp + (index <<< 3) + (if use256 then 536 else 600)).toNat ∨
      (sp + (index <<< 3) + (if use256 then 536 else 600)).toNat + 64 ≤ (sp + 8).toNat)
    (hWords : WordsAt loc.store (sp + 8) 64 (Vector.ofFn planes))
    (hKeys : WordsAt loc.store
      (sp + (index <<< 3) + (if use256 then 536 else 600)) 64 (Vector.ofFn keys)) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches ⟨loc, []⟩ ⟨next, []⟩ ∧
      CipherWorkingState use256 code fr args mem sp scheduleWords next ∧
      next.label = (if use256 then .l109010 else .l107b80) ∧
      WordsAt next.store (sp + 8) 64
        (Vector.ofFn fun p : Fin 8 ↦ if p.val = 7 then mixColumns0 planes p
          else mixColumns0 planes p ^^^ keys p) ∧
      (next.arguments[if use256 then 15 else 14]'
        (by change (if use256 then 15 else 14) < 53; cases use256 <;> decide)).get 64 =
        mixColumns0 planes 7 ∧
      memLoad next.store (sp + 64) 64 = mixColumns0 planes 7 ∧
      next.arguments[5]'(by change 5 < 53; decide) = ⟨64, index + 32⟩ := by
  have hlow := hwork.stack.readable.low
  have hTypes := hwork.typed
  have hsp := congrArg (Value.get 64) hwork.stackPointer
  have hIndex := congrArg (Value.get 64) hindex
  have hStack : Writable code loc.store (sp + 8) (if use256 then 128 else 64) :=
    hwork.stack.of_offsets (x := sp) (c := 8) (d := -296) rfl (BitVec.sub_eq_add_neg _ _)
      (by cases use256 <;> decide)
  obtain ⟨mid, hrun, hlabel', hwords', htail, htailMem, hidx, hkeep, htyped, hwrite⟩ :=
    batch_inline0 use256 code hcode loc.arguments loc.store sp index planes keys
      hTypes hsp hIndex hStack hKeyRead hApart hWords hKeys
  have hactual : LIR.program.runBlock (dialect code) loc = .jump mid := by
    cases loc with
    | mk lab vals store =>
      change lab = _ at hlabel
      subst lab
      exact hrun
  have hreach : (LIR.program.sem (dialect code)).Reaches ⟨loc, []⟩ ⟨mid, []⟩ :=
    Semantics.Reaches.single (by
      change (LIR.program.runBlock (dialect code) loc).next (dialect code) [] = _
      rw [hactual]
      rfl)
  have h8 : (sp + 8).toNat = (sp - 296).toNat + 304 :=
    toNat_of_offsets (x := sp) (c := 8) (d := -296) (n := 64) rfl
      (BitVec.sub_eq_add_neg _ _) hlow (by decide)
  have h120 : (sp + 120).toNat = (sp - 296).toNat + 416 :=
    toNat_of_offsets (x := sp) (c := 120) (d := -296) (n := 16) rfl
      (BitVec.sub_eq_add_neg _ _) hlow (by decide)
  have hscratch : RamWriteFrame loc.store mid.store [span (sp - 296) 512] := by
    apply (RamWriteFrame.refl _ _).trans hwrite
    cases use256 <;> intro r hr
    all_goals simp only [Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    all_goals first | subst r | rcases hr with rfl | rfl
    all_goals refine ⟨_, List.mem_cons_self, ?_, ?_⟩ <;> simp only [span] <;> omega
  obtain ⟨hf, hc⟩ := native_frame_of_scratch hwork hscratch
  have hw := native_frame (after := mid) hwork htyped
    ((hkeep 4 (by decide)).trans hwork.stackPointer)
    (fun r hr ↦ hkeep r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with h | h | h | h <;> rw [h] <;> decide)) hf hc
  refine ⟨mid, hreach, hw, hlabel', ?_, htail, htailMem, hidx⟩
  intro i hi
  rw [Vector.getElem_ofFn]
  by_cases h : i = 7
  · subst i
    change memLoad mid.store (sp + 8 + 56) 64 = mixColumns0 planes 7
    rw [show sp + 8 + 56 = sp + 64 by bv_omega]
    exact htailMem
  · simp only [h, ite_false]
    exact hwords' i (by omega)

end AesGcm.Proofs.Machine.CTR.Loop
