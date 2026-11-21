import AesGcm.Proofs.Machine.CTR.Loop.Frame

namespace AesGcm.Proofs.Machine.CTR.Loop

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime
open AesGcm.Proofs.Machine.Fixslice

set_option maxHeartbeats 600000 in
theorem key1_step
    (use256 : Bool) (code : CodeMap) (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (fr : Activation) (args : Values Value Reg.count) (mem : Ram)
    (sp : BitVec 64) (scheduleWords : Vector (BitVec 16) (keyWords use256))
    (index : BitVec 64) (planes keys : Planes) (loc : LIR.lifted.Location)
    (hwork : CipherWorkingState use256 code fr args mem sp scheduleWords loc)
    (hlabel : loc.label = (if use256 then .l109037 else .l107ba7))
    (hindex : loc.arguments[5]'(by change 5 < 53; decide) = ⟨64, index⟩)
    (hKeyRead : Readable loc.store
      (sp + (index <<< 3) + (if use256 then 344 else 408)) 64)
    (hApart : (sp + 8).toNat + 64 ≤
        (sp + (index <<< 3) + (if use256 then 344 else 408)).toNat ∨
      (sp + (index <<< 3) + (if use256 then 344 else 408)).toNat + 64 ≤ (sp + 8).toNat)
    (hWords : WordsAt loc.store (sp + 8) 64 (Vector.ofFn planes))
    (hKeys : WordsAt loc.store
      (sp + (index <<< 3) + (if use256 then 344 else 408)) 64 (Vector.ofFn keys)) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches ⟨loc, []⟩ ⟨next, []⟩ ∧
      CipherWorkingState use256 code fr args mem sp scheduleWords next ∧
      next.label = (if index = (if use256 then 104 else 64) then
        (if use256 then .l108600 else .l107170)
        else (if use256 then .l1090d1 else .l107c41)) ∧
      WordsAt next.store (sp + 8) 64
        (Vector.ofFn (xorPlanes planes keys)) ∧
      (∀ r : Fin 53, r.val ∈ [3, 4, 5, 12, 13, 14, 15, 22, 39, 50, 51] →
        next.arguments[r.val]'r.isLt = loc.arguments[r.val]'r.isLt) ∧
      (∀ p : Fin 8, (next.arguments[(batchPlaneRegister p).val]'(batchPlaneRegister p).isLt).get 64 =
        xorPlanes planes keys p) := by
  have hlow := hwork.stack.readable.low
  have hTypes := hwork.typed
  have hsp := congrArg (Value.get 64) hwork.stackPointer
  have hIndex := congrArg (Value.get 64) hindex
  have hStack : Writable code loc.store (sp + 8) 64 :=
    hwork.stack.of_offsets (x := sp) (c := 8) (d := -296) rfl (BitVec.sub_eq_add_neg _ _) (by decide)
  obtain ⟨mid, hrun, hlabel', hwords', hplanes, hkeep, htyped, hwrite⟩ :=
    batch_key1 use256 code hcode loc.arguments loc.store sp index planes keys
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
  have hscratch : RamWriteFrame loc.store mid.store [span (sp - 296) 512] := by
    apply (RamWriteFrame.refl _ _).trans hwrite
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact ⟨_, List.mem_cons_self, by simp only [span, h8]; omega,
      by simp only [span, h8]; omega⟩
  obtain ⟨hf, hc⟩ := native_frame_of_scratch hwork hscratch
  have hw := native_frame (after := mid) hwork htyped
    ((hkeep 4 (by decide)).trans hwork.stackPointer)
    (fun r hr ↦ hkeep r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with h | h | h | h <;> rw [h] <;> decide)) hf hc
  exact ⟨mid, hreach, hw, hlabel', hwords', hkeep, hplanes⟩

end AesGcm.Proofs.Machine.CTR.Loop
