import AesGcm.Proofs.Machine.CTR.Loop.CallAdvance

namespace AesGcm.Proofs.Machine.CTR.Loop

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime Fixslice

theorem key3_step
    (use256 : Bool) (code : CodeMap) (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (fr : Activation) (args : Values Value Reg.count) (mem : Ram)
    (sp : BitVec 64) (scheduleWords : Vector (BitVec 16) (keyWords use256))
    (index : BitVec 64) (planes keys : Planes) (loc : LIR.lifted.Location)
    (hwork : CipherWorkingState use256 code fr args mem sp scheduleWords loc)
    (hlabel : loc.label = (if use256 then .l10932e else .l107e9e))
    (hindex : loc.arguments[5]'(by change 5 < 53; decide) = ⟨64, index⟩)
    (hBase : loc.arguments[3]'(by change 3 < 53; decide) = ⟨64, sp + 8⟩)
    (hKeyRead : Readable loc.store
      (sp + (index <<< 3) + (if use256 then 472 else 536)) 64)
    (hApart : (sp - 8).toNat + 80 ≤
        (sp + (index <<< 3) + (if use256 then 472 else 536)).toNat ∨
      (sp + (index <<< 3) + (if use256 then 472 else 536)).toNat + 64 ≤ (sp - 8).toNat)
    (hWords : WordsAt loc.store (sp + 8) 64 (Vector.ofFn planes))
    (hKeys : WordsAt loc.store
      (sp + (index <<< 3) + (if use256 then 472 else 536)) 64 (Vector.ofFn keys)) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches ⟨loc, []⟩ ⟨next, []⟩ ∧
      CipherWorkingState use256 code fr args mem sp scheduleWords next ∧
      next.label = (if use256 then .l1093a3 else .l107f13) ∧
      WordsAt next.store (sp + 8) 64
        (Vector.ofFn (Fixslice.subBytes (xorPlanes planes keys))) ∧
      (∀ r : Fin Reg.count, r.val ∈ [3, 5, 12, 13, 14, 15, 22, 39, 50, 51] →
        next.arguments[r.val]'r.isLt = loc.arguments[r.val]'r.isLt) := by
  have low := hwork.stack.readable.low
  have stack : Writable code loc.store (sp - 8) 80 := by
    apply hwork.stack.sub <;> bv_omega
  obtain ⟨ca, hCall, hLabel, hCa4, hCa7, hCa6, hPlanes, hPres, hTyped, hWrite, hRet⟩ :=
    batch_key3 use256 code hcode loc.arguments loc.store sp index planes keys hwork.typed
      (by rw [hwork.stackPointer]; rfl) (by rw [hindex]; rfl)
      (by rw [hBase]; rfl) stack hKeyRead hApart hWords hKeys
  have hCall' : LIR.program.runBlock (dialect code) loc = .call ca (batchKey3Frame use256) := by
    cases loc with
    | mk l vs m => change l = _ at hlabel; subst l; exact hCall
  have scratch : RamWriteFrame loc.store ca.store [span (sp - 296) 512] := by
    apply (RamWriteFrame.refl _ _).trans hWrite
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    all_goals
      refine ⟨_, List.mem_cons_self, ?_, ?_⟩ <;> simp only [span] <;> bv_omega
  obtain ⟨hf, hc⟩ := native_frame_of_scratch hwork scratch
  obtain ⟨next, reach, hw, label, words, same⟩ :=
    call_advance (kind := 0) hcode hwork hCall' hLabel hTyped hCa4 hCa7
      (fun _ => hCa6)
      (fun r hr => hPres r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        omega))
      hRet (by cases use256 <;> decide) hf hc hPlanes
  exact ⟨next, reach, hw, label, words, fun r hr => (same r hr).trans (hPres r hr)⟩

end AesGcm.Proofs.Machine.CTR.Loop
