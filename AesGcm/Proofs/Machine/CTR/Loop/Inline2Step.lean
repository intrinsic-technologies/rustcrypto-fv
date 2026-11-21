import AesGcm.Proofs.Machine.CTR.Loop.CallAdvance

namespace AesGcm.Proofs.Machine.CTR.Loop

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime Fixslice

theorem inline2_step
    (use256 : Bool) (code : CodeMap) (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (fr : Activation) (args : Values Value Reg.count) (mem : Ram)
    (sp : BitVec 64) (scheduleWords : Vector (BitVec 16) (keyWords use256))
    (index : BitVec 64) (planes keys : Planes) (loc : LIR.lifted.Location)
    (hwork : CipherWorkingState use256 code fr args mem sp scheduleWords loc)
    (hlabel : loc.label = (if use256 then .l1090e0 else .l107c50))
    (hindex : loc.arguments[5]'(by change 5 < 53; decide) = ⟨64, index⟩)
    (hKeyRead : Readable loc.store
      (sp + (index <<< 3) + (if use256 then 408 else 472)) 64)
    (hApart : (sp - 8).toNat + 160 ≤
        (sp + (index <<< 3) + (if use256 then 408 else 472)).toNat ∨
      (sp + (index <<< 3) + (if use256 then 408 else 472)).toNat + 64 ≤ (sp - 8).toNat)
    (hWords : WordsAt loc.store (sp + 8) 64 (Vector.ofFn planes))
    (hKeys : WordsAt loc.store
      (sp + (index <<< 3) + (if use256 then 408 else 472)) 64 (Vector.ofFn keys)) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches ⟨loc, []⟩ ⟨next, []⟩ ∧
      CipherWorkingState use256 code fr args mem sp scheduleWords next ∧
      next.label = batchMixLabel use256 true ∧
      WordsAt next.store (sp + 8) 64
        (Vector.ofFn (Fixslice.subBytes (xorPlanes (mixColumns2 planes) keys))) ∧
      next.arguments[3]'(by change 3 < 53; decide) = ⟨64, sp + 8⟩ ∧
      (∀ r : Fin Reg.count, r.val ∈ [4, 5, 22, 39, 50, 51] →
        next.arguments[r.val]'r.isLt = loc.arguments[r.val]'r.isLt) := by
  have low := hwork.stack.readable.low
  have stack : Writable code loc.store (sp - 8) 160 := by
    apply hwork.stack.sub <;> bv_omega
  obtain ⟨ca, hCall, hLabel, hCa4, hCa7, hCa6, hBase, hPlanes, hPres, hTyped, hWrite, hRet⟩ :=
    batch_inline2 use256 code hcode loc.arguments loc.store sp index planes keys hwork.typed
      (by rw [hwork.stackPointer]; rfl) (by rw [hindex]; rfl)
      stack hKeyRead hApart hWords hKeys
  have hCall' : LIR.program.runBlock (dialect code) loc = .call ca (batchInline2Frame use256) := by
    cases loc with
    | mk l vs m => change l = _ at hlabel; subst l; exact hCall
  have scratch : RamWriteFrame loc.store ca.store [span (sp - 296) 512] := by
    apply (RamWriteFrame.refl _ _).trans hWrite
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
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
  refine ⟨next, reach, hw, label, words, (same 3 (by decide)).trans hBase, ?_⟩
  intro r hr
  by_cases stackReg : r.val = 4
  · obtain ⟨_, _⟩ := r
    subst_vars
    exact hw.stackPointer.trans hwork.stackPointer.symm
  · apply (same r ?_).trans (hPres r ?_) <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢ <;> omega

end AesGcm.Proofs.Machine.CTR.Loop
