import AesGcm.Proofs.Machine.CTR.Loop.CallAdvance

namespace AesGcm.Proofs.Machine.CTR.Loop

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime Fixslice

theorem header_step (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (fr : Activation) (args : Values Value Reg.count) (mem : Ram)
    (sp : BitVec 64) (keyWords : Vector (BitVec 16) (keyWords use256))
    (index tail key : BitVec 64) (planes : Planes) (loc : LIR.lifted.Location)
    (hwork : CipherWorkingState use256 code fr args mem sp keyWords loc)
    (hlabel : loc.label = (if use256 then .l109010 else .l107b80))
    (hindex : loc.arguments[5]'(by change 5 < 53; decide) = ⟨64, index⟩)
    (hTail : (loc.arguments[if use256 then 15 else 14]'
      (by change (if use256 then 15 else 14) < 53; cases use256 <;> decide)).get 64 = tail)
    (hKeyRead : Readable loc.store
      (sp + (index <<< 3) + (if use256 then 336 else 400)) 8)
    (hKey : memLoad loc.store
      (sp + (index <<< 3) + (if use256 then 336 else 400)) 64 = key)
    (hWords : WordsAt loc.store (sp + 8) 64
      (Vector.ofFn planes)) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches ⟨loc, []⟩ ⟨next, []⟩ ∧
      CipherWorkingState use256 code fr args mem sp keyWords next ∧
      next.label = batchMixLabel use256 false ∧
      WordsAt next.store (sp + 8) 64
        (Vector.ofFn (Fixslice.subBytes (fun p : Fin 8 =>
          if p.val = 7 then tail ^^^ key else planes p))) ∧
      next.arguments[3]'(by change 3 < 53; decide) = ⟨64, sp + 8⟩ ∧
      (∀ r : Fin Reg.count, r.val ∈ [4, 5, 12, 13, 22, 39, 50, 51] →
        next.arguments[r.val]'r.isLt = loc.arguments[r.val]'r.isLt) := by
  have low := hwork.stack.readable.low
  have stack : Writable code loc.store (sp - 8) 80 := by
    apply hwork.stack.sub <;> bv_omega
  obtain ⟨ca, hCall, hLabel, hCa4, hCa7, hCa6, hBase, hStore, hPres, hTyped, hWrite⟩ :=
    batch_header use256 code hcode loc.arguments loc.store sp index tail key hwork.typed
      (by rw [hwork.stackPointer]; rfl) (by rw [hindex]; rfl)
      hTail stack hKeyRead hKey
  have hCall' : LIR.program.runBlock (dialect code) loc = .call ca (batchHeaderFrame use256) := by
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
  have hRet : memLoad ca.store (sp - 8) 64 = (if use256 then 0x10902f else 0x107b9f) := by
    rw [hStore]
    exact memLoad_memStore_same _ _ _ (by decide) (by decide)
  have hPlanes : WordsAt ca.store (sp + 8) 64 (Vector.ofFn fun p : Fin 8 =>
      if p.val = 7 then tail ^^^ key else planes p) := by
    intro i hi
    rw [Vector.getElem_ofFn]
    by_cases last : i = 7
    · subst i
      simp only [↓reduceIte, wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
        BitVec.add_assoc, BitVec.reduceAdd]
      rw [hStore]
      have apart : RangeApart (sp - 8) 8 (sp + 64) 8 :=
        RangeApart.of_offsets (x := sp) (c := -8) (d := 64) (by bv_omega) rfl (by decide)
      rw [memLoad_memStore_of_rangeApart _ _ _ _ 64 apart]
      exact memLoad_memStore_same _ _ _ (by decide) (by decide)
    · simp only [last, ↓reduceIte]
      rw [← Vector.getElem_ofFn (f := planes), ← hWords i hi]
      apply hWrite.memLoad_eq
      have lt : i < 7 := by omega
      have off : (BitVec.ofNat 64 (8 * i)).toNat = 8 * i :=
        Nat.mod_eq_of_lt (by omega)
      simp only [wordAddr, Nat.reduceDiv]
      constructor
      · bv_omega
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · right; simp only [span]; bv_omega
        · left; simp only [span]; bv_omega
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
