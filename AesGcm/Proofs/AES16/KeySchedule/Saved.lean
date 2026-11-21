import AesGcm.Proofs.AES16.KeySchedule.Entry

namespace AesGcm.Proofs.Machine.AES16.KeySchedule
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime
attribute [local irreducible] memLoad memStore

theorem entryMemory_saved (use256 : Bool) (args : Values Value Reg.count) (mem : Ram) :
    memLoad (entryMemory use256 args mem) (args[4].get 64 - 48) 64 = args[3].get 64 ∧
    memLoad (entryMemory use256 args mem) (args[4].get 64 - 40) 64 = args[12].get 64 ∧
    memLoad (entryMemory use256 args mem) (args[4].get 64 - 32) 64 = args[13].get 64 ∧
    memLoad (entryMemory use256 args mem) (args[4].get 64 - 24) 64 = args[14].get 64 ∧
    memLoad (entryMemory use256 args mem) (args[4].get 64 - 16) 64 = args[15].get 64 ∧
    memLoad (entryMemory use256 args mem) (args[4].get 64 - 8) 64 = args[5].get 64 ∧
    memLoad (entryMemory use256 args mem)
      (args[4].get 64 - (if use256 then 56 else 72)) 64 = args[7].get 64 ∧
    memLoad (entryMemory use256 args mem) (args[4].get 64) 64 =
      memLoad mem (args[4].get 64) 64 := by
  cases use256
  all_goals simp only [entryMemory, savedMemory, Bool.false_eq_true, ↓reduceIte]
  all_goals repeat' apply And.intro
  all_goals repeat' first
    | exact memLoad_memStore_same _ _ _ (by decide) (by decide)
    | rfl
    | (refine (memLoad_memStore_of_rangeApart _ _ _ _ _ ?_).trans ?_
       · first
           | exact RangeApart.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide +kernel)
           | exact RangeApart.of_offsets (addr_sub _ _) (show args[4].get 64 = args[4].get 64 + BitVec.ofInt 64 0 by simp) (by decide +kernel))

theorem saved_load_outside (use256 : Bool) (sp : BitVec 64)
    (hroom : 248 ≤ sp.toNat)
    (hlow : sp.toNat + (if use256 then 360 else 264) ≤ 2 ^ 32)
    (off : Nat) (hmax : off ≤ (if use256 then 360 else 264))
    (hoff : (if use256 then 312 else 216) ≤ off ∨ off = (if use256 then 304 else 192)) :
    Outside
      [span (sp - 248) 248, span (sp + (if use256 then 12 else 8))
        (if use256 then 240 else 176), span (sp + (if use256 then 288 else 200)) 16]
      (sp + BitVec.ofNat 64 off) 8 := by
  have hsub : (sp - 248).toNat = sp.toNat - 248 := by bv_omega
  have ha : (sp + BitVec.ofNat 64 off).toNat = sp.toNat + off := by
    cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at hlow hmax <;>
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat] <;>
      rw [Nat.mod_eq_of_lt (a := off) (by omega), Nat.mod_eq_of_lt (by omega)]
  have hb : (sp + (if use256 then 12 else 8)).toNat =
      sp.toNat + (if use256 then 12 else 8) := by
    cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> bv_omega
  have hr : (sp + (if use256 then 288 else 200)).toNat =
      sp.toNat + (if use256 then 288 else 200) := by
    cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> bv_omega
  refine ⟨?_, ?_⟩
  · rw [ha]
    cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> omega
  · intro r hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl | rfl
    all_goals simp only [span, hsub, ha, hb, hr]
    all_goals cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> omega

theorem return_load_outside (use256 : Bool) (sp dst : BitVec 64)
    (hroom : 8 ≤ sp.toNat)
    (hlow : sp.toNat + (if use256 then 360 else 264) ≤ 2 ^ 32)
    (hApart : dst.toNat + (if use256 then 240 else 176) ≤ sp.toNat ∨
      sp.toNat + (if use256 then 368 else 272) ≤ dst.toNat)
    (off : Nat) (hmin : (if use256 then 312 else 216) ≤ off)
    (hmax : off ≤ (if use256 then 360 else 264)) :
    Outside
      [span (sp - 8) 8, span (sp + (if use256 then 12 else 8))
        (if use256 then 276 else 184), span dst (if use256 then 240 else 176)]
      (sp + BitVec.ofNat 64 off) 8 := by
  have hsub : (sp - 8).toNat = sp.toNat - 8 := by bv_omega
  have ha : (sp + BitVec.ofNat 64 off).toNat = sp.toNat + off := by
    cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at hlow hmax <;>
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat] <;>
      rw [Nat.mod_eq_of_lt (a := off) (by omega), Nat.mod_eq_of_lt (by omega)]
  have hb : (sp + (if use256 then 12 else 8)).toNat =
      sp.toNat + (if use256 then 12 else 8) := by
    cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> bv_omega
  refine ⟨?_, ?_⟩
  · rw [ha]
    cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> omega
  · intro r hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl | rfl
    all_goals simp only [span, hsub, ha, hb]
    all_goals cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> omega

end AesGcm.Proofs.Machine.AES16.KeySchedule
