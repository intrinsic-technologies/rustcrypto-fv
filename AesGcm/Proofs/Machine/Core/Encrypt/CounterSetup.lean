import AesGcm.Proofs.Machine.Core.Encrypt.Counter
import AesGcm.Proofs.Machine.Runtime.Atoms
import AesGcm.Proofs.Machine.LIR.Fn102520.Frame
import AesGcm.Proofs.Machine.LIR.Fn102980.Frame

namespace AesGcm.Proofs.Machine.Core.Encrypt

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem counter (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (fr : Activation) (loc : LIR.lifted.Location)
    (source destination : BitVec 64)
    (hlabel : loc.label = (if use256 then .l102a22 else .l1025c2))
    (hworking : Atom.All code loc.arguments loc.store
      (if use256 then LIR.Fn102980.frameAt .l102a22 fr else LIR.Fn102520.frameAt .l1025c2 fr))
    (hTypes : GPRsTyped loc.arguments)
    (hr : Readable loc.store fr.r9 24)
    (hsource : memLoad loc.store fr.r9 64 = source)
    (hdestination : memLoad loc.store (fr.r9 + 8) 64 = destination)
    (hsep : (callStack fr).Disjoint (span fr.r9 24)) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches ⟨loc, []⟩ ⟨next, []⟩ ∧
      next.label = (if ((loc.arguments[12]'(by change 12 < 53; decide)).get 64).toNat < 17 then
        (if use256 then .l102aaf else .l10264f) else (if use256 then .l102a59 else .l1025f9)) ∧
      Atom.All code next.arguments next.store
        (if use256 then LIR.Fn102980.frameAt .l102a22 fr else LIR.Fn102520.frameAt .l1025c2 fr) ∧
      GPRsTyped next.arguments ∧
      RamWriteFrame loc.store next.store [span (fr.rsp - 152) 28] ∧
      next.store = counterMemory loc.arguments loc.store ∧
      (next.arguments[1]'(by change 1 < 53; decide)).get 64 = fr.rsp - 144 ∧
      (next.arguments[5]'(by change 5 < 53; decide)).get 64 =
        (loc.arguments[12]'(by change 12 < 53; decide)).get 64 ∧
      (next.arguments[13]'(by change 13 < 53; decide)).get 64 = destination ∧
      (next.arguments[15]'(by change 15 < 53; decide)).get 64 = source := by
  rcases loc with ⟨label, args, mem⟩
  change Values Value Reg.count at args
  dsimp only at hlabel hworking hTypes hr hsource hdestination ⊢
  subst label
  let window : Nat := if use256 then 0xb50 else 0x940
  let slotHigh : Nat := if use256 then 0x201d88 else 0x201b78
  have h4 : args[4] = ⟨64, fr.rsp - 200⟩ := by
    apply atomsAll_mem hworking (atom := .gpr 4 (fr.rsp - 200))
    cases use256 <;> simp [LIR.Fn102980.frameAt, LIR.Fn102520.frameAt, LIR.Fn102980.frameAtG2, LIR.Fn102520.frameAtG2]
  have h14 : args[14] = ⟨64, fr.r9⟩ := by
    apply atomsAll_mem hworking (atom := .gpr 14 fr.r9)
    cases use256 <;> simp [LIR.Fn102980.frameAt, LIR.Fn102520.frameAt, LIR.Fn102980.frameAtG2, LIR.Fn102520.frameAtG2]
  have hstack : Writable code mem (fr.rsp - BitVec.ofNat 64 window) window := by
    apply atomsAll_mem hworking (atom := .writable (fr.rsp - BitVec.ofNat 64 window) window)
    cases use256 <;> simp [LIR.Fn102980.frameAt, LIR.Fn102520.frameAt, LIR.Fn102980.frameAtG2, LIR.Fn102520.frameAtG2, window]
  have hroom : fr.low.toNat + window ≤ fr.rsp.toNat := by
    apply atomsAll_mem hworking (atom := .fact (fr.low.toNat + window ≤ fr.rsp.toNat))
    cases use256 <;> simp [LIR.Fn102980.frameAt, LIR.Fn102520.frameAt, LIR.Fn102980.frameAtG2, LIR.Fn102520.frameAtG2, window]
  have hretRead : Readable mem fr.rsp 8 := by
    apply atomsAll_mem hworking (atom := .readable fr.rsp 8)
    cases use256 <;> simp [LIR.Fn102980.frameAt, LIR.Fn102520.frameAt, LIR.Fn102980.frameAtG2, LIR.Fn102520.frameAtG2]
  have hslotSep : slotHigh ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201208 := by
    apply atomsAll_mem hworking (atom := .fact (slotHigh ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201208))
    cases use256 <;> simp [LIR.Fn102980.frameAt, LIR.Fn102520.frameAt, LIR.Fn102980.frameAtG2, LIR.Fn102520.frameAtG2, slotHigh]
  have h4get : args[4].get 64 = fr.rsp - 200 := by rw [h4]; rfl
  have h14get : args[14].get 64 = fr.r9 := by rw [h14]; rfl
  have hwindow : 200 ≤ window := by cases use256 <;> decide
  have hretBound := hretRead.low
  have hsub (n : Nat) (hn : n ≤ 200) :
      (fr.rsp - BitVec.ofNat 64 n).toNat = fr.rsp.toNat - n := by
    have hle : BitVec.ofNat 64 n ≤ fr.rsp := by change n % 2^64 ≤ fr.rsp.toNat; omega
    rw [BitVec.toNat_sub_of_le hle, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hs200 : (fr.rsp - 200).toNat = fr.rsp.toNat - 200 := hsub 200 (by decide)
  have hs152 : (fr.rsp - 152).toNat = fr.rsp.toNat - 152 := hsub 152 (by decide)
  obtain ⟨next, hx, hl, hm, n0, n1, n5, n13, n15, keep, types⟩ :=
    counter_runBlock use256 code hcode args mem
      (by
        rw [h4get, show fr.rsp - 200 + 48 = fr.rsp - 152 by bv_omega]
        apply hstack.of_offsets (addr_sub _ _) (addr_sub _ _)
        cases use256 <;> decide +kernel)
      (by rw [h14get]; exact hr.of_offsets (addr_self _) (addr_self _) (by decide))
  have hf : RamWriteFrame mem next.store [span (fr.rsp - 152) 28] := by
    rw [hm]
    have hh := counterMemory_frame args mem (by rw [h4get, hs200]; omega)
    simpa only [h4get, show fr.rsp - 200 + 48 = fr.rsp - 152 by bv_omega] using hh
  have hb := disjoint_bounds fr.low.toNat (fr.rsp.toNat + 8 - fr.low.toNat)
    fr.r9.toNat 24 (by omega) (by decide) hsep
  have hdOutside : Outside [span (fr.rsp - 152) 28] fr.r9 24 := by
    refine ⟨by have := hr.low; omega, ?_⟩
    intro r hin
    obtain rfl := List.mem_singleton.mp hin
    simp only [span, hs152]
    omega
  have n13' : (next.arguments[13]'(by change 13 < 53; decide)).get 64 = destination := by
    rw [n13, h14get, ← hm, hf.memLoad_eq (outside_subregion (offset := 8) (count := 8) hdOutside (by decide) (by decide))]
    exact hdestination
  have n15' : (next.arguments[15]'(by change 15 < 53; decide)).get 64 = source := by
    have ho : Outside [span (fr.rsp - 152) 28] fr.r9 8 := by
      refine ⟨by have := hdOutside.1; omega, ?_⟩
      intro r hin
      have hh := hdOutside.2 r hin
      omega
    rw [n15, h14get, ← hm, hf.memLoad_eq ho]
    exact hsource
  have savedOutside (n : Nat) (hn : n ≤ 112) :
      Outside [span (fr.rsp - 152) 28] (fr.rsp - BitVec.ofNat 64 n) 8 := by
    refine ⟨by rw [hsub n (by omega)]; omega, ?_⟩
    intro r hin
    obtain rfl := List.mem_singleton.mp hin
    simp only [span, hs152, hsub n (by omega)]
    omega
  have slotOutside (a : BitVec 64) (ha0 : 0x201208 ≤ a.toNat) (ha1 : a.toNat + 8 ≤ 0x201238) :
      Outside [span (fr.rsp - 152) 28] a 8 := by
    refine ⟨by omega, ?_⟩
    intro r hin
    obtain rfl := List.mem_singleton.mp hin
    have hhigh : 0x201238 + 200 ≤ slotHigh := by cases use256 <;> decide
    simp only [span, hs152]
    omega
  refine ⟨next, .single (congrArg (Transfer.next (dialect code) []) hx), hl,
    ?_, types hTypes, hf, hm, ?_, n5, n13', n15'⟩
  · apply atomsAll_of_frame hf _ hworking
    intro atom ha
    cases use256
    all_goals
      simp only [LIR.Fn102980.frameAt, LIR.Fn102520.frameAt, LIR.Fn102980.frameAtG2, LIR.Fn102520.frameAtG2,
        Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact keep _ (by decide)
        | exact trivial
        | exact savedOutside _ (by decide)
        | exact (show Outside [span (fr.rsp - 152) 28] fr.rsp 8 from by
            simpa only [BitVec.ofNat_eq_ofNat, BitVec.sub_zero] using savedOutside 0 (by decide))
        | exact slotOutside _ (by decide) (by decide)
  · rw [n1, h4get]
    bv_omega

end AesGcm.Proofs.Machine.Core.Encrypt
