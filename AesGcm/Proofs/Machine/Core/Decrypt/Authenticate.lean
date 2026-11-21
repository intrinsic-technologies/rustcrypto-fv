import AesGcm.Proofs.Machine.Core.Decrypt.Authentication
import AesGcm.Proofs.Machine.Core.Decrypt.TagEquality
import AesGcm.Proofs.Machine.Runtime.Atoms
import AesGcm.Proofs.Machine.LIR.Fn1022c0.Frame
import AesGcm.Proofs.Machine.LIR.Fn102720.Frame

namespace AesGcm.Proofs.Machine.Core.Decrypt
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

set_option maxHeartbeats 1600000 in
theorem authenticate_reaches (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (fr : Activation)
    (args : Values Value Reg.count) (mem : Ram) (computed supplied : Vector UInt8 16)
    (hworking : Atom.All code args mem
      (if use256 then LIR.Fn102720.frameAt .l1027e8 fr else LIR.Fn1022c0.frameAt .l102388 fr))
    (hTypes : GPRsTyped args)
    (hcomputed : (span (fr.rsp - 80) 16).HasBytes mem ⟨computed.toArray⟩)
    (hprovided : Readable mem fr.r9 16)
    (hsupplied : (span fr.r9 16).HasBytes mem ⟨supplied.toArray⟩) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches
        ⟨⟨(if use256 then .l1027e8 else .l102388), args, mem⟩, []⟩ ⟨next, []⟩ ∧
      next.label = (if computed = supplied then (if use256 then .l102849 else .l1023e9)
        else (if use256 then .l102961 else .l102501)) ∧
      Atom.All code next.arguments next.store
        (if use256 then LIR.Fn102720.frameAt next.label fr else LIR.Fn1022c0.frameAt next.label fr) ∧
      GPRsTyped next.arguments ∧
      RamWriteFrame mem next.store [span (fr.rsp - 200) 1] ∧
      next.arguments[0].get 8 = (if computed = supplied then 0 else 1) ∧
      (∀ r : Fin 53, r.val ∈ [3,4,5,12,13,14,15,22,39,50,51] → next.arguments[r] = args[r]) := by
  let window : Nat := if use256 then 2912 else 2384
  have h4 : args[4] = ⟨64, fr.rsp - 216⟩ := by cases use256 <;> exact hworking.1
  have h13 : args[13] = ⟨64, fr.r9⟩ := by cases use256 <;> exact hworking.2.2.2.1
  have hw : Writable code mem (fr.rsp - BitVec.ofNat 64 window) window := by
    apply atomsAll_mem (atom := .writable (fr.rsp - BitVec.ofNat 64 window) window) hworking
    cases use256 <;> simp [LIR.Fn102720.frameAt, LIR.Fn102720.frameAtG2,
      LIR.Fn1022c0.frameAt, LIR.Fn1022c0.frameAtG1, window]
  have hroom : fr.low.toNat + window ≤ fr.rsp.toNat := by
    apply atomsAll_mem (atom := .fact (fr.low.toNat + window ≤ fr.rsp.toNat)) hworking
    cases use256 <;> simp [LIR.Fn102720.frameAt, LIR.Fn102720.frameAtG2,
      LIR.Fn1022c0.frameAt, LIR.Fn1022c0.frameAtG1, window]
  have hr : Readable mem fr.rsp 8 := by
    apply atomsAll_mem (atom := .readable fr.rsp 8) hworking
    cases use256 <;> simp [LIR.Fn102720.frameAt, LIR.Fn102720.frameAtG2,
      LIR.Fn1022c0.frameAt, LIR.Fn1022c0.frameAtG1]
  have hslots : 0x201238 + window ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201208 := by
    apply atomsAll_mem (atom := .fact (0x201238 + window ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201208)) hworking
    cases use256 <;> simp [LIR.Fn102720.frameAt, LIR.Fn102720.frameAtG2,
      LIR.Fn1022c0.frameAt, LIR.Fn1022c0.frameAtG1, window]
  have hwin : 216 ≤ window := by cases use256 <;> decide
  have n200 : (fr.rsp - 200).toNat = fr.rsp.toNat - 200 :=
    BitVec.toNat_sub_of_le (by change 200 ≤ fr.rsp.toNat; omega)
  have hsub (n : Nat) (hn : n ≤ 152) :
      (fr.rsp - BitVec.ofNat 64 n).toNat = fr.rsp.toNat - n := by
    rw [BitVec.toNat_sub_of_le (by change n % 2^64 ≤ fr.rsp.toNat; omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have n8 : (fr.rsp - 8).toNat = fr.rsp.toNat - 8 := hsub 8 (by decide)
  have n16 : (fr.rsp - 16).toNat = fr.rsp.toNat - 16 := hsub 16 (by decide)
  have n24 : (fr.rsp - 24).toNat = fr.rsp.toNat - 24 := hsub 24 (by decide)
  have n32 : (fr.rsp - 32).toNat = fr.rsp.toNat - 32 := hsub 32 (by decide)
  have n40 : (fr.rsp - 40).toNat = fr.rsp.toNat - 40 := hsub 40 (by decide)
  have n48 : (fr.rsp - 48).toNat = fr.rsp.toNat - 48 := hsub 48 (by decide)
  have n136 : (fr.rsp - 136).toNat = fr.rsp.toNat - 136 := hsub 136 (by decide)
  have n152 : (fr.rsp - 152).toNat = fr.rsp.toNat - 152 := hsub 152 (by decide)
  have hsp : args[4].get 64 = fr.rsp - 216 := by rw [h4]; rfl
  have htag : args[13].get 64 = fr.r9 := by rw [h13]; rfl
  have ha (off : BitVec 64) : args[4].get 64 + off = fr.rsp - (216 - off) := by
    rw [hsp]; bv_omega
  have a16 : args[4].get 64 + 16 = fr.rsp - 200 := ha 16
  obtain ⟨next, hx, hl, hm, hal, keep, typed⟩ := authenticate_runBlock use256 code hcode args mem
    (by rw [ha]; apply hw.of_offsets (addr_sub _ _) (addr_sub _ _); cases use256 <;> decide +kernel)
    (by rw [ha]; apply hw.readable.of_offsets (addr_sub _ _) (addr_sub _ _); cases use256 <;> decide +kernel)
    (by rw [htag]; exact hprovided)
  have heq : (memLoad mem (args[4].get 64 + 136) 64 = memLoad mem (args[13].get 64) 64 ∧
      memLoad mem (args[4].get 64 + 144) 64 = memLoad mem (args[13].get 64 + 8) 64) ↔
      computed = supplied := by
    have a136 : args[4].get 64 + 136 = fr.rsp - 80 := by rw [hsp]; bv_omega
    have a144 : args[4].get 64 + 144 = fr.rsp - 80 + 8 := by rw [hsp]; bv_omega
    rw [a136, a144, htag]
    exact tag_words_eq_iff hcomputed hsupplied
  simp only [heq] at hl hm hal
  rw [a16] at hm
  have hf : RamWriteFrame mem next.store [span (fr.rsp - 200) 1] := by
    rw [hm]
    apply (RamWriteFrame.refl _ _).memStore
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    simp only [InRegion, span, n200]
    have := hr.low
    omega
  have preserved : Atom.All code next.arguments next.store
      (if use256 then LIR.Fn102720.frameAt .l1027e8 fr else LIR.Fn1022c0.frameAt .l102388 fr) := by
    apply atomsAll_of_frame hf ?_ hworking
    intro atom hin
    cases use256 <;>
      simp only [Bool.false_eq_true, ↓reduceIte, LIR.Fn102720.frameAt, LIR.Fn102720.frameAtG2,
        LIR.Fn1022c0.frameAt, LIR.Fn1022c0.frameAtG1, List.mem_cons, List.not_mem_nil, or_false] at hin
    all_goals
      rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact keep _ (by decide)
      | trivial
      | (change Outside [span (fr.rsp - 200) 1] _ _
         refine ⟨?_, ?_⟩
         · try simp only [n8, n16, n24, n32, n40, n48, n136, n152, BitVec.reduceToNat]
           have := hr.low
           omega
         · intro r hr'
           obtain rfl := List.mem_singleton.mp hr'
           simp only [span, n200, n8, n16, n24, n32, n40, n48, n136, n152, BitVec.reduceToNat]
           omega)
  have working : Atom.All code next.arguments next.store
      (if use256 then LIR.Fn102720.frameAt next.label fr else LIR.Fn1022c0.frameAt next.label fr) := by
    rw [hl]
    by_cases he : computed = supplied
    · cases use256 <;> simpa only [he, Bool.false_eq_true, ↓reduceIte,
        LIR.Fn102720.frameAt, LIR.Fn102720.frameAtG2, LIR.Fn1022c0.frameAt, LIR.Fn1022c0.frameAtG1] using preserved
    · cases use256 <;>
        simp only [he, ↓reduceIte, LIR.Fn102720.frameAt, LIR.Fn102720.frameAtG2,
          LIR.Fn1022c0.frameAt, LIR.Fn1022c0.frameAtG1] at preserved ⊢
      all_goals
        rcases preserved with ⟨h4,h22,h5,h13,h15,h39,h50,h51,hd,ha,hs3,hs12,hs13,hs14,hs15,hs5,
          hr,hret,hrl,hw,hroom,halign,rest⟩
        exact ⟨h4,h22,h39,h50,h51,hs3,hs12,hs13,hs14,hs15,hs5,hr,hret,hrl,hw,hroom,halign,True.intro⟩
  refine ⟨next, Semantics.Reaches.single ?_, hl, working, typed hTypes, hf, hal, keep⟩
  change LIR.program.step (dialect code) _ = .next _
  rw [Program.step, hx]
  rfl

end AesGcm.Proofs.Machine.Core.Decrypt
