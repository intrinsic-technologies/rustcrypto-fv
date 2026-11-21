import AesGcm.Proofs.Machine.Core.Decrypt.Setup
import AesGcm.Proofs.Machine.Runtime.Atoms
import AesGcm.Proofs.Machine.LIR.Fn1022c0.Frame
import AesGcm.Proofs.Machine.LIR.Fn102720.Frame

namespace AesGcm.Proofs.Machine.Core.Decrypt
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

set_option maxHeartbeats 1600000 in
theorem counter_reaches (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (fr : Activation)
    (args : Values Value Reg.count) (mem : Ram)
    (hworking : Atom.All code args mem
      (if use256 then LIR.Fn102720.frameAt .l102849 fr else LIR.Fn1022c0.frameAt .l1023e9 fr))
    (hTypes : GPRsTyped args) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches
        ⟨⟨(if use256 then .l102849 else .l1023e9), args, mem⟩, []⟩ ⟨next, []⟩ ∧
      next.label = (if (args[14].get 64).toNat < 17
        then (if use256 then .l1028dc else .l10247c)
        else (if use256 then .l102885 else .l102425)) ∧
      Atom.All code next.arguments next.store
        (if use256 then LIR.Fn102720.frameAt next.label fr else LIR.Fn1022c0.frameAt next.label fr) ∧
      GPRsTyped next.arguments ∧ RamWriteFrame mem next.store [span (fr.rsp - 128) 28] ∧
      (∀ r : Fin 53, r.val ∈ [0,3,4,5,12,13,14,22,39,50,51] → next.arguments[r] = args[r]) ∧
      next.arguments[15]'(by change 15 < 53; decide) = ⟨64, fr.rsp - 120⟩ ∧
      memLoad next.store (fr.rsp - 128) 64 = memLoad mem (fr.rsp - 144) 64 ∧
      memLoad next.store (fr.rsp - 120) 32 = memLoad mem (fr.rsp - 156) 32 ∧
      memLoad next.store (fr.rsp - 116) 32 = memLoad mem (fr.rsp - 160) 32 ∧
      memLoad next.store (fr.rsp - 112) 32 = memLoad mem (fr.rsp - 164) 32 ∧
      memLoad next.store (fr.rsp - 108) 32 = 1 ∧ memLoad next.store (fr.rsp - 104) 32 = 1 := by
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
  have n128 : (fr.rsp - 128).toNat = fr.rsp.toNat - 128 := hsub 128 (by decide)
  have hsp : args[4].get 64 = fr.rsp - 216 := by rw [h4]; rfl
  have ha (off : BitVec 64) : args[4].get 64 + off = fr.rsp - (216 - off) := by
    rw [hsp]; bv_omega
  have a88 : args[4].get 64 + 88 = fr.rsp - 128 := ha 88
  obtain ⟨next,hx,hl,hm,h1,h15,keep,typed⟩ := counter_runBlock use256 code hcode args mem
    (by rw [a88]; apply hw.of_offsets (addr_sub _ _) (addr_sub _ _); cases use256 <;> decide +kernel)
    (by rw [hsp]; apply hw.readable.of_offsets (addr_sub _ _) (addr_sub _ _); cases use256 <;> decide +kernel)
  have hf : RamWriteFrame mem next.store [span (fr.rsp - 128) 28] := by
    rw [hm, ← a88]
    exact counterMemory_frame args mem (by
      have n216 : (fr.rsp - 216).toNat = fr.rsp.toNat - 216 :=
        BitVec.toNat_sub_of_le (by change 216 ≤ fr.rsp.toNat; omega)
      rw [hsp, n216]
      have := hr.low
      omega)
  have before : Atom.All code args mem
      (if use256 then LIR.Fn102720.frameAt next.label fr else LIR.Fn1022c0.frameAt next.label fr) := by
    rw [hl]
    by_cases hlen : (args[14].get 64).toNat < 17
    all_goals cases use256 <;> simp only [hlen, Bool.false_eq_true, ↓reduceIte]
    all_goals
      rcases hworking with ⟨a4,a22,a5,a13,a15,a39,a50,a51,rest⟩
      exact ⟨a4,a22,a5,a13,a39,a50,a51,rest⟩
  have working : Atom.All code next.arguments next.store
      (if use256 then LIR.Fn102720.frameAt next.label fr else LIR.Fn1022c0.frameAt next.label fr) := by
    apply atomsAll_of_frame hf ?_ before
    intro atom hin
    rw [hl] at hin
    by_cases hlen : (args[14].get 64).toNat < 17
    all_goals cases use256 <;>
      simp only [hlen, Bool.false_eq_true, ↓reduceIte, LIR.Fn102720.frameAt, LIR.Fn102720.frameAtG2,
        LIR.Fn1022c0.frameAt, LIR.Fn1022c0.frameAtG1, LIR.Fn1022c0.frameAtG2,
        List.mem_cons, List.not_mem_nil, or_false] at hin
    all_goals
      rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact keep _ (by decide)
      | trivial
      | (change Outside [span (fr.rsp - 128) 28] _ _
         refine ⟨?_, ?_⟩
         · try simp only [n8,n16,n24,n32,n40,n48,n136,n152,BitVec.reduceToNat]
           have := hr.low
           omega
         · intro r hr'
           obtain rfl := List.mem_singleton.mp hr'
           simp only [span,n128,n8,n16,n24,n32,n40,n48,n136,n152,BitVec.reduceToNat]
           omega)
  have loads := counterMemory_loads args mem
  rw [← hm] at loads
  have addresses (n : BitVec 64) : args[4].get 64 + n = fr.rsp - (216 - n) := ha n
  have words : memLoad next.store (fr.rsp - 128) 64 = memLoad mem (fr.rsp - 144) 64 ∧
      memLoad next.store (fr.rsp - 120) 32 = memLoad mem (fr.rsp - 156) 32 ∧
      memLoad next.store (fr.rsp - 116) 32 = memLoad mem (fr.rsp - 160) 32 ∧
      memLoad next.store (fr.rsp - 112) 32 = memLoad mem (fr.rsp - 164) 32 ∧
      memLoad next.store (fr.rsp - 108) 32 = 1 ∧ memLoad next.store (fr.rsp - 104) 32 = 1 := by
    have a (n : BitVec 64) := addresses n
    simpa only [a, BitVec.reduceSub, BitVec.ofNat_eq_ofNat] using loads
  refine ⟨next, Semantics.Reaches.single ?_, hl, working, typed hTypes, hf, keep, ?_, words⟩
  · change LIR.program.step (dialect code) _ = .next _
    rw [Program.step,hx]
    rfl
  · rw [h15]
    congr 1
    exact ha 96

end AesGcm.Proofs.Machine.Core.Decrypt
