import AesGcm.Proofs.Common.Bitwise
import AesGcm.Proofs.Machine.Runtime.Tactics
import AesGcm.Proofs.Machine.LIR.Program

namespace AesGcm.Proofs.Machine.Tag.Execution

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
theorem finish_runBlock (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (dst mask : BitVec 64)
    (hstack : Writable code mem (args[4].get 64) 184)
    (hread : Readable mem (args[4].get 64) 192)
    (hdst : memLoad mem (args[4].get 64 + 128) 64 = dst)
    (hmask : memLoad mem (args[4].get 64 + 120) 64 = mask)
    (hw : Writable code mem dst 16) (hr : Readable mem mask 16)
    (hdstsep : (span (args[4].get 64) 192).Disjoint (span dst 16))
    (hmasksep : (span (args[4].get 64) 192).Disjoint (span mask 16))
    (hret : (memLoad mem (args[4].get 64 + 184) 64).toNat < 2^32) :
    ∃ output,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l101f22 else .l101b02), args, mem⟩ = .returned output ∧
      output.tag = some ⟨64, memLoad mem (args[4].get 64 + 184) 64⟩ ∧
      output.values[4] = ⟨64, args[4].get 64 + 192⟩ ∧
      output.values[3] = ⟨64, memLoad mem (args[4].get 64 + 136) 64⟩ ∧
      output.values[12] = ⟨64, memLoad mem (args[4].get 64 + 144) 64⟩ ∧
      output.values[13] = ⟨64, memLoad mem (args[4].get 64 + 152) 64⟩ ∧
      output.values[14] = ⟨64, memLoad mem (args[4].get 64 + 160) 64⟩ ∧
      output.values[15] = ⟨64, memLoad mem (args[4].get 64 + 168) 64⟩ ∧
      output.values[5] = ⟨64, memLoad mem (args[4].get 64 + 176) 64⟩ ∧
      (∀ r : Fin 53, r.val ∈ [22,39,50,51] → output.values[r] = args[r]) ∧
      (GPRsTyped args → GPRsTyped output.values) ∧
      RamWriteFrame mem output.store [span (args[4].get 64) 184, span dst 16] ∧
      (∀ i : Nat, i < 16 → memLoad output.store (dst + BitVec.ofNat 64 i) 8 =
        memLoad mem (args[4].get 64 + BitVec.ofNat 64 (64 + (15-i))) 8 ^^^
          memLoad mem (mask + BitVec.ofNat 64 i) 8) := by
  have hdstBounds := disjoint_bounds _ _ _ _ (by decide) (by decide) hdstsep
  have hmaskBounds := disjoint_bounds _ _ _ _ (by decide) (by decide) hmasksep
  have hstackLow := hread.low
  have hdstLow := hw.readable.low
  have hmaskLow := hr.low
  have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
      (h : Writable code m a n) :
      RangeApart a n (if use256 then 0x101f22 else 0x101b02) 272 := by
    cases use256
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l101b02 x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l101f22 x hx))).apart
  have hmaskAfter (b63 b15 : BitVec 8) :
      memLoad (memStore (memStore mem (args[4].get 64 + 63) b63)
        (args[4].get 64 + 15) b15) (args[4].get 64 + 120) 64 = mask := by
    runtime_finish [hmask]
  have hdstAfter (b63 b15 b62 b15' : BitVec 8) :
      memLoad (memStore (memStore (memStore (memStore mem (args[4].get 64 + 63) b63)
        (args[4].get 64 + 15) b15) (args[4].get 64 + 62) b62)
        (args[4].get 64 + 15) b15') (args[4].get 64 + 128) 64 = dst := by
    runtime_finish [hdst]
  have hrestoreDst (m : Ram) (i : BitVec 64) (hi : i.toNat < 16)
      (k : BitVec 64) (hk : 136 ≤ k.toNat) (hk' : k.toNat ≤ 184) (v : BitVec 8) :
      memLoad (memStore m (dst + i) v) (args[4].get 64 + k) 64 =
        memLoad m (args[4].get 64 + k) 64 := by
    runtime_finish []
  have hrestoreBase (m : Ram) (k : BitVec 64) (hk : 136 ≤ k.toNat)
      (hk' : k.toNat ≤ 184) (v : BitVec 8) :
      memLoad (memStore m dst v) (args[4].get 64 + k) 64 =
        memLoad m (args[4].get 64 + k) 64 := by
    runtime_finish []
  have hrestoreStack (m : Ram) (i : BitVec 64) (hi : i.toNat < 136)
      (k : BitVec 64) (hk : 136 ≤ k.toNat) (hk' : k.toNat ≤ 184) (v : BitVec 8) :
      memLoad (memStore m (args[4].get 64 + i) v)
        (args[4].get 64 + k) 64 = memLoad m (args[4].get 64 + k) 64 := by
    runtime_finish []
  runtime_context [hmaskAfter, hdstAfter, hdst, hmask, hdstBounds, hmaskBounds, hret,
    hstackLow, hdstLow, hmaskLow]
  cases use256
  all_goals simp only [Bool.false_eq_true, ↓reduceIte] at hhelperApart ⊢
  all_goals
    refine ⟨?_, ?exec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case exec =>
      first
        | change LIR.program.runBlock (dialect code) ⟨.l101b02, args, mem⟩ = _
        | change LIR.program.runBlock (dialect code) ⟨.l101f22, args, mem⟩ = _
      cfg_eval []
      simp only [hmaskAfter, hdstAfter]
      simp only [hrestoreDst, hrestoreBase, hrestoreStack, BitVec.reduceToNat,
        Nat.reduceLT, Nat.reduceLeDiff, hret, and_true]
      runtime_guards returned
      rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rintro ⟨r, hr⟩ hin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
      rcases hin with rfl | rfl | rfl | rfl <;> rfl
    · intro hTypes
      runtime_typed
    · runtime_finish [span]
    · intro i hi
      have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
          i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by omega
      rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals
        simp only [Nat.reduceSub, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
        runtime_finish [hdst, hmask, hdstBounds, hmaskBounds, hstackLow, hdstLow,
          hmaskLow, AesGcm.Proofs.setWidth_mergeGPR]

end AesGcm.Proofs.Machine.Tag.Execution
