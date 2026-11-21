import AesGcm.Proofs.Machine.Runtime.Tactics

namespace AesGcm.Proofs.Machine.CTR
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

def counterWord (mem : Ram) (counter : BitVec 64) (j q : Fin 4) : BitVec 32 :=
  if q.val < 3 then memLoad mem (counter + BitVec.ofNat 64 (4 * q.val)) 32
  else bswapSpec (memLoad mem (counter + 12) 32 + memLoad mem (counter + 16) 32 + BitVec.ofNat 32 j.val)

def batchMemory (mem : Ram) (sp counter ret : BitVec 64) : Ram :=
  let m1 := memStore mem (sp + 256) (memLoad mem counter 32)
  let m2 := memStore m1 (sp + 260) (memLoad mem (counter + 4) 32)
  let m3 := memStore m2 (sp + 264) (memLoad mem (counter + 8) 32)
  let m4 := memStore m3 (sp + 268) (bswapSpec (memLoad mem (counter + 12) 32 + memLoad mem (counter + 16) 32))
  let m5 := memStore m4 (sp + 272) (memLoad mem counter 32)
  let m6 := memStore m5 (sp + 276) (memLoad mem (counter + 4) 32)
  let m7 := memStore m6 (sp + 280) (memLoad mem (counter + 8) 32)
  let m8 := memStore m7 (sp + 284) (bswapSpec (memLoad mem (counter + 12) 32 + memLoad mem (counter + 16) 32 + 1))
  let m9 := memStore m8 (sp + 288) (memLoad mem counter 32)
  let m10 := memStore m9 (sp + 292) (memLoad mem (counter + 4) 32)
  let m11 := memStore m10 (sp + 296) (memLoad mem (counter + 8) 32)
  let m12 := memStore m11 (sp + 300) (bswapSpec (memLoad mem (counter + 12) 32 + memLoad mem (counter + 16) 32 + 2))
  let m13 := memStore m12 (counter + 16) (memLoad mem (counter + 16) 32 + 4)
  let m14 := memStore m13 (sp + 304) (memLoad mem counter 32)
  let m15 := memStore m14 (sp + 308) (memLoad mem (counter + 4) 32)
  let m16 := memStore m15 (sp + 312) (memLoad mem (counter + 8) 32)
  let m17 := memStore m16 (sp + 316) (bswapSpec (memLoad mem (counter + 12) 32 + memLoad mem (counter + 16) 32 + 3))
  let m18 := memStore m17 (sp + 64) (0 : BitVec 64)
  let m19 := memStore m18 (sp + 56) (0 : BitVec 64)
  let m20 := memStore m19 (sp + 48) (0 : BitVec 64)
  let m21 := memStore m20 (sp + 40) (0 : BitVec 64)
  let m22 := memStore m21 (sp + 32) (0 : BitVec 64)
  let m23 := memStore m22 (sp + 24) (0 : BitVec 64)
  let m24 := memStore m23 (sp + 16) (0 : BitVec 64)
  let m25 := memStore m24 (sp + 8) (0 : BitVec 64)
  memStore m25 (sp - 8) ret

set_option maxHeartbeats 400000 in
theorem batchMemory_counter (mem : Ram) (sp counter ret : BitVec 64)
    (hStackLow : (sp - 8).toNat + 328 ≤ 2 ^ 32)
    (hCounterLow : counter.toNat + 20 ≤ 2 ^ 32)
    (hroom : 8 ≤ sp.toNat)
    (hApart : sp.toNat + 320 ≤ counter.toNat ∨ counter.toNat + 20 ≤ sp.toNat - 8) :
    memLoad (batchMemory mem sp counter ret) (counter + 16) 32 =
      memLoad mem (counter + 16) 32 + 4 := by
  unfold batchMemory
  runtime_finish []

set_option maxHeartbeats 800000 in
theorem batchMemory_words (mem : Ram) (sp counter ret : BitVec 64)
    (hStackLow : (sp - 8).toNat + 328 ≤ 2 ^ 32)
    (hCounterLow : counter.toNat + 20 ≤ 2 ^ 32)
    (hroom : 8 ≤ sp.toNat)
    (hApart : sp.toNat + 320 ≤ counter.toNat ∨ counter.toNat + 20 ≤ sp.toNat - 8)
    (j q : Fin 4) :
    memLoad (batchMemory mem sp counter ret)
      (sp + BitVec.ofNat 64 (256 + 16 * j.val + 4 * q.val)) 32 =
        counterWord mem counter j q := by
  rcases j with ⟨j,hj⟩
  rcases q with ⟨q,hq⟩
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 := by omega
  rcases hj with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl
  all_goals
    simp only [counterWord, Nat.reduceLT, Nat.reduceAdd, Nat.reduceMul, ↓reduceIte]
    unfold batchMemory
    runtime_finish [BitVec.add_zero]

set_option maxHeartbeats 400000 in
theorem batchMemory_zero (mem : Ram) (sp counter ret : BitVec 64)
    (i : Fin 8) :
    memLoad (batchMemory mem sp counter ret) (sp + BitVec.ofNat 64 (8 + 8 * i.val)) 64 = 0 := by
  rcases i with ⟨i,hi⟩
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [Nat.reduceAdd, Nat.reduceMul]
    unfold batchMemory
    runtime_finish []

theorem batchMemory_ret (mem : Ram) (sp counter ret : BitVec 64) :
    memLoad (batchMemory mem sp counter ret) (sp - 8) 64 = ret := by
  unfold batchMemory
  exact memLoad_memStore_same _ _ _ (by decide) (by decide)

set_option maxHeartbeats 400000 in
theorem batchMemory_frame (mem : Ram) (sp counter ret : BitVec 64)
    (hStackLow : (sp - 8).toNat + 328 ≤ 2 ^ 32)
    (hCounterLow : counter.toNat + 20 ≤ 2 ^ 32)
    :
    RamWriteFrame mem (batchMemory mem sp counter ret)
      [span (sp - 8) 8, span (sp + 8) 64, span (sp + 256) 64, span (counter + 16) 4] := by
  unfold batchMemory
  runtime_finish [span]

end AesGcm.Proofs.Machine.CTR
