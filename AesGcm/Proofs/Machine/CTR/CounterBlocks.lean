import AesGcm.Proofs.Machine.CTR.CounterMemory
import AesGcm.Proofs.Machine.Fixslice.Memory

namespace AesGcm.Proofs.Machine.CTR
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine

def initialCounterBlock (mem : Ram) (counter : BitVec 64) : Vector UInt8 16 :=
  Vector.ofFn fun i : Fin 16 ↦
    storedByte (counterWord mem counter 0 ⟨i.val / 4, by omega⟩) (i.val % 4)

def counterBlocks (mem : Ram) (counter : BitVec 64) : Fixslice.Blocks :=
  fun b j ↦ (storedByte (counterWord mem counter b ⟨j.val / 4, by omega⟩) (j.val % 4)).toBitVec

set_option maxRecDepth 1024 in
theorem memoryBlocks_batchMemory (mem : Ram) (sp counter ret : BitVec 64)
    (hStackLow : (sp - 8).toNat + 328 ≤ 2 ^ 32)
    (hCounterLow : counter.toNat + 20 ≤ 2 ^ 32)
    (hroom : 8 ≤ sp.toNat)
    (hApart : sp.toNat + 320 ≤ counter.toNat ∨ counter.toNat + 20 ≤ sp.toNat - 8) :
    Fixslice.memoryBlocks (batchMemory mem sp counter ret) (sp + 256) =
      counterBlocks mem counter := by
  funext b j
  have hword := batchMemory_words mem sp counter ret hStackLow hCounterLow hroom hApart
    b ⟨j.val / 4, by omega⟩
  have hb := congrArg (fun w : BitVec 32 ↦ (storedByte w (j.val % 4)).toBitVec) hword
  rw [storedByte_memLoad _ _ _ (by omega)] at hb
  change (memByte _ ((sp + 256) + BitVec.ofNat 64 (16 * b.val) + BitVec.ofNat 64 j.val)).toBitVec = _
  have ha : sp + 256 + BitVec.ofNat 64 (16 * b.val) + BitVec.ofNat 64 j.val =
      sp + BitVec.ofNat 64 (256 + 16 * b.val + 4 * (j.val / 4)) + BitVec.ofNat 64 (j.val % 4) := by
    change sp + BitVec.ofNat 64 256 + BitVec.ofNat 64 (16 * b.val) + BitVec.ofNat 64 j.val = _
    simp only [BitVec.add_assoc, ← BitVec.ofNat_add]
    apply congrArg (fun n : Nat ↦ sp + BitVec.ofNat 64 n)
    omega
  rw [ha]
  exact hb

end AesGcm.Proofs.Machine.CTR
