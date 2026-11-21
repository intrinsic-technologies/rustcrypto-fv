import X86Proofs.Instructions.Bswap.Operation
import K256.Proofs.Common.Refine.Lemma.Region

namespace K256.Proofs.Common

open Prelude X86.Machine X86Proofs K256.Proofs.Refine

theorem bswapSpec_bswapSpec (x : BitVec 64) : bswapSpec (bswapSpec x) = x := by
  unfold bswapSpec
  conv => rhs; rw [← ofLanes_lane (w := 8) (by decide) (by decide) x]
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [getLsbD_ofLanes _ _ hk, getLsbD_ofLanes _ _ hk, lane_ofLanes _ _ (by omega)]
  rw [show 64 / 8 - 1 - (64 / 8 - 1 - k / 8) = k / 8 by omega]

theorem hasBytes_of_word_copy {before after : Ram} {src : MemoryRegion} {dst : BitVec 64}
    {bytes : ByteArray} {n : Nat} (input : src.HasBytes before bytes)
    (size : bytes.size = 8 * n) (readable : Readable after dst (8 * n))
    (copied : ∀ i < n, memLoad after (wordAddr dst 64 i) 64 =
      memLoad before (wordAddr (BitVec.ofNat 64 src.start) 64 i) 64) :
    (⟨dst.toNat, bytes.size⟩ : MemoryRegion).HasBytes after bytes := by
  let words := Vector.ofFn fun i : Fin n =>
    memLoad before (wordAddr (BitVec.ofNat 64 src.start) 64 i.val) 64
  have atDst : WordsAt after dst 64 words := by
    intro i hi
    rw [copied i hi, Vector.getElem_ofFn]
  apply atDst.hasBytes readable size
  intro j hj hw
  rw [Vector.getElem_ofFn, storedByte_memLoad _ _ _ (Nat.mod_lt _ (by decide))]
  have ha : wordAddr (BitVec.ofNat 64 src.start) 64 (j / 8) + BitVec.ofNat 64 (j % 8) =
      BitVec.ofNat 64 (src.start + j) := by
    simp only [wordAddr, ← BitVec.ofNat_add, Nat.add_assoc, Nat.div_add_mod, Nat.reduceDiv]
  change bytes[j] = memByte before
    (wordAddr (BitVec.ofNat 64 src.start) 64 (j / 8) + BitVec.ofNat 64 (j % 8))
  rw [ha]
  exact (congrArg (fun b => b.getD 0) (input.2 ⟨j, hj⟩)).symm

end K256.Proofs.Common
