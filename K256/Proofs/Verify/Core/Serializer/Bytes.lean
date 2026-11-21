import K256.Proofs.Verify.LIR.Generated.Values

namespace K256.Proofs.Verify.Core.Serializer

open X86Proofs

private theorem lane_bswap (x : BitVec 64) (i : Nat) (h : i < 8) :
    lane 8 (bswapSpec x) i = lane 8 x (7 - i) :=
  lane_ofLanes _ _ h

theorem byte0 (x : BitVec 64) :
    BitVec.setWidth 8 ((bswapSpec x) >>> 56) = x.extractLsb' 0 8 := by
  exact lane_bswap x 7 (by decide)

theorem byte1 (x : BitVec 64) :
    BitVec.setWidth 8 ((bswapSpec x) >>> 48) = x.extractLsb' 8 8 := by
  exact lane_bswap x 6 (by decide)

theorem byte2 (x : BitVec 64) :
    BitVec.setWidth 8 ((bswapSpec x) >>> 40) = x.extractLsb' 16 8 := by
  exact lane_bswap x 5 (by decide)

theorem byte3 (x : BitVec 64) :
    BitVec.setWidth 8 ((bswapSpec x) >>> 32) = x.extractLsb' 24 8 := by
  exact lane_bswap x 4 (by decide)

theorem byte4 (x : BitVec 64) :
    BitVec.setWidth 8 ((BitVec.setWidth 32 (bswapSpec x)) >>> 24) = x.extractLsb' 32 8 := by
  rw [BitVec.setWidth_ushiftRight_eq_extractLsb, BitVec.extractLsb'_setWidth_of_le (by decide)]
  exact lane_bswap x 3 (by decide)

theorem byte5 (x : BitVec 64) :
    BitVec.setWidth 8 ((BitVec.setWidth 32 (bswapSpec x)) >>> 16) = x.extractLsb' 40 8 := by
  rw [BitVec.setWidth_ushiftRight_eq_extractLsb, BitVec.extractLsb'_setWidth_of_le (by decide)]
  exact lane_bswap x 2 (by decide)

theorem byte6 (x : BitVec 64) :
    (bswapSpec x).extractLsb' 8 8 = x.extractLsb' 48 8 := by
  exact lane_bswap x 1 (by decide)

theorem byte7 (x : BitVec 64) :
    BitVec.setWidth 8 (bswapSpec x) = x.extractLsb' 56 8 := by
  exact lane_bswap x 0 (by decide)

end K256.Proofs.Verify.Core.Serializer
