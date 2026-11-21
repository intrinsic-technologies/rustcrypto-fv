import Hkdf.Proofs.Common.HMAC

namespace Hkdf.Proofs.NewExpand.Expand

open Standards.RFC Hkdf.Spec

def step (H : HKDF.Hash) (prk info : ByteArray)
    (state : ByteArray × ByteArray) (i : Nat) : ByteArray × ByteArray :=
  let block := Standards.RFC.HMAC.hmac H.hash H.blockBytes prk
    (state.2 ++ info ++ ⟨#[UInt8.ofNat i]⟩)
  (state.1 ++ block, block)

def blocks (H : HKDF.Hash) (prk info : ByteArray) (count : Nat) : ByteArray × ByteArray :=
  (List.range' 1 count).foldl (step H prk info) (ByteArray.empty, ByteArray.empty)

theorem expand_eq_blocks (H : HKDF.Hash) (prk info : ByteArray) (length : Nat) :
    HKDF.expand H prk info length =
      if length > 255 * H.hashLen then none else
        some ((blocks H prk info ((length + H.hashLen - 1) / H.hashLen)).1.extract 0 length) := by
  unfold HKDF.expand blocks
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Id.run, pure_bind, Std.Legacy.Range.size, Nat.add_sub_cancel, Nat.div_one]
  rfl

theorem blocks_zero (H : HKDF.Hash) (prk info : ByteArray) :
    blocks H prk info 0 = (ByteArray.empty, ByteArray.empty) := by
  rfl

theorem blocks_succ (H : HKDF.Hash) (prk info : ByteArray) (count : Nat) :
    blocks H prk info (count + 1) = step H prk info (blocks H prk info count) (count + 1) := by
  simp only [blocks, List.range'_1_concat, List.foldl_append, List.foldl_cons,
    List.foldl_nil, Nat.add_comm 1 count]

theorem blocks_sha256_size (prk info : ByteArray) (count : Nat) :
    (blocks .sha256 prk info count).1.size = 32 * count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    have ih' := ih
    simp only [HKDF.Hash.sha256] at ih'
    simp only [blocks_succ, step, HKDF.Hash.sha256, ByteArray.size_append,
      Hkdf.Proofs.Common.HMAC.hmac_sha256_size, ih', Nat.mul_succ]

theorem blocks_sha256_previous_size (prk info : ByteArray) {count : Nat}
    (positive : 0 < count) : (blocks .sha256 prk info count).2.size = 32 := by
  cases count with
  | zero => omega
  | succ count =>
    simp only [blocks_succ, step, HKDF.Hash.sha256,
      Hkdf.Proofs.Common.HMAC.hmac_sha256_size]

theorem expandFromPrk_sha256_blocks {prk info : ByteArray} {length : Nat}
    (prkEnough : 32 ≤ prk.size) (lengthBound : length ≤ 8160) :
    RFC5869.expandFromPrk .sha256 prk info length =
      .ok ((blocks .sha256 prk info ((length + 32 - 1) / 32)).1.extract 0 length) := by
  unfold RFC5869.expandFromPrk
  have hashLen : HKDF.Hash.sha256.hashLen = 32 := rfl
  simp only [hashLen]
  have notShort : ¬ prk.size < 32 := by omega
  simp only [notShort, ↓reduceIte]
  rw [expand_eq_blocks]
  simp only [HKDF.Hash.sha256]
  have bound : ¬ length > 255 * 32 := by omega
  simp only [bound, ↓reduceIte]


end Hkdf.Proofs.NewExpand.Expand
