import ChaCha20Poly1305.Proofs.Decrypt.TailControl
import ChaCha20Poly1305.Proofs.Decrypt.XorEffect

namespace ChaCha20Poly1305.Proofs.Decrypt.Stream.Control
open Standards.RFC.ChaCha20Poly1305
open ChaChaRound

theorem remNat (x : Input) : (Tail.rem64 x.n).toNat = x.n.toNat % 64 := by
  rw [Tail.rem64,BitVec.toNat_setWidth_of_le (by decide),BitVec.toNat_and,BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt x.len]
  exact Nat.and_two_pow_sub_one_eq_mod _ 6

theorem remFourNat (x : Input) : (rem4 x).toNat = x.n.toNat % 4 := by
  rw [rem4,BitVec.toNat_setWidth_of_le (by decide),BitVec.toNat_and,BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt x.len]
  exact Nat.and_two_pow_sub_one_eq_mod _ 2

theorem maskFloor {w : Nat} (v : BitVec w) (k : Nat) :
    (v &&& (BitVec.allOnes w <<< k)).toNat = v.toNat / 2^k * 2^k := by
  rw [← BitVec.shiftLeft_ushiftRight,BitVec.toNat_shiftLeft,BitVec.toNat_ushiftRight,
    Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow,Nat.mod_eq_of_lt]
  have := v.isLt
  have := Nat.div_mul_le_self v.toNat (2^k)
  omega

theorem baseNat (x : Input) : (Tail.base64 x.n).toNat = x.n.toNat/64*64 :=
  maskFloor x.n 6

theorem groupsNat (x : Input) : (groups x).toNat = (x.n.toNat%64)/4*4 := by
  rw [groups,BitVec.toNat_setWidth_of_le (by decide)]
  rw [show (60 : BitVec 32) = 63 &&& (BitVec.allOnes 32 <<< 2) from rfl,← BitVec.and_assoc,maskFloor]
  rw [BitVec.toNat_and,BitVec.toNat_setWidth,Nat.mod_eq_of_lt x.len]
  change (x.n.toNat &&& (2^6-1))/4*4 = _
  rw [Nat.and_two_pow_sub_one_eq_mod]

theorem blocksNat (x : Input) : (x.n >>> 6).toNat = x.n.toNat/64 := by
  rw [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]

def atBlock (x : Input) (i : Nat) : Input :=
  {x with w := x.w.set 12 (x.w[12]+i.toUInt32)}

theorem atBlock_zero (x : Input) : atBlock x 0 = x := by
  simp [atBlock]

theorem atBlock_succ (x : Input) (i : Nat) :
    (atBlock x (i+1)).w = (atBlock x i).w.set 12 ((atBlock x i).w[12]+1) := by
  simp [atBlock,Vector.set_set,UInt32.add_assoc]

theorem blockIndex (x : Input) (i : Nat) (hi : i ≤ x.n.toNat/64) :
    ((BitVec.ofNat 64 i) <<< 6).toNat = i*64 := by
  have := x.len
  simp only [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq,BitVec.toNat_ofNat,Nat.reducePow,
    Nat.mod_eq_of_lt (show i < 2^64 by omega),Nat.mod_eq_of_lt (show i*64<2^64 by omega)]

theorem blockAddress (x : Input) (i : Nat) (hi : i ≤ x.n.toNat/64)
    (low : x.buf.toNat+x.n.toNat ≤ 2^32) :
    (blockPtr x (BitVec.ofNat 64 i)).toNat = x.buf.toNat+i*64 := by
  rw [blockPtr,BitVec.toNat_add,blockIndex x i hi,Nat.mod_eq_of_lt (by omega)]

theorem counterWord (key : Vector UInt8 32) (nonce : Vector UInt8 12) (ctr i : Nat) :
    (chachaState key (counterNonceWords 1 ctr nonce)).set 12
      ((chachaState key (counterNonceWords 1 ctr nonce))[12]+i.toUInt32) =
    chachaState key (counterNonceWords 1 ((ctr+i)%2^32) nonce) := by
  congr 1
  simp [chachaState,counterNonceWords,Vector.set]
  rw [UInt32.ofNat_mod_size,UInt32.ofNat_add]

end ChaCha20Poly1305.Proofs.Decrypt.Stream.Control
