import ChaCha20Poly1305.Proofs.Decrypt.CipherBytes
import ChaCha20Poly1305.Proofs.Decrypt.StreamContract

namespace ChaCha20Poly1305.Proofs.Decrypt.Stream
open Standards.RFC.ChaCha20Poly1305 ChaChaRound

def words (key : Vector UInt8 32) (nonce : Vector UInt8 12) (ctr : Nat) :=
  chachaState key (counterNonceWords 1 ctr nonce)

def keyInput (key : Vector UInt8 32) (nonce : Vector UInt8 12) (buf : BitVec 64) : Input :=
  ⟨words key nonce 0,buf,32,by decide⟩

def encode (s : ByteArray) (n : Nat) := (Bytes.packed s).setWidth (8*n)

theorem encodeByte (s : ByteArray) {n i : Nat} (hn : s.size=n) (hi : i<n) :
    (encode s n).extractLsb' (8*i) 8 = (s[i]!).toBitVec := by
  subst n
  simpa [encode,getElem!_pos s i hi] using Bytes.byte s hi

set_option maxRecDepth 10000
set_option maxHeartbeats 400000

private theorem keyByte (k : Vector UInt8 32) (i : Nat) (hi : i<32) :
    (Poly1305.keyBits k).extractLsb' (8*i) 8 = k[i].toBitVec := by
  let s : ByteArray := k
  have sz : s.size=32 := k.size_toArray
  have h := Bytes.byte s (i := i) (by omega)
  apply BitVec.eq_of_toNat_eq
  have bound := Poly1305.le_bound s
  rw [sz] at bound
  rw [BitVec.extractLsb'_toNat,Poly1305.keyBits,BitVec.toNat_ofNat,Nat.mod_eq_of_lt bound]
  have e := congrArg BitVec.toNat h
  simp only [BitVec.extractLsb'_toNat,Bytes.packedNat] at e
  exact e

private theorem firstByte (key : Vector UInt8 32) (nonce : Vector UInt8 12) (buf : BitVec 64)
    (i : Nat) (hi : i<32) :
    Control.streamByte (keyInput key nonce buf) i = (poly1305KeyGen key nonce)[i].toBitVec := by
  have h := streamByte_eq (keyInput key nonce buf) key nonce 0 rfl i
  rw [show i/64=0 by omega] at h
  refine h.trans (congrArg UInt8.toBitVec ?_)
  simp only [poly1305KeyGen,Vector.getElem_ofFn]
  change (chacha20Block key 0 nonce)[i%64] = (chacha20Block key 0 nonce)[i]
  apply getElem_congr_idx; omega

theorem keyCorrect (key : Vector UInt8 32) (nonce : Vector UInt8 12) (buf : BitVec 64) :
    (fn (keyInput key nonce buf) 0 (Poly1305.keyBits (poly1305KeyGen key nonce))).Correct := by
  apply correct (keyInput key nonce buf) (0#256) (Poly1305.keyBits (poly1305KeyGen key nonce)) (by change 0≤1; decide)
  intro i hi
  change i<32 at hi
  change (Poly1305.keyBits _).extractLsb' (8*i) 8 = Control.streamByte (keyInput key nonce buf) i ^^^ (0#256).extractLsb' (8*i) 8
  simp only [BitVec.extractLsb'_zero,BitVec.xor_zero]
  exact (keyByte _ _ hi).trans (firstByte _ _ _ _ hi).symm

theorem messageCorrect (x : Input) (key : Vector UInt8 32) (nonce : Vector UInt8 12) (msg : ByteArray)
    (hw : x.w = words key nonce 1) (hlen : msg.size=x.n.toNat) :
    (fn x (encode msg x.n.toNat) (encode (chacha20Encrypt key 1 nonce msg) x.n.toNat)).Correct := by
  apply correct _ _ _ (hw ▸ (show (1:Nat)≤1 from Nat.le_refl _))
  intro i hi
  rw [encodeByte _ ((encryptedSize ..).trans hlen) hi,encryptByte _ _ _ _ _ (by omega),
    encodeByte _ hlen hi,streamByte_eq x key nonce 1 hw,getElem!_pos _ i (by omega)]
  exact BitVec.xor_comm ..

end ChaCha20Poly1305.Proofs.Decrypt.Stream
