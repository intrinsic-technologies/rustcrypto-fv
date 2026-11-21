import ChaCha20Poly1305.Proofs.Decrypt.HashRun

namespace ChaCha20Poly1305.Proofs.Decrypt.Hash
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open Poly1305 Standards.RFC.ChaCha20Poly1305

theorem loadPart {m : Ram} {p : BitVec 64} {w : Nat} (i k : Nat) (hi : 8*(i+k)≤w) :
    (memLoad m p w).extractLsb' (8*i) (8*k) = memLoad m (p+BitVec.ofNat 64 i) (8*k) := by
  rw [extractLsb'_memLoad _ _ _ _ (by omega) (by omega) (by omega)]
  simp

theorem loadJoin {m : Ram} {p : BitVec 64} (lo hi : Nat) :
    memLoad m p (8*hi+8*lo) = memLoad m (p+BitVec.ofNat 64 lo) (8*hi) ++ memLoad m p (8*lo) := by
  have l := loadPart (m := m) (p := p) (w := 8*hi+8*lo) 0 lo (by omega)
  have h := loadPart (m := m) (p := p) (w := 8*hi+8*lo) lo hi (by omega)
  simp only [Nat.mul_zero,show p+BitVec.ofNat 64 0=p from BitVec.add_zero p] at l
  rw [←h,←l,BitVec.extractLsb'_append_extractLsb']

theorem lastNat (s : ByteArray) : (word s (s.size/16)).toNat = blockNumber s (s.size/16) := by
  let i := 16*(s.size/16)
  have hi : i≤s.size := by dsimp [i]; omega
  have h := Bytes.upper s hi
  have bound := le_bound (s.extract i s.size)
  rw [ByteArray.size_extract,Nat.min_self] at bound
  have small : 256^(s.size-i) ≤ 256^16 := Nat.pow_le_pow_right (by decide) (by dsimp [i]; omega)
  change ((Bytes.packed s).extractLsb' (8*i) 128).toNat = leBytesToNum (s.extract i (16*(s.size/16+1)))
  rw [BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow,Bytes.packedNat,Bytes.pow_bytes,h,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le bound small)]
  congr 1
  apply ByteArray.ext
  simp only [ByteArray.data_extract]
  apply Array.extract_eq_extract_right.mpr
  rw [ByteArray.size_data]; dsimp [i]; omega

def tailBits (s : ByteArray) := (Bytes.packed s).extractLsb' (8*(16*(s.size/16))) (8*(s.size%16))

theorem paddedLoad {m : Ram} (s : ByteArray) (p : BitVec 64)
    (lo : memLoad m p (8*(s.size%16)) = tailBits s)
    (hi : memLoad m (p+BitVec.ofNat 64 (s.size%16)) (8*(16-s.size%16)) = 0) :
    memLoad m p 128 = word s (s.size/16) := by
  let r := s.size%16
  have hr : r<16 := Nat.mod_lt _ (by decide)
  have h := loadPart (m := m) (p := p) (w := 128) r (16-r) (by omega)
  rw [hi] at h
  have l := loadPart (m := m) (p := p) (w := 128) 0 r (by omega)
  simp only [Nat.mul_zero,show p+BitVec.ofNat 64 0=p from BitVec.add_zero p] at l
  change _ = memLoad m p (8*(s.size%16)) at l
  rw [lo] at l
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  by_cases low : j<8*r
  · have e := congrArg (fun b => BitVec.getLsbD b j) l
    simpa [tailBits,word,BitVec.getLsbD_extractLsb',low,r,hj] using e
  · have e := congrArg (fun b => BitVec.getLsbD b (j-8*r)) h
    simp only [BitVec.getLsbD_extractLsb',show j-8*r < 8*(16-r) by omega,decide_true,
      Bool.true_and,show 8*r+(j-8*r)=j by omega] at e
    have out : 8*s.size ≤ 8*(16*(s.size/16))+j := by dsimp [r] at low; omega
    simp only [word,BitVec.getLsbD_extractLsb',BitVec.getLsbD_of_ge (Bytes.packed s) _ out,Bool.and_false]
    exact e.trans BitVec.getLsbD_zero

end ChaCha20Poly1305.Proofs.Decrypt.Hash
