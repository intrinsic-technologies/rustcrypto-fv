import ChaCha20Poly1305.Proofs.Decrypt.PolyContext
import ChaCha20Poly1305.Proofs.Decrypt.TagCompare

namespace ChaCha20Poly1305.Proofs.Decrypt.Poly1305
open Standards.RFC.ChaCha20Poly1305

private theorem byteNat (n : Nat) : (UInt8.ofNat n).toNat = n%256 := rfl

theorem num8 (n : Nat) : leBytesToNum (numTo8LeBytes n) = n%2^64 := by
  simp only [leBytesToNum,numTo8LeBytes,←Array.foldr_toList,Array.toList_ofFn,List.ofFn_succ,
    List.ofFn_zero,List.foldr_cons,List.foldr_nil,Fin.val_succ,Fin.val_zero,byteNat,
    Nat.reduceAdd,Nat.reducePow,Nat.div_one]
  omega

theorem lengths (a c : BitVec 64) : (c ++ a).toNat = lengthBlock a.toNat c.toNat := by
  rw [lengthBlock,le_append,num8,num8,Nat.mod_eq_of_lt a.isLt,Nat.mod_eq_of_lt c.isLt]
  have sz : (numTo8LeBytes a.toNat).size = 8 := Array.size_ofFn
  rw [sz,BitVec.toNat_append,←Nat.shiftLeft_add_eq_or_of_lt a.isLt,Nat.shiftLeft_eq]
  omega

def tagBits (t : Vector UInt8 16) : BitVec 128 := BitVec.ofNat _ (leBytesToNum (t : ByteArray))

theorem tagNat (n : Nat) : (tagBits (numTo16LeBytes n)).toNat = n%2^128 := by
  rw [tagBits,BitVec.toNat_ofNat]
  change ((Array.ofFn (fun i : Fin 16 => UInt8.ofNat (n/256^i.val))).foldr (fun byte num => byte.toNat+256*num) 0)%2^128 = _
  simp only [←Array.foldr_toList,Array.toList_ofFn,List.ofFn_succ,List.ofFn_zero,List.foldr_nil,List.foldr_cons,
    Fin.val_succ,Fin.val_zero,byteNat,Nat.reduceAdd,Nat.reducePow,Nat.div_one]
  omega

theorem tagInj {a b : Vector UInt8 16} : tagBits a = tagBits b ↔ a=b := by
  refine ⟨fun h => ?_,congrArg _⟩
  have atByte (k : Vector UInt8 16) (i : Nat) (hi : i<16) :
      (tagBits k).extractLsb' (8*i) 8 = k[i].toBitVec := by
    let s : ByteArray := k
    have sz : s.size=16 := k.size_toArray
    have hb := le_bound s
    rw [sz] at hb
    have e := congrArg BitVec.toNat (Bytes.byte s (i := i) (by omega))
    simp only [BitVec.extractLsb'_toNat,Bytes.packedNat] at e
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.extractLsb'_toNat,tagBits,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hb]
    exact e
  apply Vector.ext
  intro i hi
  apply UInt8.toBitVec_inj.mp
  rw [←atByte a i hi,h,atByte b i hi]

def tagValue (x : Finish.Input) : BitVec 128 :=
  (Finish.v101e0e x ++ (Finish.v101e02 x).setWidth 32) ++ ((Finish.v101df5 x).setWidth 32 ++ Finish.v101dec x)

private theorem join32 (a b : BitVec 32) : (a++b).toNat = b.toNat + 2^32*a.toNat := by
  rw [BitVec.toNat_append,←Nat.shiftLeft_add_eq_or_of_lt b.isLt,Nat.shiftLeft_eq]
  omega

theorem tagValueNat (x : Finish.Input) : (tagValue x).toNat = Finish.tagNum x := by
  rw [tagValue,BitVec.toNat_append,←Nat.shiftLeft_add_eq_or_of_lt (BitVec.isLt _),Nat.shiftLeft_eq,join32,join32]
  unfold Finish.tagNum Finish.wordsNum
  omega

theorem tagEquals {key : Vector UInt8 32} {a c : ByteArray} {ws : Vector (BitVec 32) 5}
    (h : represents ws (stepAcc (rKey key)
      (foldFrom c (rKey key) (foldFrom a (rKey key) 0 (count a)) (count c)) (lengthBlock a.size c.size))) :
    tagValue ⟨sWords key,ws⟩ = tagBits (poly1305Mac (aeadMacData a c) key) := by
  apply BitVec.eq_of_toNat_eq
  rw [tagValueNat,finishRep h,mac_parts,tagNat]

theorem halves {a b : BitVec 128} : (a.extractLsb' 0 64 = b.extractLsb' 0 64 ∧
    a.extractLsb' 64 64 = b.extractLsb' 64 64) ↔ a=b := by
  constructor
  · rintro ⟨h,l⟩
    have h := congrArg BitVec.toNat h
    have l := congrArg BitVec.toNat l
    simp only [BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow,Nat.reducePow] at *
    apply BitVec.eq_of_toNat_eq
    have := a.isLt; have := b.isLt; omega
  · rintro rfl; exact ⟨rfl,rfl⟩

end ChaCha20Poly1305.Proofs.Decrypt.Poly1305
