import ChaCha20Poly1305.Proofs.Decrypt.FullRepeat
import ChaCha20Poly1305.Proofs.Decrypt.PolyContext

namespace ChaCha20Poly1305.Proofs.Decrypt.ChaChaRound
open Standards.RFC.ChaCha20Poly1305

private theorem blockByte (s : ByteArray) (b : Vector UInt8 64) (i : Nat)
    (h : i < (xorBlock s b).size) (small : i<64) :
    (xorBlock s b)[i] = s[i]'(xorBlock_size s b ▸ h) ^^^ b[i] := by
  simp only [xorBlock,ByteArray.getElem_eq_getElem_data,Array.getElem_ofFn,getElem!_pos b i small]
  rfl

private theorem appR (a b : ByteArray) (i : Nat) (lo : a.size ≤ i) (hi : i<a.size+b.size) :
    (a++b)[i]! = b[i-a.size]! := by
  rw [getElem!_pos _ i (by rw [ByteArray.size_append]; omega),ByteArray.getElem_append_right lo,
    getElem!_pos b _ (by omega)]

private theorem appL (a b : ByteArray) (i : Nat) (hi : i<a.size) : (a++b)[i]! = a[i]! := by
  rw [getElem!_pos _ i (by rw [ByteArray.size_append]; omega),
    ByteArray.getElem_append_left hi,getElem!_pos a i hi]

private theorem partByte (msg : ByteArray) (n endp i : Nat) (ks : Vector UInt8 64)
    (left : n*64 ≤ i) (right : i < min endp msg.size) (small : i<n*64+64) :
    (xorBlock (msg.extract (n*64) endp) ks)[i-64*n]! = msg[i]! ^^^ ks[i%64] := by
  have sz : (xorBlock (msg.extract (n*64) endp) ks).size = min endp msg.size - n*64 := by simp [xorBlock_size]
  rw [getElem!_pos _ _ (by omega),blockByte _ _ _ _ (by omega),ByteArray.getElem_extract,
    getElem!_pos msg i (by omega)]
  congr 1
  · apply getElem_congr_idx; omega
  · apply getElem_congr_idx; omega

private theorem prefixByte (key : Vector UInt8 32) (nonce : Vector UInt8 12) (ctr : Nat)
    (msg : ByteArray) (n i : Nat) (hn : n≤msg.size/64) (hi : i < 64*n) :
    (encryptedPrefix key nonce ctr msg n)[i]! =
      msg[i]! ^^^ (keyStreamAt key nonce ctr (i/64))[i%64] := by
  induction n with
  | zero => omega
  | succ n ih =>
    have sz := prefixSize key nonce ctr msg (n := n) (by omega)
    rw [encryptedPrefix]
    by_cases h : i<64*n
    · rw [appL _ _ _ (by omega),ih (by omega) h]
    · have right : i < min (n*64+64) msg.size := by omega
      rw [appR _ _ _ (by omega) (by rw [xorBlock_size,ByteArray.size_extract]; omega),
        sz,partByte _ _ _ _ _ (by omega) right (by omega),show i/64=n by omega]

theorem encryptByte (key : Vector UInt8 32) (nonce : Vector UInt8 12) (ctr : UInt32) (msg : ByteArray)
    (i : Nat) (hi : i<msg.size) :
    (chacha20Encrypt key ctr nonce msg)[i]! =
      msg[i] ^^^ (keyStreamAt key nonce ctr.toNat (i/64))[i%64] := by
  let n := msg.size/64
  have sz := prefixSize key nonce ctr.toNat msg (n := n) (Nat.le_refl _)
  have pre (ht : i<64*n) := prefixByte key nonce ctr.toNat msg n i (Nat.le_refl _) ht
  rw [encrypted_eq,← getElem!_pos msg i hi]
  change (if msg.size%64 ≠ 0 then encryptedPrefix key nonce ctr.toNat msg n ++ xorBlock (msg.extract (n*64) msg.size) (keyStreamAt key nonce ctr.toNat n)
    else encryptedPrefix key nonce ctr.toNat msg n)[i]! = _
  split
  · by_cases h : i<64*n
    · rw [appL _ _ _ (by omega),pre h]
    · have r : i<n*64+64 := by dsimp [n]; omega
      rw [appR _ _ _ (by omega) (by rw [xorBlock_size,ByteArray.size_extract,Nat.min_self]; omega), sz,
        partByte _ _ _ _ _ (by omega) (by omega) r,show i/64=n by omega]
  · exact pre (by dsimp [n]; omega)

theorem streamByte_eq (x : Stream.Input) (key : Vector UInt8 32) (nonce : Vector UInt8 12) (ctr : Nat)
    (hw : x.w = chachaState key (counterNonceWords 1 ctr nonce)) (i : Nat) :
    Stream.Control.streamByte x i = (keyStreamAt key nonce ctr (i/64))[i%64].toBitVec := by
  simp only [Stream.Control.streamByte, Stream.Control.atBlock,keyStreamAt,stream_eq,hw,
    Stream.Control.counterWord]

end ChaCha20Poly1305.Proofs.Decrypt.ChaChaRound
