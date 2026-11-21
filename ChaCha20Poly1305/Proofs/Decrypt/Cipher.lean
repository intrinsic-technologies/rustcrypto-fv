import ChaCha20Poly1305.Proofs.Decrypt.ChaChaLoop
import Init.Data.Range.Lemmas
import Init.Data.ByteArray.Lemmas

namespace ChaCha20Poly1305.Proofs.Decrypt.ChaChaRound
open Standards.RFC.ChaCha20Poly1305

def stream (w : Vector UInt32 16) : Vector UInt8 64 :=
  serialize (Vector.ofFn fun i => (rounds 10 w)[i] + w[i])

theorem stream_eq (key : Vector UInt8 32) (words : Vector UInt32 4) :
    chachaBlock key words = stream (chachaState key words) := by
  unfold chachaBlock
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl]
  rfl

def xorBlock (block : ByteArray) (ks : Vector UInt8 64) : ByteArray :=
  ⟨Array.ofFn fun i : Fin block.size => block[i] ^^^ ks[i.val]!⟩

theorem xorBlock_size (data : ByteArray) (ks : Vector UInt8 64) :
    (xorBlock data ks).size = data.size := Array.size_ofFn

def keyStreamAt (key : Vector UInt8 32) (nonce : Vector UInt8 12) (ctr block : Nat) : Vector UInt8 64 :=
  chachaBlock key (counterNonceWords 1 ((ctr + block) % 2^32) nonce)

def encryptedPrefix (key : Vector UInt8 32) (nonce : Vector UInt8 12) (ctr : Nat)
    (msg : ByteArray) : Nat → ByteArray
  | 0 => .empty
  | n+1 => encryptedPrefix key nonce ctr msg n ++
    xorBlock (msg.extract (n*64) (n*64+64)) (keyStreamAt key nonce ctr n)

theorem prefixSize (key : Vector UInt8 32) (nonce : Vector UInt8 12) (ctr : Nat) (msg : ByteArray)
    {n : Nat} (h : n ≤ msg.size/64) : (encryptedPrefix key nonce ctr msg n).size = 64*n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [encryptedPrefix, ByteArray.size_append, xorBlock_size,ByteArray.size_extract,ih (by omega)]
    omega

theorem encrypted_eq (key : Vector UInt8 32) (nonce : Vector UInt8 12) (ctr : UInt32)
    (msg : ByteArray) :
    chacha20Encrypt key ctr nonce msg =
      let n := msg.size/64
      let full := encryptedPrefix key nonce ctr.toNat msg n
      if msg.size%64 ≠ 0 then full ++
        xorBlock (msg.extract (n*64) msg.size) (keyStreamAt key nonce ctr.toNat n)
      else full := by
  unfold chacha20Encrypt chachaEncrypt
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',List.forIn_pure_yield_eq_foldl,Std.Legacy.Range.size]
  have fold (n : Nat) :
      (List.range' 0 n).foldl (fun p j => p ++ xorBlock (msg.extract (j*64) (j*64+64))
        (keyStreamAt key nonce ctr.toNat j)) .empty = encryptedPrefix key nonce ctr.toNat msg n := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [List.range'_1_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, ih, Nat.zero_add]
      rfl
  simp only [Nat.sub_zero,Nat.add_one_sub_one,Nat.div_one]
  change (if _ then _ else _) = _
  split <;> simp_all only [xorBlock,keyStreamAt] <;> rfl

theorem encryptedSize (key : Vector UInt8 32) (nonce : Vector UInt8 12) (ctr : UInt32)
    (msg : ByteArray) : (chacha20Encrypt key ctr nonce msg).size = msg.size := by
  rw [encrypted_eq]
  dsimp only
  split
  · rw [ByteArray.size_append, xorBlock_size, ByteArray.size_extract, prefixSize _ _ _ _ (Nat.le_refl _)]
    omega
  · rw [prefixSize _ _ _ _ (Nat.le_refl _)]
    omega

end ChaCha20Poly1305.Proofs.Decrypt.ChaChaRound
