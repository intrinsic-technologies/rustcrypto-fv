import Standards.RFC.ChaCha20Poly1305
import ChaCha20Poly1305.Proofs.Common.Keystream

namespace ChaCha20Poly1305.Proofs.ChaCha20

open Standards.RFC.ChaCha20Poly1305

def rotl (x : UInt32) (n : Nat) : UInt32 := UInt32.ofBitVec (x.toBitVec.rotateLeft n)

def quarterRoundRol (a b c d : UInt32) : UInt32 × UInt32 × UInt32 × UInt32 :=
  let a := a + b
  let d := rotl (d ^^^ a) 16
  let c := c + d
  let b := rotl (b ^^^ c) 12
  let a := a + b
  let d := rotl (d ^^^ a) 8
  let c := c + d
  let b := rotl (b ^^^ c) 7
  (a, b, c, d)

def qroundRol (state : Vector UInt32 16) (x y z w : Fin 16) : Vector UInt32 16 :=
  let (a, b, c, d) := quarterRoundRol state[x] state[y] state[z] state[w]
  ((((state.set x a).set y b).set z c).set w d)

def doubleRound (state : Vector UInt32 16) : Vector UInt32 16 :=
  let state := qroundRol state 0 4 8 12
  let state := qroundRol state 1 5 9 13
  let state := qroundRol state 2 6 10 14
  let state := qroundRol state 3 7 11 15
  let state := qroundRol state 0 5 10 15
  let state := qroundRol state 1 6 11 12
  let state := qroundRol state 2 7 8 13
  qroundRol state 3 4 9 14

def runRounds (state : Vector UInt32 16) : Vector UInt32 16 :=
  let mixed := Nat.repeat doubleRound 10 state
  Vector.ofFn fun i => mixed[i] + state[i]

def keystreamBlock (key : Vector UInt8 32) (counter : UInt32) (nonce : Vector UInt8 12) :
    Vector UInt8 64 :=
  serialize (runRounds (initialState key counter nonce))

theorem rotl_eq_leftRoll (x : UInt32) (n : Nat) (hn : 0 < n) (hn' : n < 32) :
    rotl x n = leftRoll x n := by
  have hk : n % 32 = n := Nat.mod_eq_of_lt hn'
  apply UInt32.toBitVec_inj.mp
  simp only [rotl, leftRoll, hk, UInt32.toBitVec_ofBitVec, UInt32.toBitVec_or,
    UInt32.toBitVec_shiftLeft, UInt32.toBitVec_shiftRight]
  rw [BitVec.rotateLeft_def, hk]
  have h1 : (n.toUInt32.toBitVec % 32).toNat = n := by
    simp [Nat.toUInt32]; omega
  have h2 : ((32 - n).toUInt32.toBitVec % 32).toNat = 32 - n := by
    simp [Nat.toUInt32]; omega
  rw [BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', h1, h2]

theorem quarterRoundRol_eq (a b c d : UInt32) :
    quarterRoundRol a b c d = quarterRound a b c d := by
  simp only [quarterRoundRol, quarterRound, Id.run,
    rotl_eq_leftRoll _ 16 (by decide) (by decide), rotl_eq_leftRoll _ 12 (by decide) (by decide),
    rotl_eq_leftRoll _ 8 (by decide) (by decide), rotl_eq_leftRoll _ 7 (by decide) (by decide)]
  rfl

theorem qroundRol_eq (state : Vector UInt32 16) (x y z w : Fin 16) :
    qroundRol state x y z w = qround state x y z w := by
  simp only [qroundRol, qround, quarterRoundRol_eq]

theorem doubleRound_eq (state : Vector UInt32 16) : doubleRound state = innerBlock state := by
  simp only [doubleRound, innerBlock, qroundRol_eq]

theorem serialize_runRounds (key : Vector UInt8 32) (words : Vector UInt32 4) :
    serialize (runRounds (chachaState key words)) = chachaBlock key words := by
  have hd : doubleRound = innerBlock := funext doubleRound_eq
  simp only [runRounds, chachaBlock, hd, Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
  simp [Nat.repeat, List.range'_succ]
  rfl

theorem keystreamBlock_eq (key : Vector UInt8 32) (counter : UInt32) (nonce : Vector UInt8 12) :
    keystreamBlock key counter nonce = chacha20Block key counter nonce := by
  exact serialize_runRounds key _

theorem chachaEncrypt_eq_xorKeystream (key : Vector UInt8 32) (counter : Nat)
    (nonce : Vector UInt8 12) (message : ByteArray) :
    chachaEncrypt 1 key counter nonce message =
      Common.xorKeystream
        (fun j => chachaBlock key (counterNonceWords 1 ((counter + j) % 2 ^ 32) nonce)) message := by
  rfl

theorem chacha20Encrypt_eq_xorKeystream (key : Vector UInt8 32) (counter : UInt32)
    (nonce : Vector UInt8 12) (message : ByteArray) :
    chacha20Encrypt key counter nonce message =
      Common.xorKeystream (fun j => keystreamBlock key (counter + j.toUInt32) nonce) message := by
  have hks : (fun j => keystreamBlock key (counter + j.toUInt32) nonce) =
      fun j => chachaBlock key (counterNonceWords 1 ((counter.toNat + j) % 2 ^ 32) nonce) := by
    funext j
    rw [keystreamBlock_eq]
    unfold chacha20Block
    congr 2
    simp [UInt32.toNat_add, Nat.toUInt32]
  rw [hks]
  exact chachaEncrypt_eq_xorKeystream key counter.toNat nonce message

end ChaCha20Poly1305.Proofs.ChaCha20
