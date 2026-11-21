import Standards.NIST.AES.KeyExpansion

/-!
# FIPS 197-upd1 §§5 and 5.1: CIPHER

AES-128, AES-192, and AES-256 are CIPHER with Nr = 10, 12, and 14 and the key schedule
KEYEXPANSION(key), FIPS 197-upd1 §5, Eq. (5.1).
FIPS 197 in the docstrings is FIPS 197-upd1.

Source: https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.197-upd1.pdf
-/

namespace Standards.NIST.AES

/--
CIPHER, FIPS 197 §5.1, Algorithm 1, keyed with KEYEXPANSION of `key`: ADDROUNDKEY with round
key 0; rounds 1 to Nr − 1 of SUBBYTES, SHIFTROWS, MIXCOLUMNS, and ADDROUNDKEY; and a final
round without MIXCOLUMNS
-/
def cipher (v : Variant) (key : Vector UInt8 v.keyBytes) (input : Block) : Block :=
  let w := keyExpansion v key
  let k := fun round : Nat => roundKey v w ⟨min round v.Nr, by omega⟩
  let state := addRoundKey input (k 0)
  let state := (List.range (v.Nr - 1)).foldl (fun state j =>
    addRoundKey (mixColumns (shiftRows (subBytes state))) (k (j + 1))) state
  addRoundKey (shiftRows (subBytes state)) (k v.Nr)

end Standards.NIST.AES
