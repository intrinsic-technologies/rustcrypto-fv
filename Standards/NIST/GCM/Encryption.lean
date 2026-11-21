import Standards.NIST.GCM.GHASH
import Standards.NIST.GCM.GCTR

/-!
# SP 800-38D §§5.2.1 and 7.1: the authenticated encryption function

The supported lengths of the inputs (§5.2.1.1), the steps of Algorithm 4 (§7.1) that the
authenticated decryption function repeats, namely the pre-counter block `J_0` and the tag, and
GCM-AE itself, for any block cipher with a 128-bit block size and any tag length up to 128 bits.
The tag lengths are more general than the document: SP 800-38D, §5.2.1.2 allows only 128, 120,
112, 104, 96, 64 and 32 bits, and says an implementation shall not support others, so only
those seven values of `t` follow the document; the steps themselves are the same for every `t`.

Source: https://nvlpubs.nist.gov/nistpubs/Legacy/SP/nistspecialpublication800-38d.pdf
-/

namespace Standards.NIST.GCM

/--
The bit lengths an implementation supports for the IV, for the plaintext (which are also those
of the ciphertext, §5.2.2), and for the additional authenticated data (SP 800-38D, §5.2.1.1)
-/
structure SupportedLengths where
  IV : Nat → Bool
  P : Nat → Bool
  A : Nat → Bool

/--
The largest supported lengths SP 800-38D, §5.2.1.1 allows: `len(P) ≤ 2^39 − 256`,
`len(A) ≤ 2^64 − 1` and `1 ≤ len(IV) ≤ 2^64 − 1`
-/
def SupportedLengths.maximum : SupportedLengths where
  IV := fun n => 1 ≤ n && n ≤ 2 ^ 64 - 1
  P := fun n => n ≤ 2 ^ 39 - 256
  A := fun n => n ≤ 2 ^ 64 - 1

/--
The blocks `X_1, ..., X_m` of a bit string `X` of length `128m`, step 1 of GHASH (SP 800-38D,
§6.4, Algorithm 2), whose result `GHASH` takes as its input; the strings split here always have
a length that is a multiple of 128, and any bits after the last whole block would be dropped
-/
def blocks (X : Vector Bool n) : Array (Vector Bool 128) :=
  Array.ofFn fun i : Fin (n / 128) => Vector.ofFn fun b : Fin 128 =>
    X[128 * i.val + b.val]'(by omega)

/--
The pre-counter block `J_0` (SP 800-38D, §7.1, Algorithm 4, steps 1 and 2)

1. Let `H = CIPH_K(0^128)`.
2. If `len(IV) = 96`, then let `J_0 = IV || 0^31 || 1`. If `len(IV) ≠ 96`, then let
   `s = 128 ⌈len(IV)/128⌉ − len(IV)`, and let `J_0 = GHASH_H(IV || 0^{s+64} || [len(IV)]_64)`.
-/
def preCounterBlock (CIPH : Vector Bool 128 → Vector Bool 128) (IV : Vector Bool ivLen) :
    Vector Bool 128 :=
  let H := CIPH (zeros 128)
  if h : ivLen = 96 then
    (IV.cast h ++ zeros 31 ++ #v[true] : Vector Bool 128)
  else
    let s := 128 * ((ivLen + 127) / 128) - ivLen
    GHASH H (blocks (IV ++ zeros (s + 64) ++ integerToString 64 ivLen))

/--
The authentication tag of `C` and `A` under the IV, `T = MSB_t(GCTR_K(J_0, S))` (SP 800-38D,
§7.1, Algorithm 4, steps 1, 2 and 4 to 6, which Algorithm 5 repeats as steps 2, 3 and 5 to 7)

1. Let `H = CIPH_K(0^128)`.
2. Define the pre-counter block `J_0` from the IV (`preCounterBlock`).
4. Let `u = 128 ⌈len(C)/128⌉ − len(C)` and let `v = 128 ⌈len(A)/128⌉ − len(A)`.
5. Define a block, `S = GHASH_H(A || 0^v || C || 0^u || [len(A)]_64 || [len(C)]_64)`.
6. Let `T = MSB_t(GCTR_K(J_0, S))`.

The tag length `t` is at most 128, the length of the string `MSB_t` truncates; the module
documentation says which lengths the document allows.
-/
def authenticationTag (CIPH : Vector Bool 128 → Vector Bool 128) (t : Fin 129)
    (IV : Vector Bool ivLen) (A : Vector Bool aLen) (C : Vector Bool cLen) : Vector Bool t :=
  let H := CIPH (zeros 128)
  let J₀ := preCounterBlock CIPH IV
  let u := 128 * ((cLen + 127) / 128) - cLen
  let v := 128 * ((aLen + 127) / 128) - aLen
  let S := GHASH H
    (blocks (A ++ zeros v ++ C ++ zeros u ++ integerToString 64 aLen ++ integerToString 64 cLen))
  MSB t ((GCTR CIPH J₀ S).cast (by omega : 128 = t.val + (128 - t.val)))

/--
`GCM-AE_K(IV, P, A)` (SP 800-38D, §7.1, Algorithm 4)

Prerequisites: the forward cipher function `CIPH` of a block cipher with a 128-bit block size,
under the key K; the tag length `t`
Input: initialization vector `IV`; plaintext `P`; additional authenticated data `A`
Output: ciphertext `C`; authentication tag `T`

1. Let `H = CIPH_K(0^128)`.
2. Define a block, `J_0` (`preCounterBlock`).
3. Let `C = GCTR_K(inc_32(J_0), P)`.
4. Let `u` and `v` be the lengths of zero padding that complete `C` and `A` to whole blocks.
5. Define a block, `S = GHASH_H(A || 0^v || C || 0^u || [len(A)]_64 || [len(C)]_64)`.
6. Let `T = MSB_t(GCTR_K(J_0, S))`.
7. Return `(C, T)`.

Steps 1, 2 and 4 to 6 are `authenticationTag`. Neither the lengths (§5.2.1.1) nor `t` (§5.2.1.2)
are checked; see the module documentation.
-/
def GCM_AE (CIPH : Vector Bool 128 → Vector Bool 128) (t : Fin 129) (IV : Vector Bool ivLen)
    (P : Vector Bool pLen) (A : Vector Bool aLen) : Vector Bool pLen × Vector Bool t :=
  let J₀ := preCounterBlock CIPH IV
  let C := GCTR CIPH (inc 32 J₀) P
  (C, authenticationTag CIPH t IV A C)

end Standards.NIST.GCM
