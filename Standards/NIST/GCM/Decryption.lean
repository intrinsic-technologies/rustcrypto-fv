import Standards.NIST.GCM.Encryption

/-!
# SP 800-38D §7.2: the authenticated decryption function

GCM-AD, Algorithm 5 of NIST SP 800-38D, §7.2, for any block cipher with a 128-bit block size,
any supported lengths and any tag length up to 128 bits, as in `Standards.NIST.GCM.Encryption`.
`none` is the document's `FAIL`.

Source: https://nvlpubs.nist.gov/nistpubs/Legacy/SP/nistspecialpublication800-38d.pdf
-/

namespace Standards.NIST.GCM

/--
`GCM-AD_K(IV, C, A, T)` (SP 800-38D, §7.2, Algorithm 5)

Prerequisites: the forward cipher function `CIPH` of a block cipher with a 128-bit block size,
under the key K; the supported lengths; the tag length `t`
Input: initialization vector `IV`; ciphertext `C`; additional authenticated data `A`;
authentication tag `T`
Output: plaintext `P` or the indication of inauthenticity `FAIL` (`none`)

1. If the bit lengths of `IV`, `A` or `C` are not supported, or if `len(T) ≠ t`, then return
   `FAIL`.
2. Let `H = CIPH_K(0^128)`.
3. Define a block, `J_0`, as for the authenticated encryption function (`preCounterBlock`).
4. Let `P = GCTR_K(inc_32(J_0), C)`.
5. Let `u` and `v` be the lengths of zero padding that complete `C` and `A` to whole blocks.
6. Define a block, `S = GHASH_H(A || 0^v || C || 0^u || [len(A)]_64 || [len(C)]_64)`.
7. Let `T′ = MSB_t(GCTR_K(J_0, S))`.
8. If `T = T′`, then return `P`; else return `FAIL`.

Steps 2, 3 and 5 to 7 are `authenticationTag`.
-/
def GCM_AD (CIPH : Vector Bool 128 → Vector Bool 128) (t : Fin 129)
    (supported : SupportedLengths) (IV : Vector Bool ivLen) (C : Vector Bool cLen)
    (A : Vector Bool aLen) (T : Vector Bool tLen) : Option (Vector Bool cLen) :=
  if h : supported.IV ivLen ∧ supported.A aLen ∧ supported.P cLen ∧ tLen = t then
    let P := GCTR CIPH (inc 32 (preCounterBlock CIPH IV)) C
    if T.cast h.2.2.2 = authenticationTag CIPH t IV A C then some P else none
  else
    none

end Standards.NIST.GCM
