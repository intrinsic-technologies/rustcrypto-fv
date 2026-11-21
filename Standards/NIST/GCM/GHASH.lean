import Standards.NIST.GCM.Multiplication

/-!
# SP 800-38D §6.4: GHASH

The GHASH function under the hash subkey `H`, Algorithm 2 of NIST SP 800-38D, §6.4.

Source: https://nvlpubs.nist.gov/nistpubs/Legacy/SP/nistspecialpublication800-38d.pdf
-/

namespace Standards.NIST.GCM

/--
`GHASH_H(X)` (SP 800-38D, §6.4, Algorithm 2)

Prerequisites: block `H`, the hash subkey
Input: the blocks `X_1, ..., X_m` of a bit string `X` with `len(X) = 128m`
Output: block `GHASH_H(X)`

1. Let `X_1, X_2, ..., X_m` denote the unique sequence of blocks such that
   `X = X_1 || X_2 || ... || X_m`.
2. Let `Y_0` be the "zero block," `0^128`.
3. For `i = 1, ..., m`, let `Y_i = (Y_{i-1} ⊕ X_i) • H`.
4. Return `Y_m`.

The input is the sequence of step 1, which a string of length `128m` determines uniquely. The
document requires `m` to be positive; for `m = 0` the steps return `Y_0 = 0^128`.
-/
def GHASH (H : Vector Bool 128) (X : Array (Vector Bool 128)) : Vector Bool 128 := Id.run do
  let mut Y := zeros 128
  for Xi in X do
    Y := mul (xor Y Xi) H
  return Y

end Standards.NIST.GCM
