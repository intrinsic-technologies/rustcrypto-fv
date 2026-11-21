import Standards.NIST.GCM.Increment

/-!
# SP 800-38D §6.5: the GCTR function

The GCTR function of NIST SP 800-38D, §6.5, Algorithm 3: counter mode with the 32-bit
incrementing function, for any block cipher with a 128-bit block size, given as its forward
cipher function under the key.

Source: https://nvlpubs.nist.gov/nistpubs/Legacy/SP/nistspecialpublication800-38d.pdf
-/

namespace Standards.NIST.GCM

/--
`GCTR_K(ICB, X)` (SP 800-38D, §6.5, Algorithm 3)

Prerequisites: the forward cipher function `CIPH` of a block cipher with a 128-bit block size,
under the key K
Input: initial counter block `ICB`; bit string `X`, of arbitrary length
Output: bit string `Y` of bit length `len(X)`

1. If `X` is the empty string, then return the empty string as `Y`.
2. Let `n = ⌈len(X)/128⌉`.
3. Let `X_1, X_2, ..., X_{n-1}, X_n*` be the unique sequence of bit strings such that
   `X = X_1 || X_2 || ... || X_{n-1} || X_n*`, with `X_1, ..., X_{n-1}` complete blocks.
4. Let `CB_1 = ICB`.
5. For `i = 2` to `n`, let `CB_i = inc_32(CB_{i-1})`.
6. For `i = 1` to `n − 1`, let `Y_i = X_i ⊕ CIPH_K(CB_i)`.
7. Let `Y_n* = X_n* ⊕ MSB_{len(X_n*)}(CIPH_K(CB_n))`.
8. Let `Y = Y_1 || Y_2 || ... || Y_{n-1} || Y_n*`.
9. Return `Y`.

`CB` lists `CB_1, ..., CB_n`, `CB_{i+1}` being `inc_32` applied `i` times to `ICB`, and `E` lists
`CIPH_K(CB_1), ..., CIPH_K(CB_n)`. The result is steps 3 and 6 to 8 taken bit by bit: bit `j` of
`Y` is bit `j` of `X` exclusive-ORed with bit `j mod 128` of `CIPH_K(CB_i)` for the block
`i = ⌊j/128⌋ + 1` that holds bit `j`; for the empty string it is the empty string (step 1).
-/
def GCTR (CIPH : Vector Bool 128 → Vector Bool 128) (ICB : Vector Bool 128)
    (X : Vector Bool m) : Vector Bool m :=
  let n := (m + 127) / 128
  let CB := (List.range n).map fun i => Nat.repeat (inc 32) i ICB
  let E := CB.map CIPH
  Vector.ofFn fun j =>
    let block := E[j.val / 128]'(by simp only [E, CB, List.length_map, List.length_range]; omega)
    X[j] ^^ block[j.val % 128]'(by omega)

end Standards.NIST.GCM
