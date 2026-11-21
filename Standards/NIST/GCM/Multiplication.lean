import Standards.NIST.GCM.Strings

/-!
# SP 800-38D §6.3: multiplication of blocks

The product `X • Y` of two 128-bit blocks, Algorithm 1 of NIST SP 800-38D, §6.3: multiplication
in the field of 2^128 elements, a block `x_0 x_1 ... x_127` being the polynomial
`x_0 + x_1 u + ... + x_127 u^127`, reduced modulo the polynomial of `R || 1`.

Source: https://nvlpubs.nist.gov/nistpubs/Legacy/SP/nistspecialpublication800-38d.pdf
-/

namespace Standards.NIST.GCM

/-- `R = 11100001 || 0^120` (SP 800-38D, §6.3) -/
def R : Vector Bool 128 := #v[true, true, true, false, false, false, false, true] ++ zeros 120

/--
`X • Y` (SP 800-38D, §6.3, Algorithm 1)

Input: blocks `X`, `Y`
Output: block `X • Y`

1. Let `x_0 x_1 ... x_127` denote the sequence of bits in `X`.
2. Let `Z_0 = 0^128` and `V_0 = Y`.
3. For `i = 0` to `127`, `Z_{i+1}` is `Z_i` if `x_i = 0` and `Z_i ⊕ V_i` if `x_i = 1`;
   `V_{i+1}` is `V_i >> 1` if `LSB_1(V_i) = 0` and `(V_i >> 1) ⊕ R` if `LSB_1(V_i) = 1`.
4. Return `Z_128`.
-/
def mul (X Y : Vector Bool 128) : Vector Bool 128 := Id.run do
  let mut Z := zeros 128
  let mut V := Y
  for i in List.finRange 128 do
    Z := if X[i] then xor Z V else Z
    V := if LSB 1 V = #v[false] then rightShift V else xor (rightShift V) R
  return Z

end Standards.NIST.GCM
