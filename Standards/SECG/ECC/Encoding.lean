/-!
# Integer encodings

Big-endian octet-string conversions of integers (SEC 1 v2.0, §§2.3.7–2.3.8).

Source: https://www.secg.org/sec1-v2.pdf
-/

set_option autoImplicit false

namespace Standards.SECG.ECC.Encoding

/-- Unsigned big-endian integer represented by an octet string (SEC 1 v2.0, §2.3.8) -/
def octetsToNat (input : ByteArray) : Nat :=
  input.data.foldl (fun value byte => 256 * value + byte.toNat) 0

/--
Encode `value` in `length` big-endian octets, truncating high bits. SEC 1 v2.0, §2.3.7 requires
`value < 256^length`.
-/
def natToOctets (length value : Nat) : ByteArray :=
  ⟨(Array.range length).map fun i => UInt8.ofNat (value / 256 ^ (length - 1 - i) % 256)⟩

end Standards.SECG.ECC.Encoding
