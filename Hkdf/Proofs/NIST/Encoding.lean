set_option autoImplicit false

namespace Hkdf.Proofs.NIST.Encoding

def octetsToNat (input : ByteArray) : Nat :=
  input.data.foldl (fun value byte => 256 * value + byte.toNat) 0

def natToOctets (length value : Nat) : ByteArray :=
  ⟨(Array.range length).map fun i => UInt8.ofNat (value / 256 ^ (length - 1 - i) % 256)⟩

def octetsToBits (input : ByteArray) : Array Bool :=
  (Array.range (8 * input.size)).map fun i => input.data[i / 8]!.toNat.testBit (7 - i % 8)

def bitsToNat (input : Array Bool) : Nat :=
  input.foldl (fun value bit => 2 * value + if bit then 1 else 0) 0

end Hkdf.Proofs.NIST.Encoding
