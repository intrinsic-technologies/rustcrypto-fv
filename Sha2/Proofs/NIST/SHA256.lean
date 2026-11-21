import Sha2.Proofs.NIST.Encoding

set_option autoImplicit false

namespace Sha2.Proofs.NIST.SHA256

def rotateRight (word : UInt32) (count : Nat) : UInt32 :=
  (word >>> UInt32.ofNat (count % 32)) ||| (word <<< UInt32.ofNat ((32 - count % 32) % 32))

def initialHash : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

def initialHash224 : Array UInt32 := #[
  0xc1059ed8, 0x367cd507, 0x3070dd17, 0xf70e5939,
  0xffc00b31, 0x68581511, 0x64f98fa7, 0xbefa4fa4]

def roundConstants : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1,
  0x923f82a4, 0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
  0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786,
  0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147,
  0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
  0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
  0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a,
  0x5b9cca4f, 0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
  0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

def pad (input : Array Bool) : Array Bool :=
  let zeroCount := (448 + 512 - (input.size + 1) % 512) % 512
  input ++ #[true] ++ Array.replicate zeroCount false ++
    (Array.range 64).map (fun i => input.size.testBit (63 - i))

def compress (hash : Array UInt32) (block : Array Bool) : Array UInt32 := Id.run do
  let mut schedule : Array UInt32 := (Array.range 16).map fun i =>
    UInt32.ofNat (Encoding.bitsToNat (block.extract (32 * i) (32 * (i + 1))))
  for i in [16:64] do
    let x := schedule[i - 15]!
    let y := schedule[i - 2]!
    let σ₀ := rotateRight x 7 ^^^ rotateRight x 18 ^^^ (x >>> 3)
    let σ₁ := rotateRight y 17 ^^^ rotateRight y 19 ^^^ (y >>> 10)
    schedule := schedule.push (schedule[i - 16]! + σ₀ + schedule[i - 7]! + σ₁)
  let mut a := hash[0]!
  let mut b := hash[1]!
  let mut c := hash[2]!
  let mut d := hash[3]!
  let mut e := hash[4]!
  let mut f := hash[5]!
  let mut g := hash[6]!
  let mut h := hash[7]!
  for i in [:64] do
    let sum1 := rotateRight e 6 ^^^ rotateRight e 11 ^^^ rotateRight e 25
    let choice := (e &&& f) ^^^ (~~~e &&& g)
    let first := h + sum1 + choice + roundConstants[i]! + schedule[i]!
    let sum0 := rotateRight a 2 ^^^ rotateRight a 13 ^^^ rotateRight a 22
    let majority := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let second := sum0 + majority
    h := g
    g := f
    f := e
    e := d + first
    d := c
    c := b
    b := a
    a := first + second
  return #[hash[0]! + a, hash[1]! + b, hash[2]! + c, hash[3]! + d,
    hash[4]! + e, hash[5]! + f, hash[6]! + g, hash[7]! + h]

def sha256Bits (input : Array Bool) : ByteArray := Id.run do
  let padded := pad input
  let mut hash := initialHash
  for i in [:padded.size / 512] do
    hash := compress hash (padded.extract (512 * i) (512 * (i + 1)))
  return hash.foldl (fun output word => output ++ Encoding.natToOctets 4 word.toNat) ByteArray.empty

def sha256 (input : ByteArray) : ByteArray := sha256Bits (Encoding.octetsToBits input)

def truncatedBits (initial : Array UInt32) (bytes : Nat) (input : Array Bool) : ByteArray :=
  let padded := pad input
  let hash := (List.range (padded.size / 512)).foldl
    (fun hash i => compress hash (padded.extract (512 * i) (512 * (i + 1)))) initial
  (hash.foldl (fun output word => output ++ Encoding.natToOctets 4 word.toNat)
    ByteArray.empty).extract 0 bytes

def sha224 (input : ByteArray) : ByteArray :=
  truncatedBits initialHash224 28 (Encoding.octetsToBits input)

end Sha2.Proofs.NIST.SHA256
