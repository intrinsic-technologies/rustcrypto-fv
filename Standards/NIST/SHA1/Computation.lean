import Standards.NIST.SHA1.Functions

/-!
# SHA-1 hash computation

The initial hash value of FIPS 180-4, §5.3.1, and from §6.1.2 the message schedule, the working
variables and their step, the compression function and the processing of message blocks into the
final hash value.

Source: https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf
-/

namespace Standards.NIST.SHA1

/-- The SHA-1 initial hash value (FIPS 180-4, §5.3.1) -/
def initialHashValue : Vector (BitVec 32) 5 :=
  #v[0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0]

/-- The message schedule of one message block (FIPS 180-4, §6.1.2, step 1) -/
def messageSchedule (M : Vector (BitVec 32) 16) : Vector (BitVec 32) 80 := Id.run do
  let mut W : Vector (BitVec 32) 80 := Vector.replicate 80 0
  for t in List.finRange 80 do
    if h : t.val < 16 then
      W := W.set t.val M[t.val]
    else
      W := W.set t.val (ROTL 1 (W[t.val - 3] ^^^ W[t.val - 8] ^^^ W[t.val - 14] ^^^ W[t.val - 16]))
  return W

/-- The working variables of the SHA-1 hash computation (FIPS 180-4, §6.1) -/
structure WorkingVariables where
  a : BitVec 32
  b : BitVec 32
  c : BitVec 32
  d : BitVec 32
  e : BitVec 32
  deriving DecidableEq, Repr

/-- Initializes the working variables with a hash value (FIPS 180-4, §6.1.2, step 2) -/
def WorkingVariables.ofHashValue (H : Vector (BitVec 32) 5) : WorkingVariables :=
  { a := H[0], b := H[1], c := H[2], d := H[3], e := H[4] }

/-- Applies step `t` with the message schedule word `Wt` (FIPS 180-4, §6.1.2, step 3) -/
def step (t : Fin 80) (Wt : BitVec 32) (v : WorkingVariables) : WorkingVariables :=
  let T := ROTL 5 v.a + f t v.b v.c v.d + v.e + K t + Wt
  { a := T, b := v.a, c := ROTL 30 v.b, d := v.c, e := v.d }

/-- Applies the listed steps in order, each with its word of the message schedule `W` -/
def applySteps (W : Vector (BitVec 32) 80) (steps : List (Fin 80)) (v : WorkingVariables) :
    WorkingVariables :=
  steps.foldl (fun v t => step t W[t] v) v

/-- Adds the working variables to the previous hash value (FIPS 180-4, §6.1.2, step 4) -/
def intermediateHashValue (H : Vector (BitVec 32) 5) (v : WorkingVariables) :
    Vector (BitVec 32) 5 :=
  #v[v.a + H[0], v.b + H[1], v.c + H[2], v.d + H[3], v.e + H[4]]

/--
The SHA-1 compression function: the next hash value from the previous one and a message block
(FIPS 180-4, §6.1.2, steps 1–4)
-/
def compress (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16) : Vector (BitVec 32) 5 :=
  let W := messageSchedule M
  intermediateHashValue H (applySteps W (List.finRange 80) (.ofHashValue H))

/--
The final hash value after processing the blocks in order from the initial hash value
(FIPS 180-4, §6.1.2)
-/
def hashComputation (blocks : Array (Vector (BitVec 32) 16)) : Vector (BitVec 32) 5 :=
  blocks.foldl compress initialHashValue

end Standards.NIST.SHA1
