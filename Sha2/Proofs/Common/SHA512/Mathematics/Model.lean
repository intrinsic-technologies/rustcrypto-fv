import Sha2.Proofs.NIST.SHA512

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512

open Sha2.Proofs.NIST

def smallSigma0 (x : UInt64) : UInt64 :=
  SHA512.rotateRight x 1 ^^^ SHA512.rotateRight x 8 ^^^ (x >>> 7)

def smallSigma1 (x : UInt64) : UInt64 :=
  SHA512.rotateRight x 19 ^^^ SHA512.rotateRight x 61 ^^^ (x >>> 6)

def bigSigma0 (x : UInt64) : UInt64 :=
  SHA512.rotateRight x 28 ^^^ SHA512.rotateRight x 34 ^^^ SHA512.rotateRight x 39

def bigSigma1 (x : UInt64) : UInt64 :=
  SHA512.rotateRight x 14 ^^^ SHA512.rotateRight x 18 ^^^ SHA512.rotateRight x 41

def choice (x y z : UInt64) : UInt64 := (x &&& y) ^^^ (~~~x &&& z)

def majority (x y z : UInt64) : UInt64 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

structure State where
  a : UInt64
  b : UInt64
  c : UInt64
  d : UInt64
  e : UInt64
  f : UInt64
  g : UInt64
  h : UInt64
  deriving DecidableEq

def State.ofArray (hash : Array UInt64) : State :=
  ⟨hash[0]!, hash[1]!, hash[2]!, hash[3]!, hash[4]!, hash[5]!, hash[6]!, hash[7]!⟩

def State.toArray (s : State) : Array UInt64 := #[s.a, s.b, s.c, s.d, s.e, s.f, s.g, s.h]

def State.addHash (hash : Array UInt64) (s : State) : Array UInt64 :=
  #[hash[0]! + s.a, hash[1]! + s.b, hash[2]! + s.c, hash[3]! + s.d,
    hash[4]! + s.e, hash[5]! + s.f, hash[6]! + s.g, hash[7]! + s.h]

def initialSchedule (block : Array Bool) : Array UInt64 :=
  (Array.range 16).map fun i =>
    UInt64.ofNat (Encoding.bitsToNat (block.extract (64 * i) (64 * (i + 1))))

def scheduleStep (words : Array UInt64) (i : Nat) : Array UInt64 :=
  words.push (words[i - 16]! + smallSigma0 words[i - 15]! +
    words[i - 7]! + smallSigma1 words[i - 2]!)

def schedulePrefix (block : Array Bool) (n : Nat) : Array UInt64 :=
  (List.range' 16 n).foldl scheduleStep (initialSchedule block)

def schedule (block : Array Bool) : Array UInt64 := schedulePrefix block 64

def round (s : State) (k w : UInt64) : State :=
  let first := s.h + bigSigma1 s.e + choice s.e s.f s.g + k + w
  let second := bigSigma0 s.a + majority s.a s.b s.c
  ⟨first + second, s.a, s.b, s.c, s.d + first, s.e, s.f, s.g⟩

def rounds (initial : State) (words : Array UInt64) (n : Nat) : State :=
  (List.range n).foldl (fun s i => round s SHA512.roundConstants[i]! words[i]!) initial

def compressModel (hash : Array UInt64) (block : Array Bool) : Array UInt64 :=
  State.addHash hash (rounds (State.ofArray hash) (schedule block) 80)

theorem schedulePrefix_zero (block : Array Bool) :
    schedulePrefix block 0 = initialSchedule block := rfl

theorem schedulePrefix_succ (block : Array Bool) (n : Nat) :
    schedulePrefix block (n + 1) = scheduleStep (schedulePrefix block n) (16 + n) := by
  simp only [schedulePrefix, List.range'_1_concat, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

theorem rounds_zero (initial : State) (words : Array UInt64) :
    rounds initial words 0 = initial := rfl

theorem rounds_succ (initial : State) (words : Array UInt64) (n : Nat) :
    rounds initial words (n + 1) =
      round (rounds initial words n) SHA512.roundConstants[n]! words[n]! := by
  simp only [rounds, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

end Sha2.Proofs.Common.SHA512
