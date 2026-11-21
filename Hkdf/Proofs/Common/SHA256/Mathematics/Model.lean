import Hkdf.Proofs.NIST.SHA256

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256

open Hkdf.Proofs.NIST

def smallSigma0 (x : UInt32) : UInt32 :=
  SHA256.rotateRight x 7 ^^^ SHA256.rotateRight x 18 ^^^ (x >>> 3)

def smallSigma1 (x : UInt32) : UInt32 :=
  SHA256.rotateRight x 17 ^^^ SHA256.rotateRight x 19 ^^^ (x >>> 10)

def bigSigma0 (x : UInt32) : UInt32 :=
  SHA256.rotateRight x 2 ^^^ SHA256.rotateRight x 13 ^^^ SHA256.rotateRight x 22

def bigSigma1 (x : UInt32) : UInt32 :=
  SHA256.rotateRight x 6 ^^^ SHA256.rotateRight x 11 ^^^ SHA256.rotateRight x 25

def choice (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (~~~x &&& z)

def majority (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

structure State where
  a : UInt32
  b : UInt32
  c : UInt32
  d : UInt32
  e : UInt32
  f : UInt32
  g : UInt32
  h : UInt32
  deriving DecidableEq

def State.ofArray (hash : Array UInt32) : State :=
  ⟨hash[0]!, hash[1]!, hash[2]!, hash[3]!, hash[4]!, hash[5]!, hash[6]!, hash[7]!⟩

def State.toArray (s : State) : Array UInt32 := #[s.a, s.b, s.c, s.d, s.e, s.f, s.g, s.h]

def State.addHash (hash : Array UInt32) (s : State) : Array UInt32 :=
  #[hash[0]! + s.a, hash[1]! + s.b, hash[2]! + s.c, hash[3]! + s.d,
    hash[4]! + s.e, hash[5]! + s.f, hash[6]! + s.g, hash[7]! + s.h]

def initialSchedule (block : Array Bool) : Array UInt32 :=
  (Array.range 16).map fun i =>
    UInt32.ofNat (Encoding.bitsToNat (block.extract (32 * i) (32 * (i + 1))))

def scheduleStep (words : Array UInt32) (i : Nat) : Array UInt32 :=
  words.push (words[i - 16]! + smallSigma0 words[i - 15]! +
    words[i - 7]! + smallSigma1 words[i - 2]!)

def schedulePrefix (block : Array Bool) (n : Nat) : Array UInt32 :=
  (List.range' 16 n).foldl scheduleStep (initialSchedule block)

def schedule (block : Array Bool) : Array UInt32 := schedulePrefix block 48

def round (s : State) (k w : UInt32) : State :=
  let first := s.h + bigSigma1 s.e + choice s.e s.f s.g + k + w
  let second := bigSigma0 s.a + majority s.a s.b s.c
  ⟨first + second, s.a, s.b, s.c, s.d + first, s.e, s.f, s.g⟩

def rounds (initial : State) (words : Array UInt32) (n : Nat) : State :=
  (List.range n).foldl (fun s i => round s SHA256.roundConstants[i]! words[i]!) initial

def compressModel (hash : Array UInt32) (block : Array Bool) : Array UInt32 :=
  State.addHash hash (rounds (State.ofArray hash) (schedule block) 64)

theorem schedulePrefix_zero (block : Array Bool) :
    schedulePrefix block 0 = initialSchedule block := rfl

theorem schedulePrefix_succ (block : Array Bool) (n : Nat) :
    schedulePrefix block (n + 1) = scheduleStep (schedulePrefix block n) (16 + n) := by
  simp only [schedulePrefix, List.range'_1_concat, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

theorem rounds_zero (initial : State) (words : Array UInt32) :
    rounds initial words 0 = initial := rfl

theorem rounds_succ (initial : State) (words : Array UInt32) (n : Nat) :
    rounds initial words (n + 1) =
      round (rounds initial words n) SHA256.roundConstants[n]! words[n]! := by
  simp only [rounds, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

end Hkdf.Proofs.Common.SHA256
