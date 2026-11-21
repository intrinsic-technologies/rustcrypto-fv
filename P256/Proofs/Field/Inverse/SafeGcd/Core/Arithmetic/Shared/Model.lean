import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.Shared.Batch.Model
import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.LinearShift.Model
import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.ModularShift.Model
import P256.Proofs.Field.Inverse.SafeGcd.Correction.Model

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Shared

structure SignedWords where
  words : Vector (BitVec 64) 4
  sign : BitVec 8

structure Inputs where
  a : Vector (BitVec 64) 4
  modulus : Vector (BitVec 64) 4
  scale : Vector (BitVec 64) 4
  inverse : BitVec 64

structure LoopState where
  f : SignedWords
  g : SignedWords
  d : SignedWords
  e : SignedWords
  delta : BitVec 64
  remaining : Nat

def initialState (p : Inputs) : LoopState where
  f := ⟨p.modulus, 0⟩
  g := ⟨p.a, 0⟩
  d := ⟨#v[0, 0, 0, 0], 0⟩
  e := ⟨p.scale, 0⟩
  delta := 1
  remaining := 591

def zeroWords (a : Vector (BitVec 64) 4) : Bool :=
  (a[0] ||| a[1] ||| a[2] ||| a[3]) == 0

def lowWord (p : SignedWords) : BitVec 64 :=
  let w := p.words[0] &&& 0x7fffffffffffffff
  ((-p.sign.setWidth 64) &&& ((-w) ^^^ w)) ^^^ w

def batchInput (s : LoopState) : Batch.Words where
  delta := s.delta
  f := lowWord s.f
  g := lowWord s.g
  u := 1
  v := 0
  q := 0
  r := 1

def batchCount (s : LoopState) : Nat := min s.remaining 62

def batchResult (s : LoopState) : Batch.Words := Batch.run (batchCount s) (batchInput s)

def linearInput (a b : SignedWords) (u v : BitVec 64) : LinearCombination.Inputs :=
  ⟨a.words, b.words, a.sign, b.sign, u, v⟩

def fInput (s : LoopState) : LinearShift.Inputs :=
  ⟨linearInput s.f s.g (batchResult s).u (batchResult s).v,
    BitVec.ofNat 32 (batchCount s)⟩

def gInput (s : LoopState) : LinearShift.Inputs :=
  ⟨linearInput s.f s.g (batchResult s).q (batchResult s).r,
    BitVec.ofNat 32 (batchCount s)⟩

def dInput (p : Inputs) (s : LoopState) : ModularShift.Inputs :=
  ⟨linearInput s.d s.e (batchResult s).u (batchResult s).v,
    BitVec.ofNat 32 (batchCount s), p.modulus, p.inverse, 0⟩

def eInput (p : Inputs) (s : LoopState) : ModularShift.Inputs :=
  ⟨linearInput s.d s.e (batchResult s).q (batchResult s).r,
    BitVec.ofNat 32 (batchCount s), p.modulus, p.inverse, 0⟩

def nextState (p : Inputs) (s : LoopState) : LoopState where
  f := ⟨LinearShift.shiftedWords (fInput s), LinearShift.resultSign (fInput s)⟩
  g := ⟨LinearShift.shiftedWords (gInput s), LinearShift.resultSign (gInput s)⟩
  d := ⟨ModularShift.resultWords (dInput p s), ModularShift.resultSign (dInput p s)⟩
  e := ⟨ModularShift.resultWords (eInput p s), ModularShift.resultSign (eInput p s)⟩
  delta := (batchResult s).delta
  remaining := s.remaining - batchCount s

def correctionInput (p : Inputs) (s : LoopState) : Correction.Inputs :=
  ⟨s.d.words, p.modulus, s.d.sign, s.f.sign.setWidth 64⟩

end P256.Proofs.Field.Inverse.SafeGcd.Core.Shared
