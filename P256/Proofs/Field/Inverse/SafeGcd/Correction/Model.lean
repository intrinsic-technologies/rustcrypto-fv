import P256.Proofs.Field.Inverse.Interface
import P256.Proofs.Field.Representation
import X86Proofs.Instructions.Add.Operation

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse.SafeGcd.Correction

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At Limbs)

structure Pre [Bindings] (s : RamState) (boundary : ReturnBoundary) : Prop extends
    CalleePre s boundary 0x1126c0 33 32 56 where
  modulusRegion : P256.Proofs.Field.Inverse.ParameterPre s .rcx 32 56

structure Inputs where
  magnitude : Vector (BitVec 64) 4
  modulus : Vector (BitVec 64) 4
  sign : BitVec 8
  negate : BitVec 64

def v1181c2 (p : Inputs) := (p.modulus[0] : BitVec 64) - (p.magnitude[0])

def v1181c5 (p : Inputs) := ~~~(p.modulus[0] : BitVec 64)

def v1181cb (p : Inputs) := (p.magnitude[0] : BitVec 64) &&& (v1181c5 p)

def v1181ce (p : Inputs) := (v1181c5 p : BitVec 64) ||| (p.magnitude[0])

def v1181d1 (p : Inputs) := (v1181ce p : BitVec 64) &&& (v1181c2 p)

def v1181d4 (p : Inputs) := (v1181d1 p : BitVec 64) ||| (v1181cb p)

def v1181d7 (p : Inputs) := (v1181d4 p : BitVec 64) >>> 63

def v1181db (p : Inputs) := ((p.negate).setWidth 8 : BitVec 8) ^^^ (p.sign)

def v1181ed (p : Inputs) := (((0 : BitVec 32) : BitVec 32).setWidth 64 : BitVec 64) - (v1181d7 p)

def v1181f9 (p : Inputs) := (p.modulus[1] : BitVec 64) - (p.magnitude[1])

def v1181fc (p : Inputs) := (v1181ed p : BitVec 64).sshiftRight 63

def v118200 (p : Inputs) := addSpec (v1181fc p : BitVec 64) (v1181f9 p)

def v118203 (p : Inputs) := ~~~(p.modulus[1] : BitVec 64)

def v118209 (p : Inputs) := (p.magnitude[1] : BitVec 64) &&& (v118203 p)

def v11820c (p : Inputs) := (v118203 p : BitVec 64) ||| (p.magnitude[1])

def v11820f (p : Inputs) := (v11820c p : BitVec 64) &&& ((v118200 p).1)

def v118212 (p : Inputs) := (v11820f p : BitVec 64) ||| (v118209 p)

def v118215 (p : Inputs) := (v118212 p : BitVec 64) >>> 63

def v118220 (p : Inputs) := (((0 : BitVec 32) : BitVec 32).setWidth 64 : BitVec 64) - (v118215 p)

def v11822c (p : Inputs) := (p.modulus[2] : BitVec 64) - (p.magnitude[2])

def v11822f (p : Inputs) := (v118220 p : BitVec 64).sshiftRight 63

def v118233 (p : Inputs) := addSpec (v11822f p : BitVec 64) (v11822c p)

def v118236 (p : Inputs) := ~~~(p.modulus[2] : BitVec 64)

def v11823c (p : Inputs) := (p.magnitude[2] : BitVec 64) &&& (v118236 p)

def v11823f (p : Inputs) := (v118236 p : BitVec 64) ||| (p.magnitude[2])

def v118242 (p : Inputs) := (v11823f p : BitVec 64) &&& ((v118233 p).1)

def v118245 (p : Inputs) := (v118242 p : BitVec 64) ||| (v11823c p)

def v118248 (p : Inputs) := (v118245 p : BitVec 64) >>> 63

def v118259 (p : Inputs) := (((0 : BitVec 32) : BitVec 32).setWidth 64 : BitVec 64) - (v118248 p)

def v118263 (p : Inputs) := (p.modulus[3] : BitVec 64) - (p.magnitude[3])

def v118266 (p : Inputs) := (v118259 p : BitVec 64).sshiftRight 63

def v11826a (p : Inputs) := addSpec (v118266 p : BitVec 64) (v118263 p)

def v11826d (p : Inputs) := ~~~(p.modulus[3] : BitVec 64)

def v118273 (p : Inputs) := (p.magnitude[3] : BitVec 64) &&& (v11826d p)

def v118276 (p : Inputs) := (v11826d p : BitVec 64) ||| (p.magnitude[3])

def v118279 (p : Inputs) := (v118276 p : BitVec 64) &&& ((v11826a p).1)

def v11827c (p : Inputs) := (v118279 p : BitVec 64) ||| (v118273 p)

def v11827f (p : Inputs) := (v11827c p : BitVec 64) >>> 63

def v11828b (p : Inputs) := (p.magnitude[1] : BitVec 64) ||| (p.magnitude[0])

def v11828e (p : Inputs) := (v11828b p : BitVec 64) ||| (p.magnitude[2])

def v118291 (p : Inputs) := ((mergeGPR 8 (v1181db p) (p.negate)).setWidth 8 : BitVec 8) &&& (1)

def v118294 (p : Inputs) := (v11828e p : BitVec 64) ||| (p.magnitude[3])

def v1182ac (p : Inputs) := (v1181c2 p : BitVec 64) ^^^ (p.magnitude[0])

def v1182af (p : Inputs) := -((((((if decide (v118294 p = 0) then ((((0 : BitVec 32) : BitVec 32).setWidth 64).setWidth 32) else (((((mergeGPR 8 (v118291 p) (mergeGPR 8 (v1181db p) (p.negate))).setWidth 8).setWidth 32 : BitVec 32).setWidth 64).setWidth 32)) : BitVec 32).setWidth 64).setWidth 8).setWidth 32 : BitVec 32).setWidth 64 : BitVec 64)

def v1182b2 (p : Inputs) := (v1182af p : BitVec 64) &&& (v1182ac p)

def v1182b5 (p : Inputs) := (v1182b2 p : BitVec 64) ^^^ (p.magnitude[0])

def v1182c2 (p : Inputs) := ((v118200 p).1 : BitVec 64) ^^^ (p.magnitude[1])

def v1182c5 (p : Inputs) := -((((((if decide (v118294 p = 0) then ((((0 : BitVec 32) : BitVec 32).setWidth 64).setWidth 32) else (((((mergeGPR 8 (v118291 p) (mergeGPR 8 (v1181db p) (p.negate))).setWidth 8).setWidth 32 : BitVec 32).setWidth 64).setWidth 32)) : BitVec 32).setWidth 64).setWidth 8).setWidth 32 : BitVec 32).setWidth 64 : BitVec 64)

def v1182c8 (p : Inputs) := (v1182c5 p : BitVec 64) &&& (v1182c2 p)

def v1182cb (p : Inputs) := (v1182c8 p : BitVec 64) ^^^ (p.magnitude[1])

def v1182d7 (p : Inputs) := ((v118233 p).1 : BitVec 64) ^^^ (p.magnitude[2])

def v1182da (p : Inputs) := -((((((if decide (v118294 p = 0) then ((((0 : BitVec 32) : BitVec 32).setWidth 64).setWidth 32) else (((((mergeGPR 8 (v118291 p) (mergeGPR 8 (v1181db p) (p.negate))).setWidth 8).setWidth 32 : BitVec 32).setWidth 64).setWidth 32)) : BitVec 32).setWidth 64).setWidth 8).setWidth 32 : BitVec 32).setWidth 64 : BitVec 64)

def v1182dd (p : Inputs) := (v1182da p : BitVec 64) &&& (v1182d7 p)

def v1182e0 (p : Inputs) := (v1182dd p : BitVec 64) ^^^ (p.magnitude[2])

def v1182ec (p : Inputs) := ((v11826a p).1 : BitVec 64) ^^^ (p.magnitude[3])

def v1182ef (p : Inputs) := -((((((if decide (v118294 p = 0) then ((((0 : BitVec 32) : BitVec 32).setWidth 64).setWidth 32) else (((((mergeGPR 8 (v118291 p) (mergeGPR 8 (v1181db p) (p.negate))).setWidth 8).setWidth 32 : BitVec 32).setWidth 64).setWidth 32)) : BitVec 32).setWidth 64).setWidth 8).setWidth 32 : BitVec 32).setWidth 64 : BitVec 64)

def v1182f2 (p : Inputs) := (v1182ef p : BitVec 64) &&& (v1182ec p)

def v1182f5 (p : Inputs) := (v1182f2 p : BitVec 64) ^^^ (p.magnitude[3])

def correctedWords (p : Inputs) : Vector (BitVec 64) 4 :=
  #v[v1182b5 p, v1182cb p, v1182e0 p, v1182f5 p]

def limbs (words : Vector (BitVec 64) 4) : Limbs :=
  ⟨words[0], words[1], words[2], words[3]⟩

def inputs (s : RamState) : Inputs :=
  ⟨#v[memLoad s.external (s.regValue .rsi) 64,
      memLoad s.external (s.regValue .rsi + 8) 64,
      memLoad s.external (s.regValue .rsi + 16) 64,
      memLoad s.external (s.regValue .rsi + 24) 64],
    #v[memLoad s.external (s.regValue .rcx) 64,
      memLoad s.external (s.regValue .rcx + 8) 64,
      memLoad s.external (s.regValue .rcx + 16) 64,
      memLoad s.external (s.regValue .rcx + 24) 64],
    memLoad s.external (s.regValue .rsi + 32) 8, s.regValue .rdx⟩

end P256.Proofs.Field.Inverse.SafeGcd.Correction
