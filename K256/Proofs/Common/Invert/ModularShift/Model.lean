import K256.Proofs.Common.Invert.ModularShift.Limbs

namespace K256.Proofs.Common.Invert.ModularShift

open LinearCombination (Limbs subRaw subWord borrow subRaw_toNat subWord_borrow eq_zero_or_one)
open X86Proofs K256.Proofs.Generate.Generator.Affine.Invert
open SafeGcd (correctionWord correctionWord_value inverse_mod_two_pow)

structure Inputs where
  magnitude : Vector (BitVec 64) 5
  sign : BitVec 8
  shift : BitVec 32

def v1089a7 (p : Inputs) := (((64 : BitVec 32).setWidth 64).setWidth 32 : BitVec 32) - ((p.shift.setWidth 64).setWidth 32)

def v1089cc (p : Inputs) := (SafeGcd.inverseWord : BitVec 64) * (p.magnitude[0])

def v1089d0 (p : Inputs) := (v1089cc p : BitVec 64) <<< (64 - p.shift.toNat)

def v1089d3 (p : Inputs) := (v1089d0 p : BitVec 64) >>> (64 - p.shift.toNat)

def v1089ec (p : Inputs) := mulResult (modulusWords[0]) (v1089d3 p)

def v1089fd (p : Inputs) := mulResult (modulusWords[1]) (v1089d3 p)

def v108a0f (p : Inputs) := mulResult (modulusWords[2]) (v1089d3 p)

def v108a21 (p : Inputs) := mulResult (modulusWords[3]) (v1089d3 p)

def v108a24 (p : Inputs) := addSpec ((v1089fd p).1 : BitVec 64) ((v1089ec p).2)

def v108a2c (p : Inputs) := adcSpec ((v108a24 p).2.CF) ((v108a0f p).1 : BitVec 64) ((v1089fd p).2)

def v108a2f (p : Inputs) := adcSpec ((v108a2c p).2.CF) ((v108a21 p).1 : BitVec 64) ((v108a0f p).2)

def v108a32 (p : Inputs) := adcSpec ((v108a2f p).2.CF) ((v108a21 p).2 : BitVec 64) (0)

def v108a39 (p : Inputs) := (p.magnitude[0] : BitVec 64) - ((v1089ec p).1)

def v108a3c (p : Inputs) := ~~~(p.magnitude[0] : BitVec 64)

def v108a42 (p : Inputs) := ((v1089ec p).1 : BitVec 64) &&& (v108a3c p)

def v108a45 (p : Inputs) := (v108a3c p : BitVec 64) ||| ((v1089ec p).1)

def v108a4d (p : Inputs) := (v108a45 p : BitVec 64) &&& (v108a39 p)

def v108a50 (p : Inputs) := (v108a4d p : BitVec 64) ||| (v108a42 p)

def v108a5e (p : Inputs) := (v108a50 p : BitVec 64) >>> 63

def v108a6f (p : Inputs) := (((0 : BitVec 32) : BitVec 32).setWidth 64 : BitVec 64) - (v108a5e p)

def v108a77 (p : Inputs) := (p.magnitude[1] : BitVec 64) - ((v108a24 p).1)

def v108a7a (p : Inputs) := (v108a6f p : BitVec 64).sshiftRight 63

def v108a7e (p : Inputs) := addSpec (v108a7a p : BitVec 64) (v108a77 p)

def v108a81 (p : Inputs) := ~~~(p.magnitude[1] : BitVec 64)

def v108a87 (p : Inputs) := ((v108a24 p).1 : BitVec 64) &&& (v108a81 p)

def v108a8a (p : Inputs) := (v108a81 p : BitVec 64) ||| ((v108a24 p).1)

def v108a8d (p : Inputs) := (v108a8a p : BitVec 64) &&& ((v108a7e p).1)

def v108a90 (p : Inputs) := (v108a8d p : BitVec 64) ||| (v108a87 p)

def v108a93 (p : Inputs) := (v108a90 p : BitVec 64) >>> 63

def v108a9f (p : Inputs) := (((0 : BitVec 32) : BitVec 32).setWidth 64 : BitVec 64) - (v108a93 p)

def v108aa7 (p : Inputs) := (p.magnitude[2] : BitVec 64) - ((v108a2c p).1)

def v108aaa (p : Inputs) := (v108a9f p : BitVec 64).sshiftRight 63

def v108aae (p : Inputs) := addSpec (v108aaa p : BitVec 64) (v108aa7 p)

def v108ab1 (p : Inputs) := ~~~(p.magnitude[2] : BitVec 64)

def v108ab7 (p : Inputs) := ((v108a2c p).1 : BitVec 64) &&& (v108ab1 p)

def v108aba (p : Inputs) := (v108ab1 p : BitVec 64) ||| ((v108a2c p).1)

def v108abd (p : Inputs) := (v108aba p : BitVec 64) &&& ((v108aae p).1)

def v108ac0 (p : Inputs) := (v108abd p : BitVec 64) ||| (v108ab7 p)

def v108ac3 (p : Inputs) := (v108ac0 p : BitVec 64) >>> 63

def v108acf (p : Inputs) := (((0 : BitVec 32) : BitVec 32).setWidth 64 : BitVec 64) - (v108ac3 p)

def v108ad7 (p : Inputs) := (p.magnitude[3] : BitVec 64) - ((v108a2f p).1)

def v108ada (p : Inputs) := (v108acf p : BitVec 64).sshiftRight 63

def v108ade (p : Inputs) := addSpec (v108ada p : BitVec 64) (v108ad7 p)

def v108ae1 (p : Inputs) := ~~~(p.magnitude[3] : BitVec 64)

def v108ae7 (p : Inputs) := ((v108a2f p).1 : BitVec 64) &&& (v108ae1 p)

def v108aea (p : Inputs) := (v108ae1 p : BitVec 64) ||| ((v108a2f p).1)

def v108af0 (p : Inputs) := (v108aea p : BitVec 64) &&& ((v108ade p).1)

def v108af3 (p : Inputs) := (v108af0 p : BitVec 64) ||| (v108ae7 p)

def v108af6 (p : Inputs) := (v108af3 p : BitVec 64) >>> 63

def v108b01 (p : Inputs) := (((0 : BitVec 32) : BitVec 32).setWidth 64 : BitVec 64) - (v108af6 p)

def v108b09 (p : Inputs) := (p.magnitude[4] : BitVec 64) - ((v108a32 p).1)

def v108b0c (p : Inputs) := ~~~(p.magnitude[4] : BitVec 64)

def v108b12 (p : Inputs) := ((v108a32 p).1 : BitVec 64) &&& (v108b0c p)

def v108b15 (p : Inputs) := (v108b0c p : BitVec 64) ||| ((v108a32 p).1)

def v108b18 (p : Inputs) := (v108b01 p : BitVec 64).sshiftRight 63

def v108b1c (p : Inputs) := addSpec (v108b18 p : BitVec 64) (v108b09 p)

def v108b1f (p : Inputs) := (v108b15 p : BitVec 64) &&& ((v108b1c p).1)

def v108b22 (p : Inputs) := (v108b1f p : BitVec 64) ||| (v108b12 p)

def v108b25 (p : Inputs) := (v108b22 p : BitVec 64) >>> 63

def v108b3b (p : Inputs) := -(v108a39 p : BitVec 64)

def v108b44 (p : Inputs) := sbbSpec (decide ((v108a39 p : BitVec 64) ≠ 0)) ((0 : BitVec 32).setWidth 64 : BitVec 64) ((v108a7e p).1)

def v108b4c (p : Inputs) := sbbSpec ((v108b44 p).2.CF) ((0 : BitVec 32).setWidth 64 : BitVec 64) ((v108aae p).1)

def v108b4f (p : Inputs) := sbbSpec ((v108b4c p).2.CF) (((0 : BitVec 32) : BitVec 32).setWidth 64 : BitVec 64) ((v108ade p).1)

def v108bc1 (p : Inputs) := ((v108b4f p).1 : BitVec 64) ^^^ ((v108ade p).1)

def v108bc4 (p : Inputs) := -((((if !(decide ((v108b25 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)).setWidth 32 : BitVec 32).setWidth 64 : BitVec 64)

def v108bc7 (p : Inputs) := (v108bc4 p : BitVec 64) &&& (v108bc1 p)

def v108bca (p : Inputs) := (v108bc7 p : BitVec 64) ^^^ ((v108ade p).1)

def v108bcd (p : Inputs) := ((v108b4c p).1 : BitVec 64) ^^^ ((v108aae p).1)

def v108bd0 (p : Inputs) := -((((if !(decide ((v108b25 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)).setWidth 32 : BitVec 32).setWidth 64 : BitVec 64)

def v108bd3 (p : Inputs) := (v108bd0 p : BitVec 64) &&& (v108bcd p)

def v108bd6 (p : Inputs) := (v108bd3 p : BitVec 64) ^^^ ((v108aae p).1)

def v108bd9 (p : Inputs) := ((v108b44 p).1 : BitVec 64) ^^^ ((v108a7e p).1)

def v108bdc (p : Inputs) := -((((if !(decide ((v108b25 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)).setWidth 32 : BitVec 32).setWidth 64 : BitVec 64)

def v108bdf (p : Inputs) := (v108bdc p : BitVec 64) &&& (v108bd9 p)

def v108be2 (p : Inputs) := (v108bdf p : BitVec 64) ^^^ ((v108a7e p).1)

def v108be5 (p : Inputs) := (((((if !((v108b4f p).2.CF) then 1 else 0 : BitVec 8)).setWidth 32 : BitVec 32).setWidth 64).setWidth 32 : BitVec 32) &&& (1)

def v108beb (p : Inputs) := ~~~((v108b1c p).1 : BitVec 64)

def v108bee (p : Inputs) := addSpec (v108beb p : BitVec 64) ((v108be5 p : BitVec 32).setWidth 64)

def v108bf1 (p : Inputs) := ((v108bee p).1 : BitVec 64) ^^^ ((v108b1c p).1)

def v108bfa (p : Inputs) := -((((if !(decide ((v108b25 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)).setWidth 32 : BitVec 32).setWidth 64 : BitVec 64)

def v108bfd (p : Inputs) := (v108bfa p : BitVec 64) &&& (v108bf1 p)

def v108c00 (p : Inputs) := (v108bfd p : BitVec 64) ^^^ ((v108b1c p).1)

def v108c0a (p : Inputs) := (v108c00 p : BitVec 64) <<< (64 - p.shift.toNat)

def v108c12 (p : Inputs) := (v108b3b p : BitVec 64) ^^^ (v108a39 p)

def v108c15 (p : Inputs) := -((((if !(decide ((v108b25 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)).setWidth 32 : BitVec 32).setWidth 64 : BitVec 64)

def v108c21 (p : Inputs) := (v108bca p : BitVec 64) >>> p.shift.toNat

def v108c26 (p : Inputs) := (v108bca p : BitVec 64) <<< (64 - p.shift.toNat)

def v108c2e (p : Inputs) := (v108bd6 p : BitVec 64) >>> p.shift.toNat

def v108c31 (p : Inputs) := (v108c15 p : BitVec 64) &&& (v108c12 p)

def v108c34 (p : Inputs) := (v108c31 p : BitVec 64) ^^^ (v108a39 p)

def v108c37 (p : Inputs) := (v108c2e p : BitVec 64) ||| (v108c26 p)

def v108c3c (p : Inputs) := (v108bd6 p : BitVec 64) <<< (64 - p.shift.toNat)

def v108c44 (p : Inputs) := (v108be2 p : BitVec 64) >>> p.shift.toNat

def v108c49 (p : Inputs) := (v108be2 p : BitVec 64) <<< (64 - p.shift.toNat)

def v108c4e (p : Inputs) := (v108c34 p : BitVec 64) >>> p.shift.toNat

def v108c51 (p : Inputs) := (v108c44 p : BitVec 64) ||| (v108c3c p)

def v108c54 (p : Inputs) := (v108c4e p : BitVec 64) ||| (v108c49 p)

def v108c5f (p : Inputs) := (v108c54 p : BitVec 64) - (modulusWords[0])

def v108c65 (p : Inputs) := ~~~(v108c54 p : BitVec 64)

def v108c6b (p : Inputs) := (modulusWords[0] : BitVec 64) &&& (v108c65 p)

def v108c6e (p : Inputs) := (v108c65 p : BitVec 64) ||| (modulusWords[0])

def v108c71 (p : Inputs) := (v108c6e p : BitVec 64) &&& (v108c5f p)

def v108c74 (p : Inputs) := (v108c71 p : BitVec 64) ||| (v108c6b p)

def v108c77 (p : Inputs) := (v108c74 p : BitVec 64) >>> 63

def v108c88 (p : Inputs) := (((0 : BitVec 32) : BitVec 32).setWidth 64 : BitVec 64) - (v108c77 p)

def v108c95 (p : Inputs) := (v108c51 p : BitVec 64) - (modulusWords[1])

def v108c98 (p : Inputs) := (v108c88 p : BitVec 64).sshiftRight 63

def v108c9c (p : Inputs) := addSpec (v108c98 p : BitVec 64) (v108c95 p)

def v108ca2 (p : Inputs) := ~~~(v108c51 p : BitVec 64)

def v108ca8 (p : Inputs) := (modulusWords[1] : BitVec 64) &&& (v108ca2 p)

def v108cab (p : Inputs) := (v108ca2 p : BitVec 64) ||| (modulusWords[1])

def v108cae (p : Inputs) := (v108cab p : BitVec 64) &&& ((v108c9c p).1)

def v108cb1 (p : Inputs) := (v108cae p : BitVec 64) ||| (v108ca8 p)

def v108cb4 (p : Inputs) := (v108cb1 p : BitVec 64) >>> 63

def v108cbf (p : Inputs) := (((0 : BitVec 32) : BitVec 32).setWidth 64 : BitVec 64) - (v108cb4 p)

def v108ccc (p : Inputs) := (v108c37 p : BitVec 64) - (modulusWords[2])

def v108ccf (p : Inputs) := (v108cbf p : BitVec 64).sshiftRight 63

def v108cd3 (p : Inputs) := addSpec (v108ccf p : BitVec 64) (v108ccc p)

def v108cd9 (p : Inputs) := ~~~(v108c37 p : BitVec 64)

def v108cdf (p : Inputs) := (modulusWords[2] : BitVec 64) &&& (v108cd9 p)

def v108ce2 (p : Inputs) := (v108cd9 p : BitVec 64) ||| (modulusWords[2])

def v108ce5 (p : Inputs) := (v108ce2 p : BitVec 64) &&& ((v108cd3 p).1)

def v108ce8 (p : Inputs) := (v108ce5 p : BitVec 64) ||| (v108cdf p)

def v108ceb (p : Inputs) := (v108ce8 p : BitVec 64) >>> 63

def v108cf6 (p : Inputs) := (((0 : BitVec 32) : BitVec 32).setWidth 64 : BitVec 64) - (v108ceb p)

def v108cfb (p : Inputs) := (v108c21 p : BitVec 64) ||| (v108c0a p)

def v108d06 (p : Inputs) := (v108cfb p : BitVec 64) - (modulusWords[3])

def v108d09 (p : Inputs) := (v108cf6 p : BitVec 64).sshiftRight 63

def v108d0d (p : Inputs) := addSpec (v108d09 p : BitVec 64) (v108d06 p)

def v108d13 (p : Inputs) := ~~~(v108cfb p : BitVec 64)

def v108d19 (p : Inputs) := (modulusWords[3] : BitVec 64) &&& (v108d13 p)

def v108d1c (p : Inputs) := (v108d13 p : BitVec 64) ||| (modulusWords[3])

def v108d1f (p : Inputs) := (v108d1c p : BitVec 64) &&& ((v108d0d p).1)

def v108d22 (p : Inputs) := (v108d1f p : BitVec 64) ||| (v108d19 p)

def v108d25 (p : Inputs) := (v108d22 p : BitVec 64) >>> 63

def v108d33 (p : Inputs) := (v108c00 p : BitVec 64) >>> p.shift.toNat

def v108d36 (p : Inputs) := (((0 : BitVec 32) : BitVec 32).setWidth 64 : BitVec 64) - (v108d25 p)

def v108d40 (p : Inputs) := ((((((p.sign.setWidth 32 : BitVec 32).setWidth 64).setWidth 8).setWidth 32 : BitVec 32).setWidth 64).setWidth 8 : BitVec 8) ^^^ ((mergeGPR 8 ((if !(decide ((v108b25 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)) ((0 : BitVec 64))).setWidth 8)

def v108d4b (p : Inputs) := ((mergeGPR 8 ((if decide ((v108d33 p : BitVec 64) = 0) then 1 else 0 : BitVec 8)) (((((p.shift.setWidth 64).setWidth 32 : BitVec 32).setWidth 64).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8 : BitVec 8) &&& ((v108d36 p).setWidth 8)

def v108d5d (p : Inputs) := ((((mergeGPR 8 (v108d4b p) (mergeGPR 8 ((if decide ((v108d33 p : BitVec 64) = 0) then 1 else 0 : BitVec 8)) (((((p.shift.setWidth 64).setWidth 32 : BitVec 32).setWidth 64).setWidth 32 : BitVec 32).setWidth 64))).setWidth 8).setWidth 32 : BitVec 32).setWidth 64 : BitVec 64) - 1

def v108d60 (p : Inputs) := (v108d5d p : BitVec 64) &&& (v108d36 p)

def v108d63 (p : Inputs) := (v108d60 p : BitVec 64).sshiftRight 63

def v108d67 (p : Inputs) := addSpec (v108d63 p : BitVec 64) (v108d33 p)

def v108d6a (p : Inputs) := ((v108d67 p).1 : BitVec 64) >>> 63

def v108d87 (p : Inputs) := (v108c54 p : BitVec 64) ^^^ (v108c5f p)

def v108d8a (p : Inputs) := -((((mergeGPR 8 (v108d4b p) (mergeGPR 8 ((if decide ((v108d33 p : BitVec 64) = 0) then 1 else 0 : BitVec 8)) (((((p.shift.setWidth 64).setWidth 32 : BitVec 32).setWidth 64).setWidth 32 : BitVec 32).setWidth 64))).setWidth 8).setWidth 32 : BitVec 32).setWidth 64 : BitVec 64)

def v108d8d (p : Inputs) := (v108d8a p : BitVec 64) &&& (v108d87 p)

def v108d90 (p : Inputs) := (v108d8d p : BitVec 64) ^^^ (v108c5f p)

def v108d9c (p : Inputs) := (v108c51 p : BitVec 64) ^^^ ((v108c9c p).1)

def v108d9f (p : Inputs) := -((((mergeGPR 8 (v108d4b p) (mergeGPR 8 ((if decide ((v108d33 p : BitVec 64) = 0) then 1 else 0 : BitVec 8)) (((((p.shift.setWidth 64).setWidth 32 : BitVec 32).setWidth 64).setWidth 32 : BitVec 32).setWidth 64))).setWidth 8).setWidth 32 : BitVec 32).setWidth 64 : BitVec 64)

def v108da2 (p : Inputs) := (v108d9f p : BitVec 64) &&& (v108d9c p)

def v108da5 (p : Inputs) := (v108da2 p : BitVec 64) ^^^ ((v108c9c p).1)

def v108db1 (p : Inputs) := (v108c37 p : BitVec 64) ^^^ ((v108cd3 p).1)

def v108db4 (p : Inputs) := -((((mergeGPR 8 (v108d4b p) (mergeGPR 8 ((if decide ((v108d33 p : BitVec 64) = 0) then 1 else 0 : BitVec 8)) (((((p.shift.setWidth 64).setWidth 32 : BitVec 32).setWidth 64).setWidth 32 : BitVec 32).setWidth 64))).setWidth 8).setWidth 32 : BitVec 32).setWidth 64 : BitVec 64)

def v108db7 (p : Inputs) := (v108db4 p : BitVec 64) &&& (v108db1 p)

def v108dba (p : Inputs) := (v108db7 p : BitVec 64) ^^^ ((v108cd3 p).1)

def v108dc6 (p : Inputs) := (v108cfb p : BitVec 64) ^^^ ((v108d0d p).1)

def v108dc9 (p : Inputs) := -((((mergeGPR 8 (v108d4b p) (mergeGPR 8 ((if decide ((v108d33 p : BitVec 64) = 0) then 1 else 0 : BitVec 8)) (((((p.shift.setWidth 64).setWidth 32 : BitVec 32).setWidth 64).setWidth 32 : BitVec 32).setWidth 64))).setWidth 8).setWidth 32 : BitVec 32).setWidth 64 : BitVec 64)

def v108dcc (p : Inputs) := (v108dc9 p : BitVec 64) &&& (v108dc6 p)

def v108dcf (p : Inputs) := (v108dcc p : BitVec 64) ^^^ ((v108d0d p).1)

def resultWords (p : Inputs) : Vector (BitVec 64) 4 :=
  #v[v108d90 p, v108da5 p, v108dba p, v108dcf p]

def resultSign (p : Inputs) : BitVec 8 :=
  (mergeGPR 8 (v108d40 p) (((((p.sign.setWidth 32 : BitVec 32).setWidth 64).setWidth 8).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8

end K256.Proofs.Common.Invert.ModularShift
