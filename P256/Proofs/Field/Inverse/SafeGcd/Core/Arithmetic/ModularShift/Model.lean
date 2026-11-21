import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.LinearShift.Model

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift

open X86Proofs

structure Inputs where
  linear : LinearCombination.Inputs
  shift : BitVec 32
  modulus : Vector (BitVec 64) 4
  inverse : BitVec 64
  modulusPtr : BitVec 64

def v1b1597 (p : Inputs) := (((64 : BitVec 32).setWidth 64).setWidth 32 : BitVec 32) - ((p.shift.setWidth 64).setWidth 32)

def v1b15bc (p : Inputs) := (p.inverse : BitVec 64) * ((LinearCombination.resultWords p.linear)[0])

def v1b15c0 (p : Inputs) := (v1b15bc p : BitVec 64) <<< (64 - p.shift.toNat)

def v1b15c3 (p : Inputs) := (v1b15c0 p : BitVec 64) >>> (64 - p.shift.toNat)

def v1b15dc (p : Inputs) := mulResult (p.modulus[0]) (v1b15c3 p)

def v1b15ed (p : Inputs) := mulResult (p.modulus[1]) (v1b15c3 p)

def v1b15ff (p : Inputs) := mulResult (p.modulus[2]) (v1b15c3 p)

def v1b1611 (p : Inputs) := mulResult (p.modulus[3]) (v1b15c3 p)

def v1b1614 (p : Inputs) := addSpec ((v1b15ed p).1 : BitVec 64) ((v1b15dc p).2)

def v1b161c (p : Inputs) := adcSpec ((v1b1614 p).2.CF) ((v1b15ff p).1 : BitVec 64) ((v1b15ed p).2)

def v1b161f (p : Inputs) := adcSpec ((v1b161c p).2.CF) ((v1b1611 p).1 : BitVec 64) ((v1b15ff p).2)

def v1b1622 (p : Inputs) := adcSpec ((v1b161f p).2.CF) ((v1b1611 p).2 : BitVec 64) (0)

def v1b1629 (p : Inputs) := ((LinearCombination.resultWords p.linear)[0] : BitVec 64) - ((v1b15dc p).1)

def v1b162c (p : Inputs) := ~~~((LinearCombination.resultWords p.linear)[0] : BitVec 64)

def v1b1632 (p : Inputs) := ((v1b15dc p).1 : BitVec 64) &&& (v1b162c p)

def v1b1635 (p : Inputs) := (v1b162c p : BitVec 64) ||| ((v1b15dc p).1)

def v1b163d (p : Inputs) := (v1b1635 p : BitVec 64) &&& (v1b1629 p)

def v1b1640 (p : Inputs) := (v1b163d p : BitVec 64) ||| (v1b1632 p)

def v1b164e (p : Inputs) := (v1b1640 p : BitVec 64) >>> 63

def v1b165f (p : Inputs) := (((0 : BitVec 32) : BitVec 32).setWidth 64 : BitVec 64) - (v1b164e p)

def v1b1667 (p : Inputs) := ((LinearCombination.resultWords p.linear)[1] : BitVec 64) - ((v1b1614 p).1)

def v1b166a (p : Inputs) := (v1b165f p : BitVec 64).sshiftRight 63

def v1b166e (p : Inputs) := addSpec (v1b166a p : BitVec 64) (v1b1667 p)

def v1b1671 (p : Inputs) := ~~~((LinearCombination.resultWords p.linear)[1] : BitVec 64)

def v1b1677 (p : Inputs) := ((v1b1614 p).1 : BitVec 64) &&& (v1b1671 p)

def v1b167a (p : Inputs) := (v1b1671 p : BitVec 64) ||| ((v1b1614 p).1)

def v1b167d (p : Inputs) := (v1b167a p : BitVec 64) &&& ((v1b166e p).1)

def v1b1680 (p : Inputs) := (v1b167d p : BitVec 64) ||| (v1b1677 p)

def v1b1683 (p : Inputs) := (v1b1680 p : BitVec 64) >>> 63

def v1b168f (p : Inputs) := (((0 : BitVec 32) : BitVec 32).setWidth 64 : BitVec 64) - (v1b1683 p)

def v1b1697 (p : Inputs) := ((LinearCombination.resultWords p.linear)[2] : BitVec 64) - ((v1b161c p).1)

def v1b169a (p : Inputs) := (v1b168f p : BitVec 64).sshiftRight 63

def v1b169e (p : Inputs) := addSpec (v1b169a p : BitVec 64) (v1b1697 p)

def v1b16a1 (p : Inputs) := ~~~((LinearCombination.resultWords p.linear)[2] : BitVec 64)

def v1b16a7 (p : Inputs) := ((v1b161c p).1 : BitVec 64) &&& (v1b16a1 p)

def v1b16aa (p : Inputs) := (v1b16a1 p : BitVec 64) ||| ((v1b161c p).1)

def v1b16ad (p : Inputs) := (v1b16aa p : BitVec 64) &&& ((v1b169e p).1)

def v1b16b0 (p : Inputs) := (v1b16ad p : BitVec 64) ||| (v1b16a7 p)

def v1b16b3 (p : Inputs) := (v1b16b0 p : BitVec 64) >>> 63

def v1b16bf (p : Inputs) := (((0 : BitVec 32) : BitVec 32).setWidth 64 : BitVec 64) - (v1b16b3 p)

def v1b16c7 (p : Inputs) := ((LinearCombination.resultWords p.linear)[3] : BitVec 64) - ((v1b161f p).1)

def v1b16ca (p : Inputs) := (v1b16bf p : BitVec 64).sshiftRight 63

def v1b16ce (p : Inputs) := addSpec (v1b16ca p : BitVec 64) (v1b16c7 p)

def v1b16d1 (p : Inputs) := ~~~((LinearCombination.resultWords p.linear)[3] : BitVec 64)

def v1b16d7 (p : Inputs) := ((v1b161f p).1 : BitVec 64) &&& (v1b16d1 p)

def v1b16da (p : Inputs) := (v1b16d1 p : BitVec 64) ||| ((v1b161f p).1)

def v1b16e0 (p : Inputs) := (v1b16da p : BitVec 64) &&& ((v1b16ce p).1)

def v1b16e3 (p : Inputs) := (v1b16e0 p : BitVec 64) ||| (v1b16d7 p)

def v1b16e6 (p : Inputs) := (v1b16e3 p : BitVec 64) >>> 63

def v1b16f1 (p : Inputs) := (((0 : BitVec 32) : BitVec 32).setWidth 64 : BitVec 64) - (v1b16e6 p)

def v1b16f9 (p : Inputs) := ((LinearCombination.resultWords p.linear)[4] : BitVec 64) - ((v1b1622 p).1)

def v1b16fc (p : Inputs) := ~~~((LinearCombination.resultWords p.linear)[4] : BitVec 64)

def v1b1702 (p : Inputs) := ((v1b1622 p).1 : BitVec 64) &&& (v1b16fc p)

def v1b1705 (p : Inputs) := (v1b16fc p : BitVec 64) ||| ((v1b1622 p).1)

def v1b1708 (p : Inputs) := (v1b16f1 p : BitVec 64).sshiftRight 63

def v1b170c (p : Inputs) := addSpec (v1b1708 p : BitVec 64) (v1b16f9 p)

def v1b170f (p : Inputs) := (v1b1705 p : BitVec 64) &&& ((v1b170c p).1)

def v1b1712 (p : Inputs) := (v1b170f p : BitVec 64) ||| (v1b1702 p)

def v1b1715 (p : Inputs) := (v1b1712 p : BitVec 64) >>> 63

def v1b172b (p : Inputs) := -(v1b1629 p : BitVec 64)

def v1b1734 (p : Inputs) := P256.Proofs.Common.Instructions.Carry.sbbSpec ((0 : BitVec 32).setWidth 64 : BitVec 64) ((v1b166e p).1) (BitVec.ofBool (decide ((v1b1629 p : BitVec 64) ≠ 0)))

def v1b173c (p : Inputs) := P256.Proofs.Common.Instructions.Carry.sbbSpec ((0 : BitVec 32).setWidth 64 : BitVec 64) ((v1b169e p).1) (BitVec.ofBool ((v1b1734 p).2.CF))

def v1b173f (p : Inputs) := P256.Proofs.Common.Instructions.Carry.sbbSpec (((0 : BitVec 32) : BitVec 32).setWidth 64 : BitVec 64) ((v1b16ce p).1) (BitVec.ofBool ((v1b173c p).2.CF))

def v1b17b1 (p : Inputs) := ((v1b173f p).1 : BitVec 64) ^^^ ((v1b16ce p).1)

def v1b17b4 (p : Inputs) := -((((if !(decide ((v1b1715 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)).setWidth 32 : BitVec 32).setWidth 64 : BitVec 64)

def v1b17b7 (p : Inputs) := (v1b17b4 p : BitVec 64) &&& (v1b17b1 p)

def v1b17ba (p : Inputs) := (v1b17b7 p : BitVec 64) ^^^ ((v1b16ce p).1)

def v1b17bd (p : Inputs) := ((v1b173c p).1 : BitVec 64) ^^^ ((v1b169e p).1)

def v1b17c0 (p : Inputs) := -((((if !(decide ((v1b1715 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)).setWidth 32 : BitVec 32).setWidth 64 : BitVec 64)

def v1b17c3 (p : Inputs) := (v1b17c0 p : BitVec 64) &&& (v1b17bd p)

def v1b17c6 (p : Inputs) := (v1b17c3 p : BitVec 64) ^^^ ((v1b169e p).1)

def v1b17c9 (p : Inputs) := ((v1b1734 p).1 : BitVec 64) ^^^ ((v1b166e p).1)

def v1b17cc (p : Inputs) := -((((if !(decide ((v1b1715 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)).setWidth 32 : BitVec 32).setWidth 64 : BitVec 64)

def v1b17cf (p : Inputs) := (v1b17cc p : BitVec 64) &&& (v1b17c9 p)

def v1b17d2 (p : Inputs) := (v1b17cf p : BitVec 64) ^^^ ((v1b166e p).1)

def v1b17d5 (p : Inputs) := (((((if !((v1b173f p).2.CF) then 1 else 0 : BitVec 8)).setWidth 32 : BitVec 32).setWidth 64).setWidth 32 : BitVec 32) &&& (1)

def v1b17db (p : Inputs) := ~~~((v1b170c p).1 : BitVec 64)

def v1b17de (p : Inputs) := addSpec (v1b17db p : BitVec 64) ((v1b17d5 p : BitVec 32).setWidth 64)

def v1b17e1 (p : Inputs) := ((v1b17de p).1 : BitVec 64) ^^^ ((v1b170c p).1)

def v1b17ea (p : Inputs) := -((((if !(decide ((v1b1715 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)).setWidth 32 : BitVec 32).setWidth 64 : BitVec 64)

def v1b17ed (p : Inputs) := (v1b17ea p : BitVec 64) &&& (v1b17e1 p)

def v1b17f0 (p : Inputs) := (v1b17ed p : BitVec 64) ^^^ ((v1b170c p).1)

def v1b17fa (p : Inputs) := (v1b17f0 p : BitVec 64) <<< (64 - p.shift.toNat)

def v1b1802 (p : Inputs) := (v1b172b p : BitVec 64) ^^^ (v1b1629 p)

def v1b1805 (p : Inputs) := -((((if !(decide ((v1b1715 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)).setWidth 32 : BitVec 32).setWidth 64 : BitVec 64)

def v1b1811 (p : Inputs) := (v1b17ba p : BitVec 64) >>> p.shift.toNat

def v1b1816 (p : Inputs) := (v1b17ba p : BitVec 64) <<< (64 - p.shift.toNat)

def v1b181e (p : Inputs) := (v1b17c6 p : BitVec 64) >>> p.shift.toNat

def v1b1821 (p : Inputs) := (v1b1805 p : BitVec 64) &&& (v1b1802 p)

def v1b1824 (p : Inputs) := (v1b1821 p : BitVec 64) ^^^ (v1b1629 p)

def v1b1827 (p : Inputs) := (v1b181e p : BitVec 64) ||| (v1b1816 p)

def v1b182c (p : Inputs) := (v1b17c6 p : BitVec 64) <<< (64 - p.shift.toNat)

def v1b1834 (p : Inputs) := (v1b17d2 p : BitVec 64) >>> p.shift.toNat

def v1b1839 (p : Inputs) := (v1b17d2 p : BitVec 64) <<< (64 - p.shift.toNat)

def v1b183e (p : Inputs) := (v1b1824 p : BitVec 64) >>> p.shift.toNat

def v1b1841 (p : Inputs) := (v1b1834 p : BitVec 64) ||| (v1b182c p)

def v1b1844 (p : Inputs) := (v1b183e p : BitVec 64) ||| (v1b1839 p)

def v1b184f (p : Inputs) := (v1b1844 p : BitVec 64) - (p.modulus[0])

def v1b1855 (p : Inputs) := ~~~(v1b1844 p : BitVec 64)

def v1b185b (p : Inputs) := (p.modulus[0] : BitVec 64) &&& (v1b1855 p)

def v1b185e (p : Inputs) := (v1b1855 p : BitVec 64) ||| (p.modulus[0])

def v1b1861 (p : Inputs) := (v1b185e p : BitVec 64) &&& (v1b184f p)

def v1b1864 (p : Inputs) := (v1b1861 p : BitVec 64) ||| (v1b185b p)

def v1b1867 (p : Inputs) := (v1b1864 p : BitVec 64) >>> 63

def v1b1878 (p : Inputs) := (((0 : BitVec 32) : BitVec 32).setWidth 64 : BitVec 64) - (v1b1867 p)

def v1b1885 (p : Inputs) := (v1b1841 p : BitVec 64) - (p.modulus[1])

def v1b1888 (p : Inputs) := (v1b1878 p : BitVec 64).sshiftRight 63

def v1b188c (p : Inputs) := addSpec (v1b1888 p : BitVec 64) (v1b1885 p)

def v1b1892 (p : Inputs) := ~~~(v1b1841 p : BitVec 64)

def v1b1898 (p : Inputs) := (p.modulus[1] : BitVec 64) &&& (v1b1892 p)

def v1b189b (p : Inputs) := (v1b1892 p : BitVec 64) ||| (p.modulus[1])

def v1b189e (p : Inputs) := (v1b189b p : BitVec 64) &&& ((v1b188c p).1)

def v1b18a1 (p : Inputs) := (v1b189e p : BitVec 64) ||| (v1b1898 p)

def v1b18a4 (p : Inputs) := (v1b18a1 p : BitVec 64) >>> 63

def v1b18af (p : Inputs) := (((0 : BitVec 32) : BitVec 32).setWidth 64 : BitVec 64) - (v1b18a4 p)

def v1b18bc (p : Inputs) := (v1b1827 p : BitVec 64) - (p.modulus[2])

def v1b18bf (p : Inputs) := (v1b18af p : BitVec 64).sshiftRight 63

def v1b18c3 (p : Inputs) := addSpec (v1b18bf p : BitVec 64) (v1b18bc p)

def v1b18c9 (p : Inputs) := ~~~(v1b1827 p : BitVec 64)

def v1b18cf (p : Inputs) := (p.modulus[2] : BitVec 64) &&& (v1b18c9 p)

def v1b18d2 (p : Inputs) := (v1b18c9 p : BitVec 64) ||| (p.modulus[2])

def v1b18d5 (p : Inputs) := (v1b18d2 p : BitVec 64) &&& ((v1b18c3 p).1)

def v1b18d8 (p : Inputs) := (v1b18d5 p : BitVec 64) ||| (v1b18cf p)

def v1b18db (p : Inputs) := (v1b18d8 p : BitVec 64) >>> 63

def v1b18e6 (p : Inputs) := (((0 : BitVec 32) : BitVec 32).setWidth 64 : BitVec 64) - (v1b18db p)

def v1b18eb (p : Inputs) := (v1b1811 p : BitVec 64) ||| (v1b17fa p)

def v1b18f6 (p : Inputs) := (v1b18eb p : BitVec 64) - (p.modulus[3])

def v1b18f9 (p : Inputs) := (v1b18e6 p : BitVec 64).sshiftRight 63

def v1b18fd (p : Inputs) := addSpec (v1b18f9 p : BitVec 64) (v1b18f6 p)

def v1b1903 (p : Inputs) := ~~~(v1b18eb p : BitVec 64)

def v1b1909 (p : Inputs) := (p.modulus[3] : BitVec 64) &&& (v1b1903 p)

def v1b190c (p : Inputs) := (v1b1903 p : BitVec 64) ||| (p.modulus[3])

def v1b190f (p : Inputs) := (v1b190c p : BitVec 64) &&& ((v1b18fd p).1)

def v1b1912 (p : Inputs) := (v1b190f p : BitVec 64) ||| (v1b1909 p)

def v1b1915 (p : Inputs) := (v1b1912 p : BitVec 64) >>> 63

def v1b1923 (p : Inputs) := (v1b17f0 p : BitVec 64) >>> p.shift.toNat

def v1b1926 (p : Inputs) := (((0 : BitVec 32) : BitVec 32).setWidth 64 : BitVec 64) - (v1b1915 p)

def v1b1930 (p : Inputs) := (((((((LinearCombination.resultSign p.linear).setWidth 32 : BitVec 32).setWidth 64).setWidth 8).setWidth 32 : BitVec 32).setWidth 64).setWidth 8 : BitVec 8) ^^^ ((mergeGPR 8 ((if !(decide ((v1b1715 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)) ((0 : BitVec 64))).setWidth 8)

def v1b193b (p : Inputs) := ((mergeGPR 8 ((if decide ((v1b1923 p : BitVec 64) = 0) then 1 else 0 : BitVec 8)) (((((p.shift.setWidth 64).setWidth 32 : BitVec 32).setWidth 64).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8 : BitVec 8) &&& ((v1b1926 p).setWidth 8)

def v1b194d (p : Inputs) := ((((mergeGPR 8 (v1b193b p) (mergeGPR 8 ((if decide ((v1b1923 p : BitVec 64) = 0) then 1 else 0 : BitVec 8)) (((((p.shift.setWidth 64).setWidth 32 : BitVec 32).setWidth 64).setWidth 32 : BitVec 32).setWidth 64))).setWidth 8).setWidth 32 : BitVec 32).setWidth 64 : BitVec 64) - 1

def v1b1950 (p : Inputs) := (v1b194d p : BitVec 64) &&& (v1b1926 p)

def v1b1953 (p : Inputs) := (v1b1950 p : BitVec 64).sshiftRight 63

def v1b1957 (p : Inputs) := addSpec (v1b1953 p : BitVec 64) (v1b1923 p)

def v1b195a (p : Inputs) := ((v1b1957 p).1 : BitVec 64) >>> 63

def v1b1977 (p : Inputs) := (v1b1844 p : BitVec 64) ^^^ (v1b184f p)

def v1b197a (p : Inputs) := -((((mergeGPR 8 (v1b193b p) (mergeGPR 8 ((if decide ((v1b1923 p : BitVec 64) = 0) then 1 else 0 : BitVec 8)) (((((p.shift.setWidth 64).setWidth 32 : BitVec 32).setWidth 64).setWidth 32 : BitVec 32).setWidth 64))).setWidth 8).setWidth 32 : BitVec 32).setWidth 64 : BitVec 64)

def v1b197d (p : Inputs) := (v1b197a p : BitVec 64) &&& (v1b1977 p)

def v1b1980 (p : Inputs) := (v1b197d p : BitVec 64) ^^^ (v1b184f p)

def v1b198c (p : Inputs) := (v1b1841 p : BitVec 64) ^^^ ((v1b188c p).1)

def v1b198f (p : Inputs) := -((((mergeGPR 8 (v1b193b p) (mergeGPR 8 ((if decide ((v1b1923 p : BitVec 64) = 0) then 1 else 0 : BitVec 8)) (((((p.shift.setWidth 64).setWidth 32 : BitVec 32).setWidth 64).setWidth 32 : BitVec 32).setWidth 64))).setWidth 8).setWidth 32 : BitVec 32).setWidth 64 : BitVec 64)

def v1b1992 (p : Inputs) := (v1b198f p : BitVec 64) &&& (v1b198c p)

def v1b1995 (p : Inputs) := (v1b1992 p : BitVec 64) ^^^ ((v1b188c p).1)

def v1b19a1 (p : Inputs) := (v1b1827 p : BitVec 64) ^^^ ((v1b18c3 p).1)

def v1b19a4 (p : Inputs) := -((((mergeGPR 8 (v1b193b p) (mergeGPR 8 ((if decide ((v1b1923 p : BitVec 64) = 0) then 1 else 0 : BitVec 8)) (((((p.shift.setWidth 64).setWidth 32 : BitVec 32).setWidth 64).setWidth 32 : BitVec 32).setWidth 64))).setWidth 8).setWidth 32 : BitVec 32).setWidth 64 : BitVec 64)

def v1b19a7 (p : Inputs) := (v1b19a4 p : BitVec 64) &&& (v1b19a1 p)

def v1b19aa (p : Inputs) := (v1b19a7 p : BitVec 64) ^^^ ((v1b18c3 p).1)

def v1b19b6 (p : Inputs) := (v1b18eb p : BitVec 64) ^^^ ((v1b18fd p).1)

def v1b19b9 (p : Inputs) := -((((mergeGPR 8 (v1b193b p) (mergeGPR 8 ((if decide ((v1b1923 p : BitVec 64) = 0) then 1 else 0 : BitVec 8)) (((((p.shift.setWidth 64).setWidth 32 : BitVec 32).setWidth 64).setWidth 32 : BitVec 32).setWidth 64))).setWidth 8).setWidth 32 : BitVec 32).setWidth 64 : BitVec 64)

def v1b19bc (p : Inputs) := (v1b19b9 p : BitVec 64) &&& (v1b19b6 p)

def v1b19bf (p : Inputs) := (v1b19bc p : BitVec 64) ^^^ ((v1b18fd p).1)

def resultWords (p : Inputs) : Vector (BitVec 64) 4 :=
  #v[v1b1980 p, v1b1995 p, v1b19aa p, v1b19bf p]

def resultSign (p : Inputs) : BitVec 8 :=
  (mergeGPR 8 (v1b1930 p) ((((((LinearCombination.resultSign p.linear).setWidth 32 : BitVec 32).setWidth 64).setWidth 8).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8

end P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift
