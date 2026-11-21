import X86Proofs.Instructions.Adc.Operation
import X86Proofs.Instructions.Mul.Operation
import X86Proofs.Instructions.Sbb.Operation

namespace K256.Proofs.Common.Invert.LinearCombination

open X86Proofs

structure Inputs where
  a : Vector (BitVec 64) 4
  b : Vector (BitVec 64) 4
  aSign : BitVec 8
  bSign : BitVec 8
  u : BitVec 64
  v : BitVec 64

def v1084f4 (p : Inputs) := (p.u : BitVec 64) >>> 63

def v108500 (p : Inputs) := -(p.u : BitVec 64)

def v10850d (p : Inputs) := (v108500 p : BitVec 64) ^^^ (p.u)

def v108510 (p : Inputs) := -((((v1084f4 p).setWidth 8).setWidth 32 : BitVec 32).setWidth 64 : BitVec 64)

def v108513 (p : Inputs) := (v108510 p : BitVec 64) &&& (v10850d p)

def v108516 (p : Inputs) := (v108513 p : BitVec 64) ^^^ (p.u)

def v10851c (p : Inputs) := (p.v : BitVec 64) >>> 63

def v10852e (p : Inputs) := mulResult (v108516 p) (p.a[0])

def v10853a (p : Inputs) := -(p.v : BitVec 64)

def v108540 (p : Inputs) := mulResult (v108516 p) (p.a[1])

def v10854f (p : Inputs) := (v10853a p : BitVec 64) ^^^ (p.v)

def v108555 (p : Inputs) := mulResult (v108516 p) (p.a[2])

def v10855f (p : Inputs) := -((((v10851c p).setWidth 8).setWidth 32 : BitVec 32).setWidth 64 : BitVec 64)

def v108562 (p : Inputs) := (v10855f p : BitVec 64) &&& (v10854f p)

def v108568 (p : Inputs) := mulResult (v108516 p) (p.a[3])

def v108572 (p : Inputs) := (v108562 p : BitVec 64) ^^^ (p.v)

def v108575 (p : Inputs) := addSpec ((v108540 p).1 : BitVec 64) ((v10852e p).2)

def v108578 (p : Inputs) := adcSpec ((v108575 p).2.CF) ((v108555 p).1 : BitVec 64) ((v108540 p).2)

def v10857b (p : Inputs) := adcSpec ((v108578 p).2.CF) ((v108568 p).1 : BitVec 64) ((v108555 p).2)

def v10857e (p : Inputs) := adcSpec ((v10857b p).2.CF) ((v108568 p).2 : BitVec 64) (0)

def v108585 (p : Inputs) := mulResult (v108572 p) (p.b[0])

def v108595 (p : Inputs) := mulResult (v108572 p) (p.b[1])

def v1085a4 (p : Inputs) := mulResult (v108572 p) (p.b[2])

def v1085b3 (p : Inputs) := ((v1084f4 p).setWidth 8 : BitVec 8) ^^^ (p.aSign)

def v1085bf (p : Inputs) := mulResult (v108572 p) (p.b[3])

def v1085c3 (p : Inputs) := addSpec ((v108595 p).1 : BitVec 64) ((v108585 p).2)

def v1085c8 (p : Inputs) := adcSpec ((v1085c3 p).2.CF) ((v1085a4 p).1 : BitVec 64) ((v108595 p).2)

def v1085d5 (p : Inputs) := adcSpec ((v1085c8 p).2.CF) ((v1085bf p).1 : BitVec 64) ((v1085a4 p).2)

def v1085d8 (p : Inputs) := adcSpec ((v1085d5 p).2.CF) ((v1085bf p).2 : BitVec 64) (0)

def v1085e6 (p : Inputs) := ((v10851c p).setWidth 8 : BitVec 8) ^^^ (p.bSign)

def v1085f2 (p : Inputs) := ((((mergeGPR 8 (v1085e6 p) (v10851c p)).setWidth 32 : BitVec 32).setWidth 64).setWidth 8 : BitVec 8) ^^^ ((mergeGPR 8 (v1085b3 p) (v1084f4 p)).setWidth 8)

def v1085fa (p : Inputs) := ((mergeGPR 8 (v1085f2 p) (((mergeGPR 8 (v1085e6 p) (v10851c p)).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8 : BitVec 8) ^^^ (1)

def v108606 (p : Inputs) := -((v108585 p).1 : BitVec 64)

def v10860e (p : Inputs) := sbbSpec (decide (((v108585 p).1 : BitVec 64) ≠ 0)) ((0 : BitVec 32).setWidth 64 : BitVec 64) ((v1085c3 p).1)

def v108617 (p : Inputs) := sbbSpec ((v10860e p).2.CF) ((0 : BitVec 32).setWidth 64 : BitVec 64) ((v1085c8 p).1)

def v10861f (p : Inputs) := sbbSpec ((v108617 p).2.CF) ((0 : BitVec 32).setWidth 64 : BitVec 64) ((v1085d5 p).1)

def v108639 (p : Inputs) := (v108606 p : BitVec 64) ^^^ ((v108585 p).1)

def v108640 (p : Inputs) := -((((mergeGPR 8 (v1085fa p) (mergeGPR 8 (v1085f2 p) (((mergeGPR 8 (v1085e6 p) (v10851c p)).setWidth 32 : BitVec 32).setWidth 64))).setWidth 8).setWidth 32 : BitVec 32).setWidth 64 : BitVec 64)

def v108643 (p : Inputs) := (v108640 p : BitVec 64) &&& (v108639 p)

def v108646 (p : Inputs) := (v108643 p : BitVec 64) ^^^ ((v108585 p).1)

def v108650 (p : Inputs) := ((v10860e p).1 : BitVec 64) ^^^ ((v1085c3 p).1)

def v108658 (p : Inputs) := -((((mergeGPR 8 (v1085fa p) (mergeGPR 8 (v1085f2 p) (((mergeGPR 8 (v1085e6 p) (v10851c p)).setWidth 32 : BitVec 32).setWidth 64))).setWidth 8).setWidth 32 : BitVec 32).setWidth 64 : BitVec 64)

def v10865b (p : Inputs) := (v108658 p : BitVec 64) &&& (v108650 p)

def v10865e (p : Inputs) := (v10865b p : BitVec 64) ^^^ ((v1085c3 p).1)

def v10866d (p : Inputs) := ((v108617 p).1 : BitVec 64) ^^^ ((v1085c8 p).1)

def v108674 (p : Inputs) := -((((mergeGPR 8 (v1085fa p) (mergeGPR 8 (v1085f2 p) (((mergeGPR 8 (v1085e6 p) (v10851c p)).setWidth 32 : BitVec 32).setWidth 64))).setWidth 8).setWidth 32 : BitVec 32).setWidth 64 : BitVec 64)

def v108677 (p : Inputs) := (v108674 p : BitVec 64) &&& (v10866d p)

def v10867a (p : Inputs) := (v108677 p : BitVec 64) ^^^ ((v1085c8 p).1)

def v108681 (p : Inputs) := ((v10861f p).1 : BitVec 64) ^^^ ((v1085d5 p).1)

def v108689 (p : Inputs) := -((((mergeGPR 8 (v1085fa p) (mergeGPR 8 (v1085f2 p) (((mergeGPR 8 (v1085e6 p) (v10851c p)).setWidth 32 : BitVec 32).setWidth 64))).setWidth 8).setWidth 32 : BitVec 32).setWidth 64 : BitVec 64)

def v10868c (p : Inputs) := (v108689 p : BitVec 64) &&& (v108681 p)

def v10868f (p : Inputs) := (v10868c p : BitVec 64) ^^^ ((v1085d5 p).1)

def v10869c (p : Inputs) := ((v10852e p).1 : BitVec 64) - (v108646 p)

def v10869f (p : Inputs) := ~~~((v10852e p).1 : BitVec 64)

def v1086a5 (p : Inputs) := (v108646 p : BitVec 64) &&& (v10869f p)

def v1086a8 (p : Inputs) := (v10869f p : BitVec 64) ||| (v108646 p)

def v1086ab (p : Inputs) := (v1086a8 p : BitVec 64) &&& (v10869c p)

def v1086ae (p : Inputs) := (v1086ab p : BitVec 64) ||| (v1086a5 p)

def v1086b1 (p : Inputs) := (v1086ae p : BitVec 64) >>> 63

def v1086c4 (p : Inputs) := (((0 : BitVec 32) : BitVec 32).setWidth 64 : BitVec 64) - (v1086b1 p)

def v1086cb (p : Inputs) := ((v108575 p).1 : BitVec 64) - (v10865e p)

def v1086ce (p : Inputs) := (v1086c4 p : BitVec 64).sshiftRight 63

def v1086d2 (p : Inputs) := addSpec (v1086ce p : BitVec 64) (v1086cb p)

def v1086d5 (p : Inputs) := ~~~((v108575 p).1 : BitVec 64)

def v1086db (p : Inputs) := (v10865e p : BitVec 64) &&& (v1086d5 p)

def v1086de (p : Inputs) := (v1086d5 p : BitVec 64) ||| (v10865e p)

def v1086e1 (p : Inputs) := (v1086de p : BitVec 64) &&& ((v1086d2 p).1)

def v1086e4 (p : Inputs) := (v1086e1 p : BitVec 64) ||| (v1086db p)

def v1086e7 (p : Inputs) := (v1086e4 p : BitVec 64) >>> 63

def v1086f2 (p : Inputs) := (((0 : BitVec 32) : BitVec 32).setWidth 64 : BitVec 64) - (v1086e7 p)

def v1086f9 (p : Inputs) := ((v108578 p).1 : BitVec 64) - (v10867a p)

def v1086fc (p : Inputs) := (v1086f2 p : BitVec 64).sshiftRight 63

def v108700 (p : Inputs) := addSpec (v1086fc p : BitVec 64) (v1086f9 p)

def v108703 (p : Inputs) := ~~~((v108578 p).1 : BitVec 64)

def v108709 (p : Inputs) := (v10867a p : BitVec 64) &&& (v108703 p)

def v10870c (p : Inputs) := (v108703 p : BitVec 64) ||| (v10867a p)

def v10870f (p : Inputs) := (v10870c p : BitVec 64) &&& ((v108700 p).1)

def v108712 (p : Inputs) := (v10870f p : BitVec 64) ||| (v108709 p)

def v108715 (p : Inputs) := (v108712 p : BitVec 64) >>> 63

def v108720 (p : Inputs) := (((0 : BitVec 32) : BitVec 32).setWidth 64 : BitVec 64) - (v108715 p)

def v108727 (p : Inputs) := ((v10857b p).1 : BitVec 64) - (v10868f p)

def v10872a (p : Inputs) := (v108720 p : BitVec 64).sshiftRight 63

def v10872e (p : Inputs) := addSpec (v10872a p : BitVec 64) (v108727 p)

def v108731 (p : Inputs) := ~~~((v10857b p).1 : BitVec 64)

def v108737 (p : Inputs) := (v10868f p : BitVec 64) &&& (v108731 p)

def v10873a (p : Inputs) := (v108731 p : BitVec 64) ||| (v10868f p)

def v10873d (p : Inputs) := (v10873a p : BitVec 64) &&& ((v10872e p).1)

def v108740 (p : Inputs) := (v10873d p : BitVec 64) ||| (v108737 p)

def v108743 (p : Inputs) := (v108740 p : BitVec 64) >>> 63

def v10874d (p : Inputs) := (((0 : BitVec 32) : BitVec 32).setWidth 64 : BitVec 64) - (v108743 p)

def v108756 (p : Inputs) := (((((if !((v10861f p).2.CF) then 1 else 0 : BitVec 8)).setWidth 32 : BitVec 32).setWidth 64).setWidth 32 : BitVec 32) &&& (1)

def v108762 (p : Inputs) := ~~~((v1085d8 p).1 : BitVec 64)

def v108765 (p : Inputs) := addSpec (v108762 p : BitVec 64) ((v108756 p : BitVec 32).setWidth 64)

def v108768 (p : Inputs) := ((v108765 p).1 : BitVec 64) ^^^ ((v1085d8 p).1)

def v10876b (p : Inputs) := -((((mergeGPR 8 (v1085fa p) (mergeGPR 8 (v1085f2 p) (((mergeGPR 8 (v1085e6 p) (v10851c p)).setWidth 32 : BitVec 32).setWidth 64))).setWidth 8).setWidth 32 : BitVec 32).setWidth 64 : BitVec 64)

def v10876e (p : Inputs) := (v10876b p : BitVec 64) &&& (v108768 p)

def v108771 (p : Inputs) := (v10876e p : BitVec 64) ^^^ ((v1085d8 p).1)

def v108777 (p : Inputs) := ((v10857e p).1 : BitVec 64) - (v108771 p)

def v10877a (p : Inputs) := ~~~((v10857e p).1 : BitVec 64)

def v108780 (p : Inputs) := (v108771 p : BitVec 64) &&& (v10877a p)

def v108783 (p : Inputs) := (v10877a p : BitVec 64) ||| (v108771 p)

def v108786 (p : Inputs) := (v10874d p : BitVec 64).sshiftRight 63

def v10878a (p : Inputs) := addSpec (v108786 p : BitVec 64) (v108777 p)

def v10878d (p : Inputs) := (v108783 p : BitVec 64) &&& ((v10878a p).1)

def v108790 (p : Inputs) := (v10878d p : BitVec 64) ||| (v108780 p)

def v108793 (p : Inputs) := (v108790 p : BitVec 64) >>> 63

def v1087a3 (p : Inputs) := (((((mergeGPR 8 (v1085f2 p) (((mergeGPR 8 (v1085e6 p) (v10851c p)).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64).setWidth 8 : BitVec 8) &&& (1)

def v1087bb (p : Inputs) := -(v10869c p : BitVec 64)

def v1087c4 (p : Inputs) := sbbSpec (decide ((v10869c p : BitVec 64) ≠ 0)) ((0 : BitVec 32).setWidth 64 : BitVec 64) ((v1086d2 p).1)

def v1087cd (p : Inputs) := sbbSpec ((v1087c4 p).2.CF) ((0 : BitVec 32).setWidth 64 : BitVec 64) ((v108700 p).1)

def v1087d0 (p : Inputs) := sbbSpec ((v1087cd p).2.CF) ((0 : BitVec 32).setWidth 64 : BitVec 64) ((v10872e p).1)

def v1087d6 (p : Inputs) := ~~~((v10878a p).1 : BitVec 64)

def v1087e4 (p : Inputs) := (((((if !((v1087d0 p).2.CF) then 1 else 0 : BitVec 8)).setWidth 32 : BitVec 32).setWidth 64).setWidth 32 : BitVec 32) &&& (1)

def v1087e7 (p : Inputs) := addSpec ((v1087e4 p : BitVec 32).setWidth 64 : BitVec 64) (v1087d6 p)

def v1087f0 (p : Inputs) := (v1087bb p : BitVec 64) ^^^ (v10869c p)

def v1087f7 (p : Inputs) := -((((((if decide ((v108793 p : BitVec 64) = (0)) then (((0 : BitVec 32).setWidth 64).setWidth 32) else (((((mergeGPR 8 (v1087a3 p) ((((mergeGPR 8 (v1085f2 p) (((mergeGPR 8 (v1085e6 p) (v10851c p)).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64).setWidth 32)) : BitVec 32).setWidth 64).setWidth 8).setWidth 32 : BitVec 32).setWidth 64 : BitVec 64)

def v1087fa (p : Inputs) := (v1087f7 p : BitVec 64) &&& (v1087f0 p)

def v1087fd (p : Inputs) := (v1087fa p : BitVec 64) ^^^ (v10869c p)

def v108807 (p : Inputs) := ((v1087c4 p).1 : BitVec 64) ^^^ ((v1086d2 p).1)

def v10880a (p : Inputs) := -((((((if decide ((v108793 p : BitVec 64) = (0)) then (((0 : BitVec 32).setWidth 64).setWidth 32) else (((((mergeGPR 8 (v1087a3 p) ((((mergeGPR 8 (v1085f2 p) (((mergeGPR 8 (v1085e6 p) (v10851c p)).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64).setWidth 32)) : BitVec 32).setWidth 64).setWidth 8).setWidth 32 : BitVec 32).setWidth 64 : BitVec 64)

def v10880d (p : Inputs) := (v10880a p : BitVec 64) &&& (v108807 p)

def v108810 (p : Inputs) := (v10880d p : BitVec 64) ^^^ ((v1086d2 p).1)

def v10881b (p : Inputs) := ((v1087cd p).1 : BitVec 64) ^^^ ((v108700 p).1)

def v10881e (p : Inputs) := -((((((if decide ((v108793 p : BitVec 64) = (0)) then (((0 : BitVec 32).setWidth 64).setWidth 32) else (((((mergeGPR 8 (v1087a3 p) ((((mergeGPR 8 (v1085f2 p) (((mergeGPR 8 (v1085e6 p) (v10851c p)).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64).setWidth 32)) : BitVec 32).setWidth 64).setWidth 8).setWidth 32 : BitVec 32).setWidth 64 : BitVec 64)

def v108821 (p : Inputs) := (v10881e p : BitVec 64) &&& (v10881b p)

def v108824 (p : Inputs) := (v108821 p : BitVec 64) ^^^ ((v108700 p).1)

def v10882f (p : Inputs) := ((v1087d0 p).1 : BitVec 64) ^^^ ((v10872e p).1)

def v108832 (p : Inputs) := -((((((if decide ((v108793 p : BitVec 64) = (0)) then (((0 : BitVec 32).setWidth 64).setWidth 32) else (((((mergeGPR 8 (v1087a3 p) ((((mergeGPR 8 (v1085f2 p) (((mergeGPR 8 (v1085e6 p) (v10851c p)).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64).setWidth 32)) : BitVec 32).setWidth 64).setWidth 8).setWidth 32 : BitVec 32).setWidth 64 : BitVec 64)

def v108835 (p : Inputs) := (v108832 p : BitVec 64) &&& (v10882f p)

def v108838 (p : Inputs) := (v108835 p : BitVec 64) ^^^ ((v10872e p).1)

def v108846 (p : Inputs) := ((v1087e7 p).1 : BitVec 64) ^^^ ((v10878a p).1)

def v108849 (p : Inputs) := -((((((if decide ((v108793 p : BitVec 64) = (0)) then (((0 : BitVec 32).setWidth 64).setWidth 32) else (((((mergeGPR 8 (v1087a3 p) ((((mergeGPR 8 (v1085f2 p) (((mergeGPR 8 (v1085e6 p) (v10851c p)).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64).setWidth 32)) : BitVec 32).setWidth 64).setWidth 8).setWidth 32 : BitVec 32).setWidth 64 : BitVec 64)

def v10884c (p : Inputs) := (v108849 p : BitVec 64) &&& (v108846 p)

def v10884f (p : Inputs) := (v10884c p : BitVec 64) ^^^ ((v10878a p).1)

def v108857 (p : Inputs) := ((mergeGPR 8 (v1085e6 p) (v10851c p)).setWidth 8 : BitVec 8) &&& ((((if decide ((v108793 p : BitVec 64) = (0)) then (((0 : BitVec 32).setWidth 64).setWidth 32) else (((((mergeGPR 8 (v1087a3 p) ((((mergeGPR 8 (v1085f2 p) (((mergeGPR 8 (v1085e6 p) (v10851c p)).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64).setWidth 32)) : BitVec 32).setWidth 64).setWidth 8)

def v108859 (p : Inputs) := ((((if decide ((v108793 p : BitVec 64) = (0)) then (((0 : BitVec 32).setWidth 64).setWidth 32) else (((((mergeGPR 8 (v1087a3 p) ((((mergeGPR 8 (v1085f2 p) (((mergeGPR 8 (v1085e6 p) (v10851c p)).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64).setWidth 32)) : BitVec 32).setWidth 64).setWidth 8 : BitVec 8) ^^^ (1)

def v10885c (p : Inputs) := ((mergeGPR 8 (v108859 p) (((if decide ((v108793 p : BitVec 64) = (0)) then (((0 : BitVec 32).setWidth 64).setWidth 32) else (((((mergeGPR 8 (v1087a3 p) ((((mergeGPR 8 (v1085f2 p) (((mergeGPR 8 (v1085e6 p) (v10851c p)).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64).setWidth 32)) : BitVec 32).setWidth 64)).setWidth 8 : BitVec 8) &&& ((mergeGPR 8 (v1085b3 p) (v1084f4 p)).setWidth 8)

def v108876 (p : Inputs) := ((mergeGPR 8 (v108857 p) (mergeGPR 8 (v1085e6 p) (v10851c p))).setWidth 8 : BitVec 8) ||| ((mergeGPR 8 (v10885c p) (mergeGPR 8 (v108859 p) (((if decide ((v108793 p : BitVec 64) = (0)) then (((0 : BitVec 32).setWidth 64).setWidth 32) else (((((mergeGPR 8 (v1087a3 p) ((((mergeGPR 8 (v1085f2 p) (((mergeGPR 8 (v1085e6 p) (v10851c p)).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64).setWidth 32)) : BitVec 32).setWidth 64))).setWidth 8)

def resultWords (p : Inputs) : Vector (BitVec 64) 5 :=
  #v[v1087fd p, v108810 p, v108824 p, v108838 p, v10884f p]

def resultSign (p : Inputs) : BitVec 8 :=
  (mergeGPR 8 (v108876 p) (mergeGPR 8 (v108857 p) (mergeGPR 8 (v1085e6 p) (v10851c p)))).setWidth 8

end K256.Proofs.Common.Invert.LinearCombination
