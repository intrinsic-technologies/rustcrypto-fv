import X86Proofs.Instructions.Mul.Operation
import X86Proofs.Instructions.Adc.Operation
import X86Proofs.Instructions.Add.Operation

namespace P256.Proofs.Scalar.Multiply.Barrett

open X86Proofs

structure Inputs where
  low : Vector (BitVec 64) 4
  high : Vector (BitVec 64) 4

def v118347 (p : Inputs) := mulResult (p.low[3]) (85565669623438334)

def v11835a (p : Inputs) := mulResult (p.low[3]) (4834901528447446049)

def v118370 (p : Inputs) := mulResult (p.low[3]) (18446744069414584319)

def v118386 (p : Inputs) := mulResult (p.low[3]) ((4294967295 : BitVec 32).setWidth 64)

def v11838f (p : Inputs) := addSpec ((v11835a p).1 : BitVec 64) ((v118347 p).2)

def v118392 (p : Inputs) := adcSpec ((v11838f p).2.CF) ((v118370 p).1 : BitVec 64) ((v11835a p).2)

def v118395 (p : Inputs) := adcSpec ((v118392 p).2.CF) ((v118386 p).1 : BitVec 64) ((v118370 p).2)

def v118398 (p : Inputs) := adcSpec ((v118395 p).2.CF) ((v118386 p).2 : BitVec 64) (p.low[3])

def v1183a5 (p : Inputs) := adcSpec ((v118398 p).2.CF) (p.high[0] : BitVec 64) (0)

def v1183b6 (p : Inputs) := mulResult (p.high[0]) (85565669623438334)

def v1183bf (p : Inputs) := ((v11838f p).1 : BitVec 64) &&& (18446744073709551614)

def v1183c6 (p : Inputs) := mulResult (p.high[0]) (4834901528447446049)

def v1183cf (p : Inputs) := addSpec ((v1183c6 p).1 : BitVec 64) ((v118392 p).1)

def v1183d2 (p : Inputs) := adcSpec ((v1183cf p).2.CF) ((v1183c6 p).2 : BitVec 64) (0)

def v1183d6 (p : Inputs) := addSpec ((v1183b6 p).1 : BitVec 64) (v1183bf p)

def v1183d9 (p : Inputs) := adcSpec ((v1183d6 p).2.CF) ((v1183cf p).1 : BitVec 64) ((v1183b6 p).2)

def v1183dc (p : Inputs) := adcSpec ((v1183d9 p).2.CF) ((v1183d2 p).1 : BitVec 64) (0)

def v1183e8 (p : Inputs) := mulResult (p.high[0]) (18446744069414584319)

def v1183f1 (p : Inputs) := addSpec ((v1183e8 p).1 : BitVec 64) ((v118395 p).1)

def v1183f4 (p : Inputs) := adcSpec ((v1183f1 p).2.CF) ((v1183e8 p).2 : BitVec 64) (0)

def v1183f8 (p : Inputs) := addSpec ((v1183f1 p).1 : BitVec 64) ((v1183dc p).1)

def v1183fb (p : Inputs) := adcSpec ((v1183f8 p).2.CF) ((v1183f4 p).1 : BitVec 64) (0)

def v118407 (p : Inputs) := mulResult (p.high[0]) ((4294967295 : BitVec 32).setWidth 64)

def v118410 (p : Inputs) := addSpec ((v118407 p).1 : BitVec 64) ((v118398 p).1)

def v118413 (p : Inputs) := adcSpec ((v118410 p).2.CF) ((v118407 p).2 : BitVec 64) (0)

def v118423 (p : Inputs) := mulResult (p.high[1]) (85565669623438334)

def v11842c (p : Inputs) := ((v1183d9 p).1 : BitVec 64) &&& (18446744073709551614)

def v11843d (p : Inputs) := mulResult (p.high[1]) (4834901528447446049)

def v118446 (p : Inputs) := addSpec ((v11843d p).1 : BitVec 64) ((v1183f8 p).1)

def v118449 (p : Inputs) := adcSpec ((v118446 p).2.CF) ((v11843d p).2 : BitVec 64) (0)

def v11844d (p : Inputs) := addSpec ((v118423 p).1 : BitVec 64) (v11842c p)

def v118450 (p : Inputs) := adcSpec ((v11844d p).2.CF) ((v118446 p).1 : BitVec 64) ((v118423 p).2)

def v118453 (p : Inputs) := adcSpec ((v118450 p).2.CF) ((v118449 p).1 : BitVec 64) (0)

def v118464 (p : Inputs) := mulResult (p.high[1]) (18446744069414584319)

def v11846a (p : Inputs) := addSpec ((v118410 p).1 : BitVec 64) ((v1183fb p).1)

def v11846d (p : Inputs) := adcSpec ((v11846a p).2.CF) ((v118413 p).1 : BitVec 64) ((v1183a5 p).1)

def v118477 (p : Inputs) := adcSpec ((v11846d p).2.CF) ((((if (v1183a5 p).2.CF then 1 else 0 : BitVec 8)).setWidth 32 : BitVec 32).setWidth 64 : BitVec 64) (p.high[1])

def v11847f (p : Inputs) := addSpec ((v11846a p).1 : BitVec 64) ((v118464 p).1)

def v118482 (p : Inputs) := adcSpec ((v11847f p).2.CF) ((v118464 p).2 : BitVec 64) (0)

def v118486 (p : Inputs) := addSpec ((v11847f p).1 : BitVec 64) ((v118453 p).1)

def v118489 (p : Inputs) := adcSpec ((v118486 p).2.CF) ((v118482 p).1 : BitVec 64) (0)

def v118495 (p : Inputs) := mulResult (p.high[1]) ((4294967295 : BitVec 32).setWidth 64)

def v11849e (p : Inputs) := addSpec ((v118495 p).1 : BitVec 64) ((v11846d p).1)

def v1184a1 (p : Inputs) := adcSpec ((v11849e p).2.CF) ((v118495 p).2 : BitVec 64) (0)

def v1184b6 (p : Inputs) := mulResult (p.high[2]) (85565669623438334)

def v1184bf (p : Inputs) := ((v118450 p).1 : BitVec 64) &&& (18446744073709551614)

def v1184d0 (p : Inputs) := mulResult (p.high[2]) (4834901528447446049)

def v1184d9 (p : Inputs) := addSpec ((v1184d0 p).1 : BitVec 64) ((v118486 p).1)

def v1184dc (p : Inputs) := adcSpec ((v1184d9 p).2.CF) ((v1184d0 p).2 : BitVec 64) (0)

def v1184e0 (p : Inputs) := addSpec ((v1184b6 p).1 : BitVec 64) (v1184bf p)

def v1184e3 (p : Inputs) := adcSpec ((v1184e0 p).2.CF) ((v1184d9 p).1 : BitVec 64) ((v1184b6 p).2)

def v1184e6 (p : Inputs) := adcSpec ((v1184e3 p).2.CF) ((v1184dc p).1 : BitVec 64) (0)

def v1184f7 (p : Inputs) := mulResult (p.high[2]) (18446744069414584319)

def v118500 (p : Inputs) := addSpec ((v11849e p).1 : BitVec 64) ((v118489 p).1)

def v118503 (p : Inputs) := adcSpec ((v118500 p).2.CF) ((v1184a1 p).1 : BitVec 64) ((v118477 p).1)

def v11850c (p : Inputs) := adcSpec ((v118503 p).2.CF) ((((if (v118477 p).2.CF then 1 else 0 : BitVec 8)).setWidth 32 : BitVec 32).setWidth 64 : BitVec 64) (p.high[2])

def v118512 (p : Inputs) := addSpec ((v1184f7 p).1 : BitVec 64) ((v118500 p).1)

def v118515 (p : Inputs) := adcSpec ((v118512 p).2.CF) ((v1184f7 p).2 : BitVec 64) (0)

def v118519 (p : Inputs) := addSpec ((v118512 p).1 : BitVec 64) ((v1184e6 p).1)

def v11851c (p : Inputs) := adcSpec ((v118519 p).2.CF) ((v118515 p).1 : BitVec 64) (0)

def v118528 (p : Inputs) := mulResult (p.high[2]) ((4294967295 : BitVec 32).setWidth 64)

def v118531 (p : Inputs) := addSpec ((v118528 p).1 : BitVec 64) ((v118503 p).1)

def v118534 (p : Inputs) := adcSpec ((v118531 p).2.CF) ((v118528 p).2 : BitVec 64) (0)

def v11854e (p : Inputs) := mulResult (p.high[3]) (85565669623438334)

def v118557 (p : Inputs) := ((v1184e3 p).1 : BitVec 64) &&& (18446744073709551614)

def v118568 (p : Inputs) := mulResult (p.high[3]) (4834901528447446049)

def v118571 (p : Inputs) := addSpec ((v118568 p).1 : BitVec 64) ((v118519 p).1)

def v118574 (p : Inputs) := adcSpec ((v118571 p).2.CF) ((v118568 p).2 : BitVec 64) (0)

def v118578 (p : Inputs) := addSpec ((v11854e p).1 : BitVec 64) (v118557 p)

def v11857b (p : Inputs) := adcSpec ((v118578 p).2.CF) ((v118571 p).1 : BitVec 64) ((v11854e p).2)

def v11857e (p : Inputs) := adcSpec ((v11857b p).2.CF) ((v118574 p).1 : BitVec 64) (0)

def v11858f (p : Inputs) := mulResult (p.high[3]) (18446744069414584319)

def v118598 (p : Inputs) := addSpec ((v118531 p).1 : BitVec 64) ((v11851c p).1)

def v11859e (p : Inputs) := adcSpec ((v118598 p).2.CF) ((v118534 p).1 : BitVec 64) ((v11850c p).1)

def v1185a1 (p : Inputs) := adcSpec ((v11859e p).2.CF) ((((mergeGPR 8 ((if (v11850c p).2.CF then 1 else 0 : BitVec 8)) ((v118477 p).1)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64 : BitVec 64) (p.high[3])

def v1185a8 (p : Inputs) := addSpec ((v11858f p).1 : BitVec 64) ((v118598 p).1)

def v1185ab (p : Inputs) := adcSpec ((v1185a8 p).2.CF) ((v11858f p).2 : BitVec 64) (0)

def v1185af (p : Inputs) := addSpec ((v1185a8 p).1 : BitVec 64) ((v11857e p).1)

def v1185b2 (p : Inputs) := adcSpec ((v1185af p).2.CF) ((v1185ab p).1 : BitVec 64) (0)

def v1185be (p : Inputs) := mulResult (p.high[3]) ((4294967295 : BitVec 32).setWidth 64)

def v1185c4 (p : Inputs) := addSpec ((v1185be p).1 : BitVec 64) ((v11859e p).1)

def v1185c7 (p : Inputs) := adcSpec ((v1185c4 p).2.CF) ((v1185be p).2 : BitVec 64) (0)

def v1185cb (p : Inputs) := addSpec ((v1185c4 p).1 : BitVec 64) ((v1185b2 p).1)

def v1185d2 (p : Inputs) := adcSpec ((v1185cb p).2.CF) ((v1185a1 p).1 : BitVec 64) ((v1185c7 p).1)

def v1185d5 (p : Inputs) := adcSpec ((v1185d2 p).2.CF) ((((mergeGPR 8 ((if (v1185a1 p).2.CF then 1 else 0 : BitVec 8)) ((v11850c p).1)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64 : BitVec 64) (0)

def v1185e6 (p : Inputs) := mulResult ((v11857b p).1) (17562291160714782033)

def v118600 (p : Inputs) := mulResult ((v11857b p).1) (13611842547513532036)

def v118615 (p : Inputs) := mulResult ((v11857b p).1) (18446744073709551615)

def v118623 (p : Inputs) := ((v1185af p).1 : BitVec 64) <<< 32

def v11862a (p : Inputs) := ((v1185d2 p).1 : BitVec 64) * (13611842547513532036)

def v11862e (p : Inputs) := addSpec (v118623 p : BitVec 64) ((v1185cb p).1)

def v118631 (p : Inputs) := (v11862a p : BitVec 64) - ((v11862e p).1)

def v118641 (p : Inputs) := mulResult ((v11857b p).1) (18446744069414584320)

def v11864a (p : Inputs) := ((v1185d5 p).1 : BitVec 64) * (17562291160714782033)

def v11864e (p : Inputs) := addSpec (v118631 p : BitVec 64) (v11864a p)

def v118654 (p : Inputs) := mulResult ((v1185af p).1) (17562291160714782033)

def v11866a (p : Inputs) := mulResult ((v1185af p).1) (13611842547513532036)

def v118670 (p : Inputs) := addSpec ((v118600 p).1 : BitVec 64) ((v1185e6 p).2)

def v118675 (p : Inputs) := adcSpec ((v118670 p).2.CF) ((v118615 p).1 : BitVec 64) ((v118600 p).2)

def v11867a (p : Inputs) := adcSpec ((v118675 p).2.CF) ((v118641 p).1 : BitVec 64) ((v118615 p).2)

def v11867f (p : Inputs) := adcSpec ((v11867a p).2.CF) ((v11864e p).1 : BitVec 64) ((v118641 p).2)

def v118682 (p : Inputs) := addSpec ((v118675 p).1 : BitVec 64) ((v11866a p).1)

def v118685 (p : Inputs) := adcSpec ((v118682 p).2.CF) ((v11866a p).2 : BitVec 64) (0)

def v118689 (p : Inputs) := addSpec ((v118670 p).1 : BitVec 64) ((v118654 p).1)

def v11868c (p : Inputs) := adcSpec ((v118689 p).2.CF) ((v118682 p).1 : BitVec 64) ((v118654 p).2)

def v11868f (p : Inputs) := adcSpec ((v11868c p).2.CF) ((v118685 p).1 : BitVec 64) (0)

def v11869d (p : Inputs) := mulResult ((v1185af p).1) (18446744073709551615)

def v1186a6 (p : Inputs) := addSpec ((v11869d p).1 : BitVec 64) ((v11867a p).1)

def v1186a9 (p : Inputs) := adcSpec ((v1186a6 p).2.CF) ((v11869d p).2 : BitVec 64) (0)

def v1186b0 (p : Inputs) := mulResult ((v1185cb p).1) (17562291160714782033)

def v1186c6 (p : Inputs) := mulResult ((v1185cb p).1) (13611842547513532036)

def v1186cc (p : Inputs) := addSpec ((v1186a6 p).1 : BitVec 64) ((v11868f p).1)

def v1186cf (p : Inputs) := adcSpec ((v1186cc p).2.CF) ((v1186a9 p).1 : BitVec 64) ((v11867f p).1)

def v1186d2 (p : Inputs) := addSpec ((v1186cc p).1 : BitVec 64) ((v1186c6 p).1)

def v1186d5 (p : Inputs) := adcSpec ((v1186d2 p).2.CF) ((v1186c6 p).2 : BitVec 64) (0)

def v1186dc (p : Inputs) := mulResult ((v1185d2 p).1) (17562291160714782033)

def v1186e2 (p : Inputs) := addSpec ((v1186b0 p).1 : BitVec 64) ((v11868c p).1)

def v1186e5 (p : Inputs) := adcSpec ((v1186e2 p).2.CF) ((v1186d2 p).1 : BitVec 64) ((v1186b0 p).2)

def v1186e8 (p : Inputs) := adcSpec ((v1186e5 p).2.CF) ((v1186d5 p).1 : BitVec 64) ((v1186cf p).1)

def v1186f3 (p : Inputs) := addSpec ((v1186e5 p).1 : BitVec 64) ((v1186dc p).1)

def v1186f6 (p : Inputs) := adcSpec ((v1186f3 p).2.CF) ((v1186e8 p).1 : BitVec 64) ((v1186dc p).2)

def v118701 (p : Inputs) := (p.low[0] : BitVec 64) - ((v1185e6 p).1)

def v118704 (p : Inputs) := ~~~(p.low[0] : BitVec 64)

def v11870a (p : Inputs) := ((v1185e6 p).1 : BitVec 64) &&& (v118704 p)

def v11870d (p : Inputs) := (v118704 p : BitVec 64) ||| ((v1185e6 p).1)

def v118718 (p : Inputs) := (v11870d p : BitVec 64) &&& (v118701 p)

def v11871b (p : Inputs) := (v118718 p : BitVec 64) ||| (v11870a p)

def v11871e (p : Inputs) := (v11871b p : BitVec 64) >>> 63

def v11872b (p : Inputs) := (((0 : BitVec 32) : BitVec 32).setWidth 64 : BitVec 64) - (v11871e p)

def v118732 (p : Inputs) := (p.low[1] : BitVec 64) - ((v118689 p).1)

def v118735 (p : Inputs) := (v11872b p : BitVec 64).sshiftRight 63

def v118739 (p : Inputs) := addSpec (v118735 p : BitVec 64) (v118732 p)

def v11873c (p : Inputs) := ~~~(p.low[1] : BitVec 64)

def v118742 (p : Inputs) := ((v118689 p).1 : BitVec 64) &&& (v11873c p)

def v118745 (p : Inputs) := (v11873c p : BitVec 64) ||| ((v118689 p).1)

def v118748 (p : Inputs) := (v118745 p : BitVec 64) &&& ((v118739 p).1)

def v11874b (p : Inputs) := (v118748 p : BitVec 64) ||| (v118742 p)

def v11874e (p : Inputs) := (v11874b p : BitVec 64) >>> 63

def v11875b (p : Inputs) := (((0 : BitVec 32) : BitVec 32).setWidth 64 : BitVec 64) - (v11874e p)

def v118762 (p : Inputs) := (p.low[2] : BitVec 64) - ((v1186e2 p).1)

def v118765 (p : Inputs) := (v11875b p : BitVec 64).sshiftRight 63

def v118769 (p : Inputs) := addSpec (v118765 p : BitVec 64) (v118762 p)

def v11876c (p : Inputs) := ~~~(p.low[2] : BitVec 64)

def v118772 (p : Inputs) := ((v1186e2 p).1 : BitVec 64) &&& (v11876c p)

def v118775 (p : Inputs) := (v11876c p : BitVec 64) ||| ((v1186e2 p).1)

def v118778 (p : Inputs) := (v118775 p : BitVec 64) &&& ((v118769 p).1)

def v11877b (p : Inputs) := (v118778 p : BitVec 64) ||| (v118772 p)

def v11877e (p : Inputs) := (v11877b p : BitVec 64) >>> 63

def v11878c (p : Inputs) := (((0 : BitVec 32) : BitVec 32).setWidth 64 : BitVec 64) - (v11877e p)

def v118798 (p : Inputs) := (p.low[3] : BitVec 64) - ((v1186f3 p).1)

def v11879b (p : Inputs) := (v11878c p : BitVec 64).sshiftRight 63

def v11879f (p : Inputs) := addSpec (v11879b p : BitVec 64) (v118798 p)

def v1187a2 (p : Inputs) := ~~~(p.low[3] : BitVec 64)

def v1187a8 (p : Inputs) := ((v1186f3 p).1 : BitVec 64) &&& (v1187a2 p)

def v1187ab (p : Inputs) := (v1187a2 p : BitVec 64) ||| ((v1186f3 p).1)

def v1187ae (p : Inputs) := (v1187ab p : BitVec 64) &&& ((v11879f p).1)

def v1187b1 (p : Inputs) := (v1187ae p : BitVec 64) ||| (v1187a8 p)

def v1187b4 (p : Inputs) := (v1187b1 p : BitVec 64) >>> 63

def v1187c1 (p : Inputs) := (((0 : BitVec 32) : BitVec 32).setWidth 64 : BitVec 64) - (v1187b4 p)

def v1187cd (p : Inputs) := (p.high[0] : BitVec 64) - ((v1186f6 p).1)

def v1187d0 (p : Inputs) := (v1187c1 p : BitVec 64).sshiftRight 63

def v1187d4 (p : Inputs) := addSpec (v1187d0 p : BitVec 64) (v1187cd p)

def v1187d7 (p : Inputs) := ~~~(p.high[0] : BitVec 64)

def v1187dd (p : Inputs) := ((v1186f6 p).1 : BitVec 64) &&& (v1187d7 p)

def v1187e0 (p : Inputs) := (v1187d7 p : BitVec 64) ||| ((v1186f6 p).1)

def v1187e3 (p : Inputs) := (v1187e0 p : BitVec 64) &&& ((v1187d4 p).1)

def v1187e6 (p : Inputs) := (v1187e3 p : BitVec 64) ||| (v1187dd p)

def v1187e9 (p : Inputs) := (v1187e6 p : BitVec 64) >>> 63

def v1187fe (p : Inputs) := addSpec (884452912994769583 : BitVec 64) (v118701 p)

def v118801 (p : Inputs) := ~~~(v118701 p : BitVec 64)

def v118804 (p : Inputs) := (v118801 p : BitVec 64) ||| ((v1187fe p).1)

def v118807 (p : Inputs) := (v118804 p : BitVec 64) >>> 63

def v118815 (p : Inputs) := (((0 : BitVec 32) : BitVec 32).setWidth 64 : BitVec 64) - (v118807 p)

def v118819 (p : Inputs) := (v118815 p : BitVec 64).sshiftRight 63

def v118827 (p : Inputs) := addSpec (4834901526196019580 : BitVec 64) (v118819 p)

def v11882a (p : Inputs) := addSpec ((v118827 p).1 : BitVec 64) ((v118739 p).1)

def v11882d (p : Inputs) := ~~~((v118739 p).1 : BitVec 64)

def v118830 (p : Inputs) := (v11882d p : BitVec 64) ||| ((v11882a p).1)

def v118833 (p : Inputs) := (v118830 p : BitVec 64) >>> 63

def v118842 (p : Inputs) := (v118833 p : BitVec 64) - 1

def v118845 (p : Inputs) := (v118842 p : BitVec 64) >>> 63

def v118849 (p : Inputs) := addSpec (v118845 p : BitVec 64) ((v118769 p).1)

def v11884c (p : Inputs) := ~~~((v118769 p).1 : BitVec 64)

def v11884f (p : Inputs) := (v11884c p : BitVec 64) ||| ((v118849 p).1)

def v118852 (p : Inputs) := (v11884f p : BitVec 64) >>> 63

def v118860 (p : Inputs) := (((0 : BitVec 32) : BitVec 32).setWidth 64 : BitVec 64) - (v118852 p)

def v118864 (p : Inputs) := (v118860 p : BitVec 64).sshiftRight 63

def v118872 (p : Inputs) := addSpec (4294967296 : BitVec 64) (v118864 p)

def v118875 (p : Inputs) := addSpec ((v118872 p).1 : BitVec 64) ((v11879f p).1)

def v118878 (p : Inputs) := ~~~((v11879f p).1 : BitVec 64)

def v11887b (p : Inputs) := (v118878 p : BitVec 64) ||| ((v118875 p).1)

def v11887e (p : Inputs) := (v11887b p : BitVec 64) >>> 63

def v11888c (p : Inputs) := (((0 : BitVec 32) : BitVec 32).setWidth 64 : BitVec 64) - (v11887e p)

def v118890 (p : Inputs) := (v11888c p : BitVec 64).sshiftRight 63

def v118894 (p : Inputs) := addSpec (v118890 p : BitVec 64) ((v1187d4 p).1)

def v118897 (p : Inputs) := ~~~((v1187d4 p).1 : BitVec 64)

def v11889a (p : Inputs) := (v118897 p : BitVec 64) &&& ((v118894 p).1)

def v11889d (p : Inputs) := (v11889a p : BitVec 64) >>> 63

def v1188af (p : Inputs) := ((v118849 p).1 : BitVec 64) - (v11889d p)

def v1188b2 (p : Inputs) := -(v11889d p : BitVec 64)

def v1188b5 (p : Inputs) := (17562291160714782033 : BitVec 64) &&& (v1188b2 p)

def v1188c2 (p : Inputs) := (13611842547513532036 : BitVec 64) &&& (v1188b2 p)

def v1188c5 (p : Inputs) := addSpec (v1188b5 p : BitVec 64) ((v1187fe p).1)

def v1188c8 (p : Inputs) := adcSpec ((v1188c5 p).2.CF) (v1188c2 p : BitVec 64) ((v11882a p).1)

def v1188ce (p : Inputs) := adcSpec ((v1188c8 p).2.CF) (v1188af p : BitVec 64) (0)

def v1188dc (p : Inputs) := (18446744069414584320 : BitVec 64) &&& (v1188b2 p)

def v1188df (p : Inputs) := addSpec ((mergeGPR 8 ((if (v1188c8 p).2.CF then 1 else 0 : BitVec 8)) ((v11882a p).1)).setWidth 8 : BitVec 8) (255)

def v1188e1 (p : Inputs) := adcSpec ((v1188df p).2.CF) (v1188b2 p : BitVec 64) ((v118849 p).1)

def v1188e4 (p : Inputs) := adcSpec ((v1188e1 p).2.CF) (v1188dc p : BitVec 64) ((v118875 p).1)

def reducedWords (p : Inputs) : Vector (BitVec 64) 4 :=
  #v[(v1188c5 p).1, (v1188c8 p).1, (v1188ce p).1, (v1188e4 p).1]

abbrev resultWords := reducedWords

end P256.Proofs.Scalar.Multiply.Barrett
