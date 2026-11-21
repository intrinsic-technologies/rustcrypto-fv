import K256.Proofs.Common.Tactic
import K256.Proofs.Common.Invert.LinearCombination
import K256.Proofs.Generate.Generator.Affine.Invert.Core.Callee

namespace K256.Proofs.Generate.Generator.Affine.Invert.Core.LinearCombination
open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
open K256.Proofs.Common.Invert.LinearCombination
open K256.Proofs.Sec1.Affine.Uncompressed

structure Controls (a : Registers) {n : Nat} (b : Values Value n) (size : 51 < n) : Prop where
  r22 : b[22]'(by omega) = a[22]
  r39 : b[39]'(by omega) = a[39]
  r50 : b[50]'(by omega) = a[50]
  r51 : b[51]'(by omega) = a[51]

structure Saved (a : Registers) (m : Ram) (sp ret : BitVec 64) : Prop where
  msp0_64 : memLoad m sp 64 = ret
  msp8_64 : memLoad m (sp - 8) 64 = a[5].get 64
  msp16_64 : memLoad m (sp - 16) 64 = a[15].get 64
  msp24_64 : memLoad m (sp - 24) 64 = a[14].get 64
  msp32_64 : memLoad m (sp - 32) 64 = a[13].get 64
  msp40_64 : memLoad m (sp - 40) 64 = a[12].get 64
  msp48_64 : memLoad m (sp - 48) 64 = a[3].get 64

def rightProductSign (p : Inputs) : BitVec 64 :=
  (mergeGPR 8 (v108857 p) ((mergeGPR 8 (v1085e6 p) (v10851c p))))

def negateOperand (p : Inputs) : BitVec 64 :=
  ((((mergeGPR 8 (v1085fa p) ((mergeGPR 8 (v1085f2 p) ((((mergeGPR 8 (v1085e6 p) (v10851c p))).setWidth 32).setWidth 64))))).setWidth 8).setWidth 32).setWidth 64

def selectMagnitude (p : Inputs) : BitVec 64 :=
  ((if decide ((v108793 p) = 0) then ((0 : BitVec 32).setWidth 64).setWidth 32 else (((((mergeGPR 8 (v1087a3 p) (((((mergeGPR 8 (v1085f2 p) ((((mergeGPR 8 (v1085e6 p) (v10851c p))).setWidth 32).setWidth 64))).setWidth 8).setWidth 32).setWidth 64))).setWidth 8).setWidth 32).setWidth 64).setWidth 32)).setWidth 64

structure At1084e0 (a : Registers) (sp dst ret left right : BitVec 64) (p : Inputs) (b : Values Value 53) (m : Ram) : Prop extends Controls a b (by decide) where
  r1 : b[1].get 64 = p.u
  r2 : b[2].get 64 = right
  r3 : b[3].get 64 = a[3].get 64
  r4 : b[4].get 64 = sp
  r5 : b[5].get 64 = a[5].get 64
  r6 : b[6].get 64 = left
  r7 : b[7].get 64 = dst
  r8 : b[8].get 64 = p.v
  r12 : b[12].get 64 = a[12].get 64
  r13 : b[13].get 64 = a[13].get 64
  r14 : b[14].get 64 = a[14].get 64
  r15 : b[15].get 64 = a[15].get 64
  mleft0_64 : memLoad m left 64 = p.a[0]
  mleft8_64 : memLoad m (left + 8) 64 = p.a[1]
  mleft16_64 : memLoad m (left + 16) 64 = p.a[2]
  mleft24_64 : memLoad m (left + 24) 64 = p.a[3]
  mright0_64 : memLoad m right 64 = p.b[0]
  mright8_64 : memLoad m (right + 8) 64 = p.b[1]
  mright16_64 : memLoad m (right + 16) 64 = p.b[2]
  mleft32_8 : memLoad m (left + 32) 8 = p.aSign
  mright24_64 : memLoad m (right + 24) 64 = p.b[3]
  mright32_8 : memLoad m (right + 32) 8 = p.bSign
  msp0_64 : memLoad m sp 64 = ret

structure At108519 (a : Registers) (sp dst ret left right : BitVec 64) (p : Inputs) (b : Values Value 90) (m : Ram) : Prop extends Controls a b (by decide), Saved a m sp ret where
  r6 : b[6].get 64 = left
  r7 : b[7].get 64 = dst
  r8 : b[8].get 64 = p.v
  r65 : b[65].get 64 = sp - 112
  r67 : b[67].get 64 = right
  r88 : b[88].get 64 = v108516 p
  mleft0_64 : memLoad m left 64 = p.a[0]
  mleft8_64 : memLoad m (left + 8) 64 = p.a[1]
  mleft16_64 : memLoad m (left + 16) 64 = p.a[2]
  mleft24_64 : memLoad m (left + 24) 64 = p.a[3]
  mright0_64 : memLoad m right 64 = p.b[0]
  mright8_64 : memLoad m (right + 8) 64 = p.b[1]
  mright16_64 : memLoad m (right + 16) 64 = p.b[2]
  msp80_64 : memLoad m (sp - 80) 64 = v1084f4 p
  mleft32_8 : memLoad m (left + 32) 8 = p.aSign
  mright24_64 : memLoad m (right + 24) 64 = p.b[3]
  mright32_8 : memLoad m (right + 32) 8 = p.bSign

structure At10855c (a : Registers) (sp dst ret left right : BitVec 64) (p : Inputs) (b : Values Value 130) (m : Ram) : Prop extends Controls a b (by decide), Saved a m sp ret where
  r6 : b[6].get 64 = left
  r7 : b[7].get 64 = dst
  r8 : b[8].get 64 = p.v
  r65 : b[65].get 64 = sp - 112
  r67 : b[67].get 64 = right
  r88 : b[88].get 64 = v108516 p
  r102 : b[102].get 64 = (v10852e p).1
  r104 : b[104].get 64 = (v10852e p).2
  r115 : b[115].get 64 = (v108540 p).1
  r117 : b[117].get 64 = (v108540 p).2
  r119 : b[119].get 64 = (((v10851c p).setWidth 8).setWidth 32).setWidth 64
  r121 : b[121].get 64 = v10854f p
  r126 : b[126].get 64 = (v108555 p).2
  r128 : b[128].get 64 = (v108555 p).1
  mleft24_64 : memLoad m (left + 24) 64 = p.a[3]
  mright0_64 : memLoad m right 64 = p.b[0]
  mright8_64 : memLoad m (right + 8) 64 = p.b[1]
  mright16_64 : memLoad m (right + 16) 64 = p.b[2]
  msp80_64 : memLoad m (sp - 80) 64 = v1084f4 p
  mleft32_8 : memLoad m (left + 32) 8 = p.aSign
  mright24_64 : memLoad m (right + 24) 64 = p.b[3]
  msp88_64 : memLoad m (sp - 88) 64 = v10851c p
  mright32_8 : memLoad m (right + 32) 8 = p.bSign

structure At1085a1 (a : Registers) (sp dst ret left right : BitVec 64) (p : Inputs) (b : Values Value 173) (m : Ram) : Prop extends Controls a b (by decide), Saved a m sp ret where
  r6 : b[6].get 64 = left
  r7 : b[7].get 64 = dst
  r65 : b[65].get 64 = sp - 112
  r67 : b[67].get 64 = right
  r102 : b[102].get 64 = (v10852e p).1
  r145 : b[145].get 64 = v108572 p
  r147 : b[147].get 64 = (v108575 p).1
  r150 : b[150].get 64 = (v108578 p).1
  r153 : b[153].get 64 = (v10857b p).1
  r156 : b[156].get 64 = (v10857e p).1
  r171 : b[171].get 64 = (v108595 p).1
  mright16_64 : memLoad m (right + 16) 64 = p.b[2]
  msp80_64 : memLoad m (sp - 80) 64 = v1084f4 p
  mleft32_8 : memLoad m (left + 32) 8 = p.aSign
  mright24_64 : memLoad m (right + 24) 64 = p.b[3]
  msp96_64 : memLoad m (sp - 96) 64 = (v108585 p).2
  msp104_64 : memLoad m (sp - 104) 64 = (v108595 p).2
  msp88_64 : memLoad m (sp - 88) 64 = v10851c p
  mright32_8 : memLoad m (right + 32) 8 = p.bSign
  msp72_64 : memLoad m (sp - 72) 64 = (v108585 p).1

structure At1085f2 (a : Registers) (sp dst ret left right : BitVec 64) (p : Inputs) (b : Values Value 214) (m : Ram) : Prop extends Controls a b (by decide), Saved a m sp ret where
  r7 : b[7].get 64 = dst
  r65 : b[65].get 64 = sp - 112
  r102 : b[102].get 64 = (v10852e p).1
  r147 : b[147].get 64 = (v108575 p).1
  r150 : b[150].get 64 = (v108578 p).1
  r153 : b[153].get 64 = (v10857b p).1
  r156 : b[156].get 64 = (v10857e p).1
  r184 : b[184].get 64 = (mergeGPR 8 (v1085b3 p) (v1084f4 p))
  r192 : b[192].get 64 = (v1085c3 p).1
  r198 : b[198].get 64 = (v1085c8 p).1
  r201 : b[201].get 64 = (v1085d5 p).1
  r212 : b[212].get 64 = (((mergeGPR 8 (v1085e6 p) (v10851c p))).setWidth 32).setWidth 64
  msp72_64 : memLoad m (sp - 72) 64 = (v108585 p).1
  msp64_64 : memLoad m (sp - 64) 64 = (v1085c8 p).1
  msp104_64 : memLoad m (sp - 104) 64 = (v1085d8 p).1
  msp88_64 : memLoad m (sp - 88) 64 = (mergeGPR 8 (v1085e6 p) (v10851c p))
  msp80_8 : memLoad m (sp - 80) 8 = ((mergeGPR 8 (v1085b3 p) (v1084f4 p))).setWidth 8

structure At108640 (a : Registers) (sp dst ret left right : BitVec 64) (p : Inputs) (b : Values Value 252) (m : Ram) : Prop extends Controls a b (by decide), Saved a m sp ret where
  r7 : b[7].get 64 = dst
  r65 : b[65].get 64 = sp - 112
  r102 : b[102].get 64 = (v10852e p).1
  r147 : b[147].get 64 = (v108575 p).1
  r150 : b[150].get 64 = (v108578 p).1
  r153 : b[153].get 64 = (v10857b p).1
  r156 : b[156].get 64 = (v10857e p).1
  r192 : b[192].get 64 = (v1085c3 p).1
  r201 : b[201].get 64 = (v1085d5 p).1
  r217 : b[217].get 64 = (mergeGPR 8 (v1085fa p) ((mergeGPR 8 (v1085f2 p) ((((mergeGPR 8 (v1085e6 p) (v10851c p))).setWidth 32).setWidth 64))))
  r219 : b[219].get 64 = (v108585 p).1
  r228 : b[228].get 64 = (v10860e p).1
  r233 : b[233].get 64 = (v108617 p).1
  r238 : b[238].get 64 = (v10861f p).1
  r248 : b[248].get 64 = v108639 p
  r250 : b[250].get 64 = negateOperand p
  msp64_64 : memLoad m (sp - 64) 64 = (v1085c8 p).1
  msp56_64 : memLoad m (sp - 56) 64 = (((if !((v10861f p).2.CF) then 1 else 0 : BitVec 8)).setWidth 32).setWidth 64
  msp104_64 : memLoad m (sp - 104) 64 = (v1085d8 p).1
  msp96_8 : memLoad m (sp - 96) 8 = ((mergeGPR 8 (v1085f2 p) ((((mergeGPR 8 (v1085e6 p) (v10851c p))).setWidth 32).setWidth 64))).setWidth 8
  msp88_64 : memLoad m (sp - 88) 64 = (mergeGPR 8 (v1085e6 p) (v10851c p))
  msp80_8 : memLoad m (sp - 80) 8 = ((mergeGPR 8 (v1085b3 p) (v1084f4 p))).setWidth 8

structure At108684 (a : Registers) (sp dst ret left right : BitVec 64) (p : Inputs) (b : Values Value 288) (m : Ram) : Prop extends Controls a b (by decide), Saved a m sp ret where
  r7 : b[7].get 64 = dst
  r65 : b[65].get 64 = sp - 112
  r102 : b[102].get 64 = (v10852e p).1
  r147 : b[147].get 64 = (v108575 p).1
  r150 : b[150].get 64 = (v108578 p).1
  r153 : b[153].get 64 = (v10857b p).1
  r156 : b[156].get 64 = (v10857e p).1
  r201 : b[201].get 64 = (v1085d5 p).1
  r217 : b[217].get 64 = (mergeGPR 8 (v1085fa p) ((mergeGPR 8 (v1085f2 p) ((((mergeGPR 8 (v1085e6 p) (v10851c p))).setWidth 32).setWidth 64))))
  r256 : b[256].get 64 = v108646 p
  r269 : b[269].get 64 = v10865e p
  r275 : b[275].get 64 = v10866d p
  r283 : b[283].get 64 = v10867a p
  r286 : b[286].get 64 = v108681 p
  msp112_8 : memLoad m (sp - 112) 8 = ((mergeGPR 8 (v1085fa p) ((mergeGPR 8 (v1085f2 p) ((((mergeGPR 8 (v1085e6 p) (v10851c p))).setWidth 32).setWidth 64))))).setWidth 8
  msp56_64 : memLoad m (sp - 56) 64 = (((if !((v10861f p).2.CF) then 1 else 0 : BitVec 8)).setWidth 32).setWidth 64
  msp104_64 : memLoad m (sp - 104) 64 = (v1085d8 p).1
  msp96_8 : memLoad m (sp - 96) 8 = ((mergeGPR 8 (v1085f2 p) ((((mergeGPR 8 (v1085e6 p) (v10851c p))).setWidth 32).setWidth 64))).setWidth 8
  msp88_64 : memLoad m (sp - 88) 64 = (mergeGPR 8 (v1085e6 p) (v10851c p))
  msp80_8 : memLoad m (sp - 80) 8 = ((mergeGPR 8 (v1085b3 p) (v1084f4 p))).setWidth 8

structure At1086c8 (a : Registers) (sp dst ret left right : BitVec 64) (p : Inputs) (b : Values Value 324) (m : Ram) : Prop extends Controls a b (by decide), Saved a m sp ret where
  r7 : b[7].get 64 = dst
  r65 : b[65].get 64 = sp - 112
  r147 : b[147].get 64 = (v108575 p).1
  r150 : b[150].get 64 = (v108578 p).1
  r153 : b[153].get 64 = (v10857b p).1
  r156 : b[156].get 64 = (v10857e p).1
  r269 : b[269].get 64 = v10865e p
  r283 : b[283].get 64 = v10867a p
  r294 : b[294].get 64 = v10868f p
  r300 : b[300].get 64 = v10869c p
  r314 : b[314].get 64 = v1086b1 p
  r316 : b[316].get 64 = negateOperand p
  r322 : b[322].get 64 = v1086c4 p
  msp56_64 : memLoad m (sp - 56) 64 = (((if !((v10861f p).2.CF) then 1 else 0 : BitVec 8)).setWidth 32).setWidth 64
  msp104_64 : memLoad m (sp - 104) 64 = (v1085d8 p).1
  msp96_8 : memLoad m (sp - 96) 8 = ((mergeGPR 8 (v1085f2 p) ((((mergeGPR 8 (v1085e6 p) (v10851c p))).setWidth 32).setWidth 64))).setWidth 8
  msp88_64 : memLoad m (sp - 88) 64 = (mergeGPR 8 (v1085e6 p) (v10851c p))
  msp80_8 : memLoad m (sp - 80) 8 = ((mergeGPR 8 (v1085b3 p) (v1084f4 p))).setWidth 8

structure At108709 (a : Registers) (sp dst ret left right : BitVec 64) (p : Inputs) (b : Values Value 363) (m : Ram) : Prop extends Controls a b (by decide), Saved a m sp ret where
  r7 : b[7].get 64 = dst
  r65 : b[65].get 64 = sp - 112
  r153 : b[153].get 64 = (v10857b p).1
  r156 : b[156].get 64 = (v10857e p).1
  r283 : b[283].get 64 = v10867a p
  r294 : b[294].get 64 = v10868f p
  r300 : b[300].get 64 = v10869c p
  r314 : b[314].get 64 = v1086b1 p
  r316 : b[316].get 64 = negateOperand p
  r330 : b[330].get 64 = (v1086d2 p).1
  r357 : b[357].get 64 = (v108700 p).1
  r359 : b[359].get 64 = v108703 p
  r361 : b[361].get 64 = v10867a p
  msp56_64 : memLoad m (sp - 56) 64 = (((if !((v10861f p).2.CF) then 1 else 0 : BitVec 8)).setWidth 32).setWidth 64
  msp104_64 : memLoad m (sp - 104) 64 = (v1085d8 p).1
  msp96_8 : memLoad m (sp - 96) 8 = ((mergeGPR 8 (v1085f2 p) ((((mergeGPR 8 (v1085e6 p) (v10851c p))).setWidth 32).setWidth 64))).setWidth 8
  msp88_64 : memLoad m (sp - 88) 64 = (mergeGPR 8 (v1085e6 p) (v10851c p))
  msp80_8 : memLoad m (sp - 80) 8 = ((mergeGPR 8 (v1085b3 p) (v1084f4 p))).setWidth 8

structure At10874b (a : Registers) (sp dst ret left right : BitVec 64) (p : Inputs) (b : Values Value 401) (m : Ram) : Prop extends Controls a b (by decide), Saved a m sp ret where
  r7 : b[7].get 64 = dst
  r65 : b[65].get 64 = sp - 112
  r156 : b[156].get 64 = (v10857e p).1
  r300 : b[300].get 64 = v10869c p
  r316 : b[316].get 64 = negateOperand p
  r330 : b[330].get 64 = (v1086d2 p).1
  r357 : b[357].get 64 = (v108700 p).1
  r384 : b[384].get 64 = (v10872e p).1
  r398 : b[398].get 64 = v108743 p
  msp112_64 : memLoad m (sp - 112) 64 = v108743 p
  msp56_64 : memLoad m (sp - 56) 64 = (((if !((v10861f p).2.CF) then 1 else 0 : BitVec 8)).setWidth 32).setWidth 64
  msp104_64 : memLoad m (sp - 104) 64 = (v1085d8 p).1
  msp96_8 : memLoad m (sp - 96) 8 = ((mergeGPR 8 (v1085f2 p) ((((mergeGPR 8 (v1085e6 p) (v10851c p))).setWidth 32).setWidth 64))).setWidth 8
  msp88_64 : memLoad m (sp - 88) 64 = (mergeGPR 8 (v1085e6 p) (v10851c p))
  msp80_8 : memLoad m (sp - 80) 8 = ((mergeGPR 8 (v1085b3 p) (v1084f4 p))).setWidth 8

structure At10878d (a : Registers) (sp dst ret left right : BitVec 64) (p : Inputs) (b : Values Value 441) (m : Ram) : Prop extends Controls a b (by decide), Saved a m sp ret where
  r7 : b[7].get 64 = dst
  r65 : b[65].get 64 = sp - 112
  r300 : b[300].get 64 = v10869c p
  r330 : b[330].get 64 = (v1086d2 p).1
  r357 : b[357].get 64 = (v108700 p).1
  r384 : b[384].get 64 = (v10872e p).1
  r433 : b[433].get 64 = v108780 p
  r435 : b[435].get 64 = v108783 p
  r439 : b[439].get 64 = (v10878a p).1
  msp96_8 : memLoad m (sp - 96) 8 = ((mergeGPR 8 (v1085f2 p) ((((mergeGPR 8 (v1085e6 p) (v10851c p))).setWidth 32).setWidth 64))).setWidth 8
  msp88_64 : memLoad m (sp - 88) 64 = (mergeGPR 8 (v1085e6 p) (v10851c p))
  msp80_8 : memLoad m (sp - 80) 8 = ((mergeGPR 8 (v1085b3 p) (v1084f4 p))).setWidth 8

structure At1087d9 (a : Registers) (sp dst ret left right : BitVec 64) (p : Inputs) (b : Values Value 483) (m : Ram) : Prop extends Controls a b (by decide), Saved a m sp ret where
  r7 : b[7].get 64 = dst
  r65 : b[65].get 64 = sp - 112
  r300 : b[300].get 64 = v10869c p
  r330 : b[330].get 64 = (v1086d2 p).1
  r357 : b[357].get 64 = (v108700 p).1
  r384 : b[384].get 64 = (v10872e p).1
  r439 : b[439].get 64 = (v10878a p).1
  r459 : b[459].get 64 = selectMagnitude p
  r463 : b[463].get 64 = v1087bb p
  r468 : b[468].get 64 = (v1087c4 p).1
  r473 : b[473].get 64 = (v1087cd p).1
  r476 : b[476].get 64 = (v1087d0 p).1
  r477 : b[477].truth = (v1087d0 p).2.CF
  r481 : b[481].get 64 = v1087d6 p
  msp88_64 : memLoad m (sp - 88) 64 = (mergeGPR 8 (v1085e6 p) (v10851c p))
  msp80_8 : memLoad m (sp - 80) 8 = ((mergeGPR 8 (v1085b3 p) (v1084f4 p))).setWidth 8

structure At10881b (a : Registers) (sp dst ret left right : BitVec 64) (p : Inputs) (b : Values Value 517) (m : Ram) : Prop extends Controls a b (by decide), Saved a m sp ret where
  r7 : b[7].get 64 = dst
  r65 : b[65].get 64 = sp - 112
  r357 : b[357].get 64 = (v108700 p).1
  r384 : b[384].get 64 = (v10872e p).1
  r439 : b[439].get 64 = (v10878a p).1
  r459 : b[459].get 64 = selectMagnitude p
  r473 : b[473].get 64 = (v1087cd p).1
  r476 : b[476].get 64 = (v1087d0 p).1
  r489 : b[489].get 64 = (v1087e7 p).1
  r501 : b[501].get 64 = v1087fd p
  r512 : b[512].get 64 = v108810 p
  r515 : b[515].get 64 = (((selectMagnitude p).setWidth 8).setWidth 32).setWidth 64
  msp88_64 : memLoad m (sp - 88) 64 = (mergeGPR 8 (v1085e6 p) (v10851c p))
  msp80_8 : memLoad m (sp - 80) 8 = ((mergeGPR 8 (v1085b3 p) (v1084f4 p))).setWidth 8

structure At10885c (a : Registers) (sp dst ret left right : BitVec 64) (p : Inputs) (b : Values Value 554) (m : Ram) : Prop extends Controls a b (by decide), Saved a m sp ret where
  r7 : b[7].get 64 = dst
  r65 : b[65].get 64 = sp - 112
  r501 : b[501].get 64 = v1087fd p
  r512 : b[512].get 64 = v108810 p
  r523 : b[523].get 64 = v108824 p
  r534 : b[534].get 64 = v108838 p
  r546 : b[546].get 64 = v10884f p
  r550 : b[550].get 64 = rightProductSign p
  r552 : b[552].get 64 = (mergeGPR 8 (v108859 p) (selectMagnitude p))
  msp80_8 : memLoad m (sp - 80) 8 = ((mergeGPR 8 (v1085b3 p) (v1084f4 p))).setWidth 8

structure At10888a (a : Registers) (sp dst ret left right : BitVec 64) (p : Inputs) (b : Values Value 589) (m : Ram) : Prop extends Controls a b (by decide) where
  r568 : b[568] = ⟨64, (a[3].get 64)⟩
  r571 : b[571] = ⟨64, (a[12].get 64)⟩
  r574 : b[574] = ⟨64, (a[13].get 64)⟩
  r577 : b[577] = ⟨64, (a[14].get 64)⟩
  r580 : b[580] = ⟨64, (a[15].get 64)⟩
  r583 : b[583] = ⟨64, (a[5].get 64)⟩
  r586 : b[586] = ⟨64, ret⟩
  r587 : b[587] = ⟨64, (sp + 8)⟩
  mdst0_64 : memLoad m dst 64 = v1087fd p
  mdst8_64 : memLoad m (dst + 8) 64 = v108810 p
  mdst16_64 : memLoad m (dst + 16) 64 = v108824 p
  mdst24_64 : memLoad m (dst + 24) 64 = v108838 p
  mdst32_64 : memLoad m (dst + 32) 64 = v10884f p
  mdst40_8 : memLoad m (dst + 40) 8 = ((mergeGPR 8 (v108876 p) (rightProductSign p))).setWidth 8

def returnBlock : Block Op Label signature Reg.count 589 :=
  .terminate (.ret (RegMap.args [(0, 563), (1, 554), (2, 550), (3, 568), (4, 587), (5, 583), (6, 501), (7, 7), (8, 523), (9, 534), (10, 546), (11, 517), (12, 571), (13, 574), (14, 577), (15, 580), (22, 22), (39, 39), (50, 50), (51, 51)] 589) (some ⟨586, by decide⟩))


structure Returned (a : Registers) (sp dst ret : BitVec 64) (p : Inputs)
    (o : Output Value Ram Reg.count) : Prop where
  tag : o.tag = some ⟨64, ret⟩
  rsp : o.values[4] = ⟨64, sp + 8⟩
  rbx : o.values[3] = ⟨64, a[3].get 64⟩
  rbp : o.values[5] = ⟨64, a[5].get 64⟩
  r12 : o.values[12] = ⟨64, a[12].get 64⟩
  r13 : o.values[13] = ⟨64, a[13].get 64⟩
  r14 : o.values[14] = ⟨64, a[14].get 64⟩
  r15 : o.values[15] = ⟨64, a[15].get 64⟩
  df : o.values[22] = a[22]
  mxcsr : o.values[39] = a[39]
  ftw : o.values[50] = a[50]
  fcw : o.values[51] = a[51]
  mag0 : memLoad o.store dst 64 = (resultWords p)[0]
  mag1 : memLoad o.store (dst + 8) 64 = (resultWords p)[1]
  mag2 : memLoad o.store (dst + 16) 64 = (resultWords p)[2]
  mag3 : memLoad o.store (dst + 24) 64 = (resultWords p)[3]
  mag4 : memLoad o.store (dst + 32) 64 = (resultWords p)[4]
  sign : memLoad o.store (dst + 40) 8 = resultSign p

end K256.Proofs.Generate.Generator.Affine.Invert.Core.LinearCombination
