import K256.Proofs.Verify.Core.Lincomb.Prepare.State

namespace K256.Proofs.Verify.Core.Lincomb.Prepare

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (scalarWords)
open Generate.Curve

structure SplitFrame (initial : Registers) (original : Ram) (sp src tables digits : BitVec 64)
    (b : Registers) (n : Ram) : Prop extends SavedFrame initial sp tables b n where
  frame : RamWriteFrame original n [scratch sp 0x558]
  pointPtr : memLoad n (frameSp sp + 0x28) 64 = src
  digitPtr : memLoad n (frameSp sp + 0xd8) 64 = digits
  arguments : ParseSignature.ArgumentWidths b

structure Residues (initial : Registers) (original : Ram) (sp src tables digits : BitVec 64)
    (k : Nat) (b : Registers) (n : Ram) : Prop extends SplitFrame initial original sp src tables digits b n where
  firstWords : WordsAt n (frameSp sp + 0x38) 64 (scalarWords (splitFirst k))
  secondWords : WordsAt n (frameSp sp + 0xb0) 64 (scalarWords (splitSecond k))

structure Signs (initial : Registers) (original : Ram) (sp src tables digits : BitVec 64)
    (k : Nat) (b : Registers) (n : Ram) : Prop extends SplitFrame initial original sp src tables digits b n where
  firstSign : b[14].get 8 = signByte (first k)
  secondSign : b[0].get 8 = signByte (second k)
  firstWords : WordsAt n (frameSp sp + 8) 64 (scalarWords (splitFirst k))
  low : memLoad n (frameSp sp + 0x30) 64 = (scalarWords (splitSecond k))[0]
  midLow : b[12].get 64 = (scalarWords (splitSecond k))[1]
  midHigh : b[5].get 64 = (scalarWords (splitSecond k))[2]
  high : b[13].get 64 = (scalarWords (splitSecond k))[3]

end K256.Proofs.Verify.Core.Lincomb.Prepare
