import K256.Proofs.Generate.Generator.Multiply.Loop.State
import K256.Proofs.Generate.Generator.Multiply.DoubleExecution.Body

namespace K256.Proofs.Generate.Generator.Multiply

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters.Secp256k1

structure RoundState (fr : Activation) (d k : Nat) (l : Label) (a : Registers) (m : Ram) : Prop where
  atoms : Atom.All Extracted.programImage a m (Fn11c880.frameAt l fr)
  widths : ParseSignature.ArgumentWidths a
  saved : SavedWidths a
  memory : WindowMemory fr m d
  count : memLoad m (fr.rsp - 0xa68) 64 = BitVec.ofNat 64 k + 1
  pointer : memLoad m (fr.rsp - 0xbc8) 64 = (fr.r9 + BitVec.ofNat 64 (32+k)) + 1

end K256.Proofs.Generate.Generator.Multiply
