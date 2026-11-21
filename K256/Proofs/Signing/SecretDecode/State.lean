import K256.Proofs.Verify.Core.State
import K256.Proofs.Verify.LIR.Fn106dd0.Frame
import K256.Proofs.Generate.Sampling.Predicate
namespace K256.Proofs.Signing.SecretDecode

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters

abbrev word (fr : Activation) := Common.scalarWord fr.original fr.rsi

structure Frame (l : Label) (fr : Activation) (a : Verify.Core.Registers) (m : Ram) : Prop where
  atoms : Atom.All Extracted.programImage a m (Fn106dd0.frameAt l fr)
  writes : RamWriteFrame fr.original m [fr.region]
  widths : ParseSignature.ArgumentWidths a

structure Limbs (fr : Activation) (a : Verify.Core.Registers) : Prop where
  w0 : a[14] = ⟨64, word fr 0⟩
  w1 : a[15] = ⟨64, word fr 1⟩
  w2 : a[12] = ⟨64, word fr 2⟩
  w3 : a[13] = ⟨64, word fr 3⟩
  rbpWidth : a[5].width = 64

end K256.Proofs.Signing.SecretDecode
