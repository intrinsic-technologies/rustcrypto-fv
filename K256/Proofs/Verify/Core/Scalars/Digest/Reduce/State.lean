import K256.Proofs.Verify.Core.Scalars.State
import K256.Proofs.Verify.LIR.Fn109f80.Frame
import K256.Proofs.ParseSignature.Contract
import K256.Proofs.ParseSignature.Scalar.Borrow

namespace K256.Proofs.Verify.Core.Reduce

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Generate.Generator.Multiply ParseSignature

abbrev sp (fr : Activation) := fr.rsp - 88

def difference (w : Vector (BitVec 64) 4) : Vector (BitVec 64) 4 :=
  let s0 := 0x402da1732fc9bebf + w[0]
  let c0 := (~~~w[0] ||| s0) >>> 63
  let s1 := 0x4551231950b75fc5 + w[1] + (0 - c0).sshiftRight 63
  let c1 := (~~~w[1] ||| s1) >>> 63
  let s2 := (0 - c1).sshiftRight 63 + w[2] + 2
  let c2 := (~~~w[2] ||| s2) >>> 63
  #v[s0,s1,s2,((c2 - 1) >>> 63) + w[3]]

abbrev borrow (w : Vector (BitVec 64) 4) := Scalar.borrowChain w[0] w[1] w[2] w[3]

structure Live (fr : Activation) (w : Vector (BitVec 64) 4) (a : Registers) (m : Ram) : Prop where
  atoms : Atom.All Extracted.programImage a m (Fn109f80.frameAt .l10a053 fr)
  frame : RamWriteFrame fr.original m [fr.region]
  widths : ArgumentWidths a
  r14 : a[14] = ⟨64,w[0]⟩
  r12 : a[12] = ⟨64,w[1]⟩
  rbp : a[5] = ⟨64,w[2]⟩
  r15 : a[15] = ⟨64,w[3]⟩
  lowDiff : memLoad m (sp fr + 24) 64 = (difference w)[0]
  r13 : a[13] = ⟨64,(difference w)[1]⟩
  highDiff : memLoad m (sp fr + 16) 64 = (difference w)[2]
  rbx : a[3] = ⟨64,(difference w)[3]⟩

end K256.Proofs.Verify.Core.Reduce
