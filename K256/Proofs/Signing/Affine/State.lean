import K256.Proofs.Verify.Core.Affine.State

namespace K256.Proofs.Signing.Affine

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR
open K256.Proofs.Generate.Generator.Affine
open Standards.SECG.ECC

structure CallState (l : Label) (fr : Activation) (a : Registers) (m : Ram) : Prop where
  atoms : Atom.All Extracted.programImage a m (Verify.Core.Affine.atomsAt l fr)
  image : ∀ b ∈ Extracted.programImage, m[b.1]? = some b.2
  source : Readable m fr.rsi 120
  dest : Writable Extracted.programImage m fr.rdi 88
  srcAbove : fr.rsp.toNat + 8 ≤ fr.rsi.toNat
  dstAbove : fr.rsp.toNat + 8 ≤ fr.rdi.toNat
  frame : RamWriteFrame fr.original m (writes fr)

end K256.Proofs.Signing.Affine
