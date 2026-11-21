import K256.Proofs.Ecdh.Affine.State

namespace K256.Proofs.Verify.Core.Affine

open Ecdh.Affine

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR
open K256.Proofs.Generate.Generator.Affine
open Standards.SECG.ECC

private def ignoreVolatile : Atom → Atom
  | .reg 1 _ | .reg 2 _ | .reg 8 _ | .reg 9 _ => .fact True
  | atom => atom

def atomsAt (l : Label) (fr : Activation) : List Atom :=
  (Fn10fe50.frameAt l fr).map ignoreVolatile

structure CallState (l : Label) (fr : Activation) (a : Registers) (m : Ram) : Prop where
  atoms : Atom.All Extracted.programImage a m (atomsAt l fr)
  image : ∀ b ∈ Extracted.programImage, m[b.1]? = some b.2
  source : Readable m fr.rsi 120
  dest : Writable Extracted.programImage m fr.rdi 88
  srcAddr : fr.rsi = fr.rsp + 16
  dstAddr : fr.rdi = fr.rsp + 144
  high : fr.rsp.toNat + 232 ≤ 2^32
  frame : RamWriteFrame fr.original m (writes fr)

end K256.Proofs.Verify.Core.Affine
