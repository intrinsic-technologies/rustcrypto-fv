import K256.Proofs.Verify.LIR.Fn104c90.Frame
import K256.Proofs.Verify.Core.Signature.High

namespace K256.Proofs.Signing.Scalar.Normalize

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  Verify.LIR Generate.Generator.Multiply Standards.SECG.DomainParameters.Secp256k1

structure Inputs (fr : Activation) (r s : Nat) : Prop where
  image : ∀ b ∈ Extracted.programImage, fr.original[b.1]? = some b.2
  low : fr.low = fr.rsp - 464
  room : 464 ≤ fr.rsp.toNat
  high : fr.rsp.toNat + 264 < 2^32
  dst : fr.rdi = fr.rsp + 16
  src : fr.rsi = fr.rsp + 200
  write : Writable Extracted.programImage fr.original fr.rdi 64
  read : Readable fr.original fr.rsi 64
  rWords : WordsAt fr.original fr.rsi 64 (scalarWords r)
  sWords : WordsAt fr.original (fr.rsi + 32) 64 (scalarWords s)
  rPos : 0 < r
  rBound : r < domain.n
  sPos : 0 < s
  sBound : s < domain.n

structure Saved (fr : Activation) (a : Verify.Core.Registers) (m : Ram) : Prop where
  atoms : Atom.All Extracted.programImage a m (Fn104c90.frameAt .l104d5e fr)
  frame : RamWriteFrame fr.original m [fr.region]

theorem Inputs.words_of_frame {fr : Activation} {r s : Nat} {m : Ram}
    (input : Inputs fr r s) (frame : RamWriteFrame fr.original m [fr.region]) :
    WordsAt m fr.rsi 64 (scalarWords r) ∧ WordsAt m (fr.rsi + 32) 64 (scalarWords s) := by
  have room := input.room
  have high := input.high
  refine ⟨input.rWords.of_frame frame (by decide) ?_, input.sWords.of_frame frame (by decide) ?_⟩
  all_goals
    simp only [Outside, List.mem_singleton, forall_eq, Activation.region, input.low,
      input.src, BitVec.add_assoc, BitVec.reduceAdd, BitVec.toNat_add, BitVec.toNat_sub,
      BitVec.reduceToNat, Nat.reducePow, Nat.reduceDiv, Nat.reduceMul]
    omega

end K256.Proofs.Signing.Scalar.Normalize
