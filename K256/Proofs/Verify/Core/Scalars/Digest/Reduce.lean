import K256.Proofs.Verify.Core.Scalars.Digest.Reduce.Entry
import K256.Proofs.Verify.Core.Scalars.Digest.Reduce.Finish
import K256.Proofs.Verify.Core.Scalars.Digest.Reduce.Arithmetic
import K256.Proofs.Verify.Core.Scalars.Digest.Reduce.InvertChoice

namespace K256.Proofs.Verify.Core

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.DomainParameters.Secp256k1 Generate.Generator.Multiply ParseSignature

theorem reduceScalar {fr : Activation} {a : Registers} {x : Nat}
    (entry : Atom.All Extracted.programImage a fr.original (Fn109f80.frameAt .l109f80 fr))
    (src : Readable fr.original fr.rsi 32) (dst : Writable Extracted.programImage fr.original fr.rdi 32)
    (srcApart : Outside [callStack fr] fr.rsi 32) (dstApart : Outside [callStack fr] fr.rdi 32)
    (words : WordsAt fr.original fr.rsi 64 (scalarWords x)) (bound : x < 2^256) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l109f80, a, fr.original⟩, []⟩ out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧ Atom.All Extracted.programImage out.values out.store (Fn109f80.doneAt fr) ∧
      RamWriteFrame fr.original out.store [fr.region, buffer fr.rdi 32] ∧
      WordsAt out.store fr.rdi 64 (scalarWords (x % domain.n)) ∧ ArgumentWidths out.values := by
  obtain ⟨b,m,first,live,flag⟩ := Reduce.entry entry src srcApart words
  obtain ⟨eqWords,eqBorrow⟩ := Reduce.reductionWords bound
  let choose := decide (¬ x < domain.n)
  have input : b[0] = ⟨64,if choose then 0 else 1⟩ := by
    rw [flag,eqBorrow]
    by_cases h : x < domain.n <;> simp [choose,h]
  obtain ⟨c,n,second,live,flag⟩ := Reduce.invertChoice live choose input
  obtain ⟨out,run,tag,done,writes,result,widths⟩ := Reduce.finish choose live flag dst dstApart
  have reduced : (if choose then Reduce.difference (scalarWords x) else scalarWords x) =
      scalarWords (x % domain.n) := by
    by_cases h : x < domain.n <;> simpa [choose,h] using eqWords
  exact ⟨out,Program.Exec.of_sem ((first.trans second).exec run.sem),tag,done,writes,reduced ▸ result,widths⟩

end K256.Proofs.Verify.Core
