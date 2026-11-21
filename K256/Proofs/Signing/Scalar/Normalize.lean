import K256.Proofs.Signing.Scalar.Normalize.Nonzero
import K256.Proofs.Signing.Scalar.Normalize.Negate
import K256.Proofs.Signing.Scalar.Normalize.High
import K256.Proofs.Signing.Scalar.Normalize.Return

namespace K256.Proofs.Signing.Scalar

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  Verify.LIR Generate.Generator.Multiply Standards.SECG.DomainParameters.Secp256k1

theorem normalize {fr : Activation} {a : Values Value Reg.count} {r s : Nat}
    (entry : Atom.All Extracted.programImage a fr.original (Fn104c90.frameAt .l104c90 fr))
    (image : ∀ b ∈ Extracted.programImage, fr.original[b.1]? = some b.2)
    (low : fr.low = fr.rsp - 464) (room : 464 ≤ fr.rsp.toNat)
    (high : fr.rsp.toNat + 264 < 2^32)
    (dst : fr.rdi = fr.rsp + 16) (src : fr.rsi = fr.rsp + 200)
    (write : Writable Extracted.programImage fr.original fr.rdi 64)
    (read : Readable fr.original fr.rsi 64)
    (rWords : WordsAt fr.original fr.rsi 64 (scalarWords r))
    (sWords : WordsAt fr.original (fr.rsi + 32) 64 (scalarWords s))
    (rPos : 0 < r) (rBound : r < domain.n) (sPos : 0 < s) (sBound : s < domain.n) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l104c90,a,fr.original⟩,[]⟩ out ∧
      out.tag = some ⟨64,fr.ret⟩ ∧
      Atom.All Extracted.programImage out.values out.store (Fn104c90.doneAt fr) ∧
      WordsAt out.store fr.rdi 64 (scalarWords r) ∧
      WordsAt out.store (fr.rdi + 32) 64 (scalarWords (if s > domain.n / 2 then domain.n - s else s)) ∧
      RamWriteFrame fr.original out.store [fr.region, ⟨fr.rdi.toNat,64⟩] := by
  let input : Normalize.Inputs fr r s :=
    ⟨image,low,room,high,dst,src,write,read,rWords,sWords,rPos,rBound,sPos,sBound⟩
  obtain ⟨b,m,p,start⟩ := Normalize.nonzero input entry
  obtain ⟨c,n,q,next,ptr,neg⟩ := Normalize.negate input start
  obtain ⟨e,t,v,last,flag,neg⟩ := Normalize.high input next ptr neg
  obtain ⟨out,run,post⟩ := Normalize.finish input last flag neg
  exact ⟨out, Program.Exec.of_sem (((p.trans q).trans v).exec run.sem), post⟩

end K256.Proofs.Signing.Scalar
