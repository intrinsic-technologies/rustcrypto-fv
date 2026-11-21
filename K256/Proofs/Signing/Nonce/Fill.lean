import K256.Proofs.Signing.Nonce.Fill.Entry
import K256.Proofs.Signing.Nonce.Fill.Generate
import K256.Proofs.Signing.Nonce.Fill.Update
import K256.Proofs.Signing.Nonce.Fill.Decode
import K256.Proofs.Signing.Nonce.Fill.Test
import K256.Proofs.Signing.Nonce.Fill.Return
import K256.Proofs.Signing.Nonce.Fill.Reject

namespace K256.Proofs.Signing.Nonce

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (scalarWords)
open Verify.Core (Registers Reaches)
open Initialize (State StateAt)

theorem fill {fr : Activation} {a : Registers} {seed : State}
    (entry : Atom.All Extracted.programImage a fr.original (Fn100a40.frameAt .l100a40 fr))
    (image : ∀ b ∈ Extracted.programImage, fr.original[b.1]? = some b.2)
    (low : fr.low = fr.rsp - 2160) (depth : 2160 ≤ fr.rsp.toNat)
    (limit : fr.rsp.toNat + 768 < 2^32)
    (window : Writable Extracted.programImage fr.original fr.rsp 768)
    (gen : fr.rdi = fr.rsp + 696) (dst : fr.rsi = fr.rsp + 392) (size : fr.rdx = 32)
    (orderPtr : memLoad fr.original fr.rdi 64 = fr.rsp + 600)
    (orderWords : WordsAt fr.original (fr.rsp + 600) 64 (scalarWords domain.n))
    (seedAt : StateAt fr.original (fr.rdi + 8) seed) :
    ∃ head : State → Registers → Ram → Prop, ∃ b m,
      Reaches .l100a40 a fr.original .l100ab0 b m ∧ head seed b m ∧
      ∀ state c n, head state c n →
        let k := (candidate state).1
        if 0 < k ∧ k < domain.n then
          ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l100ab0,c,n⟩,[]⟩ out ∧
            out.tag = some ⟨64,fr.ret⟩ ∧
            Atom.All Extracted.programImage out.values out.store (Fn100a40.doneAt fr) ∧
            ParseSignature.ArgumentWidths out.values ∧
            RamWriteFrame fr.original out.store
              [fr.region, ⟨fr.rsi.toNat,32⟩, ⟨(fr.rdi+8).toNat,64⟩] ∧
            StateAt out.store (fr.rdi+8) (retry state) ∧
            (⟨fr.rsi.toNat,32⟩ : MemoryRegion).HasBytes out.store (Encoding.natToOctets 32 k)
        else
          ∃ c' n' b' m', Reaches .l100ab0 c n .l100ac0 c' n' ∧
            Reaches .l100ac0 c' n' .l100ab0 b' m' ∧ head (retry state) b' m' := by
  let env : Fill.Environment fr := ⟨image,low,depth,limit,window,gen,dst,size,orderPtr,orderWords⟩
  obtain ⟨b,m,entered,ready⟩ := Fill.entryPath env entry seedAt
  refine ⟨Fill.Head fr,b,m,entered,ready,?_⟩
  intro state c n head
  obtain ⟨d,t,e,u,front,generate,generated⟩ := Fill.generate env head
  obtain ⟨f,v,advance,updated⟩ := Fill.advance env generated
  obtain ⟨g,w,decode,decoded⟩ := Fill.decode env updated
  obtain ⟨h,z,test,tested⟩ := Fill.test env decoded
  let k := (candidate state).1
  by_cases valid : 0 < k ∧ k < domain.n
  · rw [ite_eq_left valid]
    rw [Fill.testTarget, ite_eq_left valid] at test
    obtain ⟨out,run,post⟩ := Fill.returnPath env tested
    exact ⟨out,Program.Exec.of_sem ((front.trans (generate.trans (advance.trans (decode.trans test)))).exec run.sem),post⟩
  · rw [ite_eq_right valid]
    rw [Fill.testTarget, ite_eq_right valid] at test
    obtain ⟨b',m',again,newHead⟩ := Fill.reject env tested
    exact ⟨d,t,b',m',front,generate.trans (advance.trans (decode.trans (test.trans again))),newHead⟩

end K256.Proofs.Signing.Nonce
