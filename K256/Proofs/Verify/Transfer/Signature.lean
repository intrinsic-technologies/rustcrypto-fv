import K256.Proofs.Verify.Transfer.Signature.Relabel
import K256.Proofs.Verify.Transfer.SignatureWords
import K256.Proofs.Verify.LIR.Fn103ac0.Frame
import K256.Proofs.ParseSignature.Pair
import K256.Proofs.Common.SignatureRun

namespace K256.Proofs.Verify.Transfer

open K256.Spec K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
open CFG Lift Refine Generate.Generator.Multiply ParseSignature
open Standards.SECG.DomainParameters.Secp256k1 Verify.LIR

theorem signatureExecution (fr : Activation) (a : Values Value Reg.count)
    (entry : Atom.All Extracted.programImage a fr.original (Fn103ac0.frameAt .l103ac0 fr))
    (src : Readable fr.original fr.rsi 64) (dst : Writable Extracted.programImage fr.original fr.rdi 72)
    (srcApart : Outside [callStack fr] fr.rsi 64) (dstApart : Outside [callStack fr] fr.rdi 72)
    {bytes : ByteArray} {r s : Nat}
    (input : (⟨fr.rsi.toNat,64⟩ : MemoryRegion).HasBytes fr.original bytes)
    (decoded : Ecdsa.signatureScalars bytes = some (r,s)) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l103ac0,a,fr.original⟩,[]⟩ out ∧
      out.tag = some ⟨64,fr.ret⟩ ∧ Atom.All Extracted.programImage out.values out.store (Fn103ac0.doneAt fr) ∧
      RamWriteFrame fr.original out.store [fr.region, ⟨fr.rdi.toNat,72⟩] ∧
      ArgumentWidths out.values ∧ memLoad out.store fr.rdi 64 = 0 ∧
      WordsAt out.store (fr.rdi+8) 64 (scalarWords r) ∧ WordsAt out.store (fr.rdi+40) 64 (scalarWords s) := by
  obtain ⟨hr,hs,bounds⟩ := signatureValues input decoded
  subst r s
  obtain ⟨old,run,tag,done_,frame,widths,post⟩ :=
    decodePair_call Common.fnCode_subset_programImage fr src dst srcApart dstApart a entry
  dsimp only at post
  rw [ite_eq_left bounds] at post
  obtain ⟨out,exec,mem,ret,regs⟩ := Signature.transferAt (y := .l103ac0) rfl run
  refine ⟨out,exec,ret.trans tag,?_,mem ▸ frame,?_,mem ▸ post.1,
    mem ▸ wordsAt_of_scalarLimbsAt post.2.1, mem ▸ wordsAt_of_scalarLimbsAt post.2.2⟩
  · change Atom.All Extracted.programImage old.values old.store (Fn103ac0.doneAt fr) at done_
    simp only [Fn103ac0.doneAt, Atom.All, Atom.Holds] at done_ ⊢
    simpa only [regs 4 (by decide), regs 22 (by decide), regs 3 (by decide),
      regs 5 (by decide), regs 12 (by decide), regs 13 (by decide), regs 14 (by decide),
      regs 15 (by decide), regs 39 (by decide), regs 50 (by decide), regs 51 (by decide)] using done_
  · intro i hi
    rw [regs i (by
      simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
      omega)]
    exact widths i hi

end K256.Proofs.Verify.Transfer
