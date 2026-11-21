import K256.Proofs.Generate.Generator.Multiply.Prepare.Bases.Endomorphism.Machine

namespace K256.Proofs.Generate.Generator.Multiply.Prepare

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters.Secp256k1

theorem endomorphismCall {fr : Activation} {a : Registers} {m : Ram}
    (atoms : Atom.All Extracted.programImage a m (Fn10e010.frameAt .l10e010 fr))
    (loaded : ∀ v ∈ Extracted.programImage, m[v.1]? = some v.2)
    (src : Readable m fr.rsi 120) (dst : Writable Extracted.programImage m fr.rdi 120)
    (aboveSrc : fr.rsp.toNat + 8 ≤ fr.rsi.toNat) (aboveDst : fr.rsp.toNat + 8 ≤ fr.rdi.toNat)
    (apart : fr.rsi.toNat + 120 ≤ fr.rdi.toNat ∨ fr.rdi.toNat + 120 ≤ fr.rsi.toNat)
    (input : ∀ i : Fin 15, memLoad m (wordAddr fr.rsi 64 i.val) 64 =
      memLoad m (wordAddr 0x202bc8 64 i.val) 64) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l10e010, a, m⟩, []⟩ out ∧
      out.tag = some ⟨64,fr.ret⟩ ∧ Atom.All Extracted.programImage out.values out.store (Fn10e010.doneAt fr) ∧
      ParseSignature.ArgumentWidths out.values ∧
      RamWriteFrame m out.store [⟨fr.rsp.toNat - 128,128⟩,⟨fr.rdi.toNat,120⟩] ∧
      ∃ p : Projective, p.valid ∧ p.Stored out.store fr.rdi ∧ p.value = Curve.endomorphism domain.G := by
  obtain ⟨out, run, tag, done_, widths, frame, words⟩ :=
    Endomorphism.run atoms src dst aboveSrc aboveDst apart (Endomorphism.sourceWords loaded input)
  exact ⟨out, run, tag, done_, widths, frame, Endomorphism.resultOfWords words⟩

end K256.Proofs.Generate.Generator.Multiply.Prepare
