import K256.Proofs.Signing.SecretDecode.Fill
import K256.Proofs.Signing.SecretDecode.Range
import K256.Proofs.Signing.SecretDecode.Nonzero
import K256.Proofs.Signing.SecretDecode.Return
import K256.Proofs.Verify.Transfer.SignatureWords

namespace K256.Proofs.Signing.SecretDecode

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters

theorem execution {fr : Activation} {a : Values Value Reg.count} {secret : ByteArray} {d : Nat}
    (entry : Atom.All Extracted.programImage a fr.original (Fn106dd0.frameAt .l106dd0 fr))
    (image : ∀ b ∈ Extracted.programImage, fr.original[b.1]? = some b.2)
    (low : fr.low = fr.rsp - 336) (room : 336 ≤ fr.rsp.toNat)
    (high : fr.rsp.toNat + 80 < 2^32)
    (dst : fr.rdi = fr.rsp + 40)
    (writable : Writable Extracted.programImage fr.original fr.rdi 40)
    (length : secret.size = 32)
    (bytes : (⟨fr.rsi.toNat, 32⟩ : MemoryRegion).HasBytes fr.original secret)
    (source : Readable fr.original fr.rsi 32)
    (limit : fr.rsi.toNat + 32 < 2^32)
    (apart : fr.rsi.toNat + 32 ≤ fr.rsp.toNat - 336 ∨ fr.rsp.toNat + 80 ≤ fr.rsi.toNat)
    (decoded : Keys.decodeSecret Secp256k1.domain secret = some d) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l106dd0, a, fr.original⟩, []⟩ out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧
      Atom.All Extracted.programImage out.values out.store (Fn106dd0.doneAt fr) ∧
      ParseSignature.ArgumentWidths out.values ∧
      RamWriteFrame fr.original out.store [fr.region, ⟨fr.rdi.toNat, 40⟩] ∧
      memLoad out.store fr.rdi 64 = 0 ∧
      WordsAt out.store (fr.rdi + 8) 64
        (Vector.ofFn fun i : Fin 4 => BitVec.ofNat 64 (d / 2^(64*i.val))) := by
  have ok := Generate.Sampling.decodeSecret_eq_words bytes length
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq, decoded] at ok
  split at ok
  next valid =>
    obtain rfl := Option.some.inj ok
    obtain ⟨b, m, fill, hb, words⟩ := fillPath entry image low room high source limit apart
    obtain ⟨c, n, range, hc, limbs⟩ := rangePath low room high hb words valid.1
    obtain ⟨e, t, nz, he, limbs'⟩ := nonzeroPath low room high hc limbs
      (fun all => valid.2 ((Generate.Sampling.words_all_zero_iff _).mp all))
    obtain ⟨out, run, tag, atoms, widths, writes, zero, result⟩ := returnPath dst writable he limbs'
    refine ⟨out, Program.Exec.of_sem ((fill.trans (range.trans nz)).exec run.sem),
      tag, atoms, widths, writes, zero, Verify.Transfer.wordsAt_of_scalarLimbsAt ?_⟩
    intro i hi
    simpa only [Vector.getElem_ofFn] using result i hi
  next => contradiction

end K256.Proofs.Signing.SecretDecode
