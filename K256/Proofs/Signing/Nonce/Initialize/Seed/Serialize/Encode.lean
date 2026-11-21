import K256.Proofs.Signing.Nonce.Initialize.Seed.Serialize.Encode.Entry
import K256.Proofs.Signing.Nonce.Initialize.Seed.Serialize.Encode.Step
import K256.Proofs.Signing.Nonce.Initialize.Seed.Serialize.Encode.Return

import K256.Proofs.Verify.LIR.Fn100000.Frame

namespace K256.Proofs.Signing.Nonce.Initialize

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters Standards.NIST.SHA2

open Generate.Generator.Multiply (scalarWords)

theorem encodeWords {fr : Activation} {a : Verify.Core.Registers} {x : Nat}
    (entry : Atom.All Extracted.programImage a fr.original (Fn100000.frameAt .l100000 fr))
    (depth : 208 ≤ fr.rsp.toNat) (low : fr.low = fr.rsp - 208)
    (srcAfter : fr.rsp.toNat + 8 ≤ fr.rdi.toNat) (srcBeforeDst : fr.rdi.toNat + 32 ≤ fr.rdx.toNat)
    (orderAfter : fr.rsp.toNat ≤ fr.rsi.toNat) (len : fr.rcx = 32)
    (srcRead : Readable fr.original fr.rdi 32) (orderRead : Readable fr.original fr.rsi 32)
    (dstWrite : Writable Extracted.programImage fr.original fr.rdx 32)
    (srcWords : WordsAt fr.original fr.rdi 64 (scalarWords x))
    (orderWords : WordsAt fr.original fr.rsi 64 (scalarWords Secp256k1.domain.n)) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l100000,a,fr.original⟩,[]⟩ out ∧
      out.tag = some ⟨64,fr.ret⟩ ∧
      Atom.All Extracted.programImage out.values out.store (Fn100000.doneAt fr) ∧
      ParseSignature.ArgumentWidths out.values ∧
      RamWriteFrame fr.original out.store [fr.region, ⟨fr.rdx.toNat,32⟩] ∧
      (⟨fr.rdx.toNat,32⟩ : MemoryRegion).HasBytes out.store (Encoding.natToOctets 32 x) := by
  obtain ⟨b,m,h0,l0⟩ := Encode.enterLoop (x := x) entry depth low orderAfter len orderRead orderWords
  let advance {k b m} (hk : k < 4) (loop : Encode.Loop fr x k b m) :=
    Encode.stepLoop hk depth low srcAfter srcBeforeDst srcRead dstWrite srcWords loop
  obtain ⟨b1,m1,h1,l1⟩ := advance (by decide) l0
  obtain ⟨b2,m2,h2,l2⟩ := advance (by decide) l1
  obtain ⟨b3,m3,h3,l3⟩ := advance (by decide) l2
  obtain ⟨b4,m4,h4,l4⟩ := advance (by decide) l3
  obtain ⟨out,run,mem,tag,done_,widths⟩ := Encode.finish depth l4
  refine ⟨out, Program.Exec.of_sem (h0.exec (h1.exec (h2.exec (h3.exec (h4.exec run.sem))))),
    tag, done_, widths, mem ▸ l4.writes, ?_⟩
  rw [mem]
  refine Generate.Wrapper.scalarOctets ?_ ((dstWrite.of_frame l4.writes).readable)
  intro i hi
  have word := l4.words (3-i) (by omega) (by omega)
  rw [show 3-(3-i) = i by omega] at word
  simpa only [scalarWords, Vector.getElem_ofFn] using word

end K256.Proofs.Signing.Nonce.Initialize
