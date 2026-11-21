import K256.Proofs.Signing.Nonce.Initialize.Seed
import K256.Proofs.Signing.Nonce.Initialize.Call
import K256.Proofs.Signing.Nonce.Initialize.Return

namespace K256.Proofs.Signing.Nonce

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters Standards.NIST.SHA2

theorem initializeGenerator {fr : Activation} {a : Values Value Reg.count} {d : Nat} {digest : ByteArray}
    (entry : Atom.All Extracted.programImage a fr.original (Fn100ea0.frameAt .l100ea0 fr))
    (image : ∀ b ∈ Extracted.programImage, fr.original[b.1]? = some b.2)
    (depth : 2208 ≤ fr.rsp.toNat) (low : fr.low = fr.rsp - 2208)
    (limit : fr.rsp.toNat + 784 < 2^32)
    (window : Writable Extracted.programImage fr.original fr.rsp 784)
    (dst : fr.rdi = fr.rsp + 712) (secretPtr : fr.rsi = fr.rsp + 32)
    (digestPtr : fr.rcx = fr.rsp + 376)
    (secretLen : fr.rdx = 32) (digestLen : fr.r8 = 32) (extraPtr : fr.r9 = 1)
    (extraLen : memLoad fr.original (fr.rsp + 8) 64 = 0)
    (orderPtr : memLoad fr.original (fr.rsp + 16) 64 = fr.rsp + 616)
    (orderWords : WordsAt fr.original (fr.rsp + 616) 64 (Vector.ofFn fun i : Fin 4 =>
      BitVec.ofNat 64 (Secp256k1.domain.n / 2^(64*i.val))))
    (secret : (⟨fr.rsi.toNat, 32⟩ : MemoryRegion).HasBytes fr.original (Encoding.natToOctets 32 d))
    (hash : (⟨fr.rcx.toNat, 32⟩ : MemoryRegion).HasBytes fr.original digest)
    (positive : 0 < d) (bound : d < Secp256k1.domain.n) :
    let state := Standards.RFC.DeterministicSigning.Nonce.initialState SHA256.hashBytes 64 32
      Secp256k1.domain.n d digest
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l100ea0, a, fr.original⟩, []⟩ out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧
      Atom.All Extracted.programImage out.values out.store (Fn100ea0.doneAt fr) ∧
      ParseSignature.ArgumentWidths out.values ∧
      RamWriteFrame fr.original out.store [fr.region, ⟨fr.rdi.toNat, 72⟩] ∧
      memLoad out.store fr.rdi 64 = fr.rsp + 616 ∧
      (⟨fr.rdi.toNat + 8, 32⟩ : MemoryRegion).HasBytes out.store state.key ∧
      (⟨fr.rdi.toNat + 40, 32⟩ : MemoryRegion).HasBytes out.store state.value := by
  have _ := positive
  have _ := bound
  obtain ⟨b, m, first, ready⟩ := Initialize.prepare entry image depth low limit window dst secretPtr digestPtr
    secretLen digestLen extraPtr extraLen orderPtr orderWords hash
  obtain ⟨c, n, next, updated⟩ := Initialize.seedUpdate image depth low limit window dst secretPtr digestPtr
    secretLen digestLen extraPtr extraLen orderPtr secret hash.1 ready
  obtain ⟨out, run, post⟩ := Initialize.returnPath dst window depth limit updated
  exact ⟨out, Program.Exec.of_sem ((first.trans next).exec run.sem), post⟩

end K256.Proofs.Signing.Nonce
