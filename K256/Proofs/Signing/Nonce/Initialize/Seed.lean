import K256.Proofs.Signing.Nonce.Initialize.Seed.Length
import K256.Proofs.Signing.Nonce.Initialize.Seed.Parse
import K256.Proofs.Signing.Nonce.Initialize.Seed.Reduce
import K256.Proofs.Signing.Nonce.Initialize.Seed.Serialize

namespace K256.Proofs.Signing.Nonce.Initialize

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters Standards.NIST.SHA2

theorem prepare {fr : Activation} {a : Verify.Core.Registers} {digest : ByteArray}
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
    (hash : (⟨fr.rcx.toNat, 32⟩ : MemoryRegion).HasBytes fr.original digest)
    : ∃ b m, Verify.Core.Reaches .l100ea0 a fr.original .l101295 b m ∧ Prepared fr b m digest := by
  obtain ⟨b, m, first, length⟩ := digestLength entry image depth low limit window dst secretPtr digestPtr
    secretLen digestLen extraPtr extraLen orderPtr orderWords
  obtain ⟨c, n, second, parsed⟩ := parseDigest depth low limit window digestPtr digestLen hash length
  have bound : Encoding.octetsToNat digest < 2^256 := by
    have len : digest.size = 32 := hash.1
    have eq := Common.octetsToNat_extract_eq_words hash (off := 0) (by omega)
    let w := Common.scalarWord fr.original (BitVec.ofNat 64 (fr.rcx.toNat + 0))
    change Encoding.octetsToNat (digest.extract 0 32) =
      ((w 3).toNat * 2^64 + (w 2).toNat) * 2^128 + (w 1).toNat * 2^64 + (w 0).toNat at eq
    rw [← len, ByteArray.extract_zero_size] at eq
    have := (w 0).isLt
    have := (w 1).isLt
    have := (w 2).isLt
    have := (w 3).isLt
    omega
  obtain ⟨d, p, third, reduced⟩ := reduceDigest depth low limit bound parsed
  obtain ⟨e, q, last, prepared⟩ := serializeDigest depth low limit window secretLen orderPtr orderWords reduced
  exact ⟨e, q, first.trans (second.trans (third.trans last)), prepared⟩

end K256.Proofs.Signing.Nonce.Initialize
