import ChaCha20Poly1305.Proofs.MemoryRoutines.Contracts
import ChaCha20Poly1305.Proofs.CoreContract

namespace ChaCha20Poly1305.Proofs.Encrypt.Prefix

open ChaCha20Poly1305.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open MemoryRoutines CoreContract

theorem copied_input [Bindings] {s t : RamState} {bytes : ByteArray}
    (hs : ValidInput s (registerRegion s .rsi bytes.size) bytes)
    (hd : (rdi.read s).toNat + bytes.size < 2^32)
    (hlen : (rdx.read s).toNat = bytes.size)
    (hc : MemcpyResult s t) :
    ValidInput t (messageRegion (rdi.read s) bytes.size) bytes := by
  refine ⟨hd, rfl, fun i => ?_⟩
  have he (p : BitVec 64) (hi : p.toNat + bytes.size < 2^32) :
      BitVec.ofNat 64 (p.toNat + i.val) = p + BitVec.ofNat 64 i.val := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_add]
    have := i.isLt
    omega
  change t.external[BitVec.ofNat 64 ((rdi.read s).toNat + i.val)]? = _
  rw [he _ hd, hc.copy i.val (by rw [hlen]; exact i.isLt)]
  have src := hs.2.2 i
  change s.external[BitVec.ofNat 64 ((rsi.read s).toNat + i.val)]? = _ at src
  rw [he (rsi.read s) hs.1] at src
  exact src

end ChaCha20Poly1305.Proofs.Encrypt.Prefix
