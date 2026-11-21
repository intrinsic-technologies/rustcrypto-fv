import K256.Proofs.Common.Refine.Lemma.Store
import X86Proofs.Program.Code

namespace K256.Proofs.ParseSignature

open X86.Machine X86.UserProcess X86Proofs K256.Proofs.Lift K256.Proofs.Refine

theorem storeOk_of_codeRange {code : CodeMap} {mem : Ram} {addr base : BitVec 64}
    {size off len : Nat} {bytes : List UInt8} (writable : Writable code mem addr size)
    (included : ∀ x ∈ codeRange base bytes, x ∈ code) (within : off + len ≤ bytes.length) :
    StoreOk code mem addr size (base + BitVec.ofNat 64 off) len := by
  refine ⟨writable.readable.low, writable.readable.present, writable.tables, ?_, writable.notCode⟩
  intro i hi j hj eq
  apply writable.notCode _ (included _ (mem_codeRange base bytes (off + j) (by omega))) i hi
  simpa only [BitVec.ofNat_add, BitVec.add_assoc] using eq.symm

end K256.Proofs.ParseSignature
