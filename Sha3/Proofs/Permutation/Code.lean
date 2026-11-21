import Sha3.Proofs.Image
import Sha3.Proofs.Permutation.Layout

namespace Sha3.Proofs.Permutation

open X86 Sha3.Spec.Program Prelude

theorem inProgram_text_offset (offset : Nat) (h : offset < Extracted.textBytes.size) :
    InProgram (Extracted.textAddress + BitVec.ofNat 64 offset) := by
  obtain ⟨byte, hbyte⟩ : ∃ byte, Extracted.textBytes.get? offset = some byte := by
    simp only [Bytes.Chunked.get?, h, ite_true]
    exact ⟨_, rfl⟩
  have hm := codeRange_mem_of_getElem? (chunked_getElem?_toList_of_get? hbyte)
    Extracted.textAddress
  refine ⟨byte, ?_⟩
  change (Extracted.textAddress + BitVec.ofNat 64 offset, byte) ∈
    UserProcess.codeRange Extracted.textAddress Extracted.textBytes.toList ++ _
  exact List.mem_append_left _ hm

theorem inProgram_permutation_address {address : BitVec 64}
    (hlo : 0x100000 ≤ address.toNat) (hhi : address.toNat ≤ 0x106222) : InProgram address := by
  have hsize : 0x6223 ≤ Extracted.textBytes.size := by decide +kernel
  have hoff : (address - Extracted.textAddress).toNat < Extracted.textBytes.size := by
    rw [BitVec.toNat_sub]
    change ((2 ^ 64 - 0x100000) + address.toNat) % 2 ^ 64 < Extracted.textBytes.size
    omega
  have h := inProgram_text_offset (address - Extracted.textAddress).toNat hoff
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm Extracted.textAddress,
    BitVec.sub_add_cancel] using h

theorem permutation_address_ne_boundary {address : BitVec 64} {boundary : UserProcess.ReturnBoundary}
    (hboundary : ¬ InProgram boundary.rip) (hlo : 0x100000 ≤ address.toNat)
    (hhi : address.toNat ≤ 0x106222) : address ≠ boundary.rip := by
  intro h
  exact hboundary (h ▸ inProgram_permutation_address hlo hhi)

end Sha3.Proofs.Permutation
