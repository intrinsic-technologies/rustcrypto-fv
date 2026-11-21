import Sha1.Proofs.Buffered.Update.Contracts
import Sha1.Proofs.Common.CompressCall
import Sha1.Proofs.MemoryRoutines.Memcpy
import Sha1.Proofs.MemoryRoutines.Memset
import Sha1.Proofs.Compress.Machine.Code

namespace Sha1.Proofs.Buffered

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem outside_text_range_of_not_inProgram {address : BitVec 64}
    (h : ¬ InProgram address) (lo hi : Nat) (hlo : 0x100000 ≤ lo)
    (hhi : hi ≤ 0x100000 + Extracted.textBytes.size) :
    address.toNat < lo ∨ hi ≤ address.toNat := by
  apply Classical.byContradiction
  intro hn
  have hlow : lo ≤ address.toNat := by omega
  have hhigh : address.toNat < hi := by omega
  have hoff : address.toNat - 0x100000 < Extracted.textBytes.size := by omega
  have heq : Extracted.textAddress + BitVec.ofNat 64 (address.toNat - 0x100000) = address := by
    change BitVec.ofNat 64 0x100000 + BitVec.ofNat 64 (address.toNat - 0x100000) = address
    rw [← BitVec.ofNat_add, show 0x100000 + (address.toNat - 0x100000) = address.toNat by omega,
      BitVec.ofNat_toNat, BitVec.setWidth_eq]
  exact h (heq ▸ Sha1.Proofs.Compress.Machine.text_address_in_program _ hoff)

end Sha1.Proofs.Buffered
