import Sha3.Proofs.Image
import X86Proofs.Program.Entry
import Sha3.Proofs.Permutation.LoadStore.Store.Basic
import Sha3.Proofs.Permutation.LoadStore.Store.Restore

namespace Sha3.Proofs.Permutation.Store

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

theorem storeCode_subset_programImage (copy : Copy) :
    ∀ x ∈ codeRange (storeAddress copy) bytes, x ∈ Extracted.programImage := by
  have h := textSlice_subset_programImage
    (by cases copy <;> decide +kernel) (bytes_extracted copy)
  have haddr : Extracted.textAddress +
      BitVec.ofNat 64 ((storeAddress copy).toNat - 0x100000) = storeAddress copy := by
    cases copy <;> rfl
  rwa [haddr] at h

theorem restoreBytes_extracted (copy : Copy) :
    Extracted.textBytes.toListFrom ((restoreAddress copy).toNat - 0x100000) 18 = restoreBytes := by
  cases copy <;> decide +kernel

theorem restoreCode_subset_programImage (copy : Copy) :
    ∀ x ∈ restoreCode copy, x ∈ Extracted.programImage := by
  have h := textSlice_subset_programImage
    (by cases copy <;> decide +kernel) (restoreBytes_extracted copy)
  have haddr : Extracted.textAddress +
      BitVec.ofNat 64 ((restoreAddress copy).toNat - 0x100000) = restoreAddress copy := by
    cases copy <;> rfl
  rwa [haddr] at h

theorem store_restore_code_subset_programImage (copy : Copy) :
    ∀ x ∈ codeRange (storeAddress copy) (bytes ++ restoreBytes), x ∈ Extracted.programImage := by
  rw [codeRange_append, bytes_length]
  have hnext : storeAddress copy + BitVec.ofNat 64 214 = restoreAddress copy := by
    cases copy <;> rfl
  rw [hnext]
  intro x hx
  rcases List.mem_append.mp hx with hs | hr
  · exact storeCode_subset_programImage copy x hs
  · exact restoreCode_subset_programImage copy x hr

theorem inProgram_of_codeRange {base p : BitVec 64} {code : List UInt8}
    (hcode : ∀ x ∈ codeRange base code, x ∈ Extracted.programImage)
    (hlo : base.toNat ≤ p.toNat) (hhi : p.toNat < base.toNat + code.length) : InProgram p := by
  have hi : p.toNat - base.toNat < code.length := by omega
  have haddress : base + BitVec.ofNat 64 (p.toNat - base.toNat) = p := by
    apply BitVec.eq_of_toNat_eq
    have := p.isLt
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  refine ⟨code[p.toNat - base.toNat], hcode _ ?_⟩
  simpa only [haddress] using mem_codeRange base code (p.toNat - base.toNat) hi

theorem store_restore_inProgram (copy : Copy) {p : BitVec 64}
    (hlo : (storeAddress copy).toNat ≤ p.toNat)
    (hhi : p.toNat ≤ (returnAddress copy).toNat) : InProgram p := by
  apply inProgram_of_codeRange (store_restore_code_subset_programImage copy) hlo
  have hlen : (bytes ++ restoreBytes).length = 232 := by
    rw [List.length_append, bytes_length]
    rfl
  rw [hlen]
  have hbound : (returnAddress copy).toNat < (storeAddress copy).toNat + 232 := by
    cases copy <;> decide +kernel
  omega

theorem store_boundary (copy : Copy) {boundary : ReturnBoundary} (h : ¬ InProgram boundary.rip) :
    ∀ p : BitVec 64, (storeAddress copy).toNat ≤ p.toNat →
      p.toNat ≤ (restoreAddress copy).toNat → p ≠ boundary.rip := by
  intro p hlo hhi heq
  have hle : (restoreAddress copy).toNat ≤ (returnAddress copy).toNat := by
    cases copy <;> decide +kernel
  exact h (heq ▸ store_restore_inProgram copy hlo (by omega))

theorem restore_boundary (copy : Copy) {boundary : ReturnBoundary}
    (h : ¬ InProgram boundary.rip) :
    ∀ k ≤ 6, restorePopPC copy k ≠ boundary.rip := by
  intro k hk heq
  have hrange : (storeAddress copy).toNat ≤ (restorePopPC copy k).toNat ∧
      (restorePopPC copy k).toNat ≤ (returnAddress copy).toNat := by
    have hclosed : ∀ i : Fin 7,
        (storeAddress copy).toNat ≤ (restorePopPC copy i.val).toNat ∧
        (restorePopPC copy i.val).toNat ≤ (returnAddress copy).toNat := by
      cases copy <;> decide +kernel
    exact hclosed ⟨k, by omega⟩
  exact h (heq ▸ store_restore_inProgram copy hrange.1 hrange.2)

end Sha3.Proofs.Permutation.Store
