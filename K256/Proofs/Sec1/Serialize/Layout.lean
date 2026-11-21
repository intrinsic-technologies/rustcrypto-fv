import K256.Proofs.Common.Image
import K256.Proofs.Common.Refine.Lemma.Region
import K256.Proofs.Common.Refine.Lemma.Store

namespace K256.Proofs.Sec1.Serialize

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.Refine

private theorem writable_section_apart {mem : Ram} {a : BitVec 64} {n : Nat}
    {sec : ImageSection} (included : sec ∈ Extracted.programSections)
    (h : Writable Extracted.programImage mem a n) (hn : 0 < n) (hs : 0 < sec.bytes.size) :
    a.toNat + n ≤ sec.address.toNat ∨ sec.address.toNat + sec.bytes.size ≤ a.toNat := by
  apply Classical.byContradiction
  intro neither
  let p := max a.toNat sec.address.toNat
  have hi : p - sec.address.toNat < sec.bytes.toList.length := by
    rw [chunked_toList_length]
    dsimp only [p]
    omega
  let i := p - sec.address.toNat
  let entry := (sec.address + BitVec.ofNat 64 i, sec.bytes.toList[i])
  have inCode : entry ∈ Extracted.programImage :=
    List.mem_flatMap.mpr ⟨sec, included, mem_codeRange _ _ _ hi⟩
  apply h.notCode entry inCode (p - a.toNat) (by dsimp only [p]; omega)
  change sec.address + BitVec.ofNat 64 (p - sec.address.toNat) = _
  rw [← ofNat_toNat_add, ← ofNat_toNat_add a]
  congr 1
  dsimp only [p]
  omega

theorem writable_text_apart {mem : Ram} {a : BitVec 64} {n : Nat}
    (h : Writable Extracted.programImage mem a n) (hn : 0 < n) :
    a.toNat + n ≤ 0x100000 ∨ 0x12a9bf ≤ a.toNat := by
  have sz := Common.textBytes_size
  have e := writable_section_apart (sec := ⟨Extracted.textAddress, Extracted.textBytes⟩)
    (.head _) h hn (by change 0 < Extracted.textBytes.size; omega)
  change a.toNat + n ≤ 0x100000 ∨ 0x100000 + Extracted.textBytes.size ≤ a.toNat at e
  omega

theorem writable_copy_slot_apart {mem : Ram} {a : BitVec 64} {n : Nat}
    (h : Writable Extracted.programImage mem a n) (hn : 0 < n) :
    a.toNat + n ≤ 0x203dd0 ∨ 0x203dd0 + 8 ≤ a.toNat := by
  have sz := Common.rodataBytes_size
  have e := writable_section_apart (sec := ⟨Extracted.rodataAddress, Extracted.rodataBytes⟩)
    (.tail _ (.head _)) h hn (by change 0 < Extracted.rodataBytes.size; omega)
  change a.toNat + n ≤ 0x200000 ∨ 0x200000 + Extracted.rodataBytes.size ≤ a.toNat at e
  omega

end K256.Proofs.Sec1.Serialize
