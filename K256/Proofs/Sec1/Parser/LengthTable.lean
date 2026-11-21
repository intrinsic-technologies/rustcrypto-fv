import K256.Spec.Program.Extracted.Image
import K256.Proofs.Common.Refine.Lemma.SysVEntry
import X86Proofs.Core.Shift

namespace K256.Proofs.Sec1.Parser

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.Lift K256.Proofs.Refine Prelude
open K256.Spec.Program

def validTag (t : BitVec 8) : Prop := t = 0 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5

instance (t : BitVec 8) : Decidable (validTag t) := by unfold validTag; infer_instance

theorem tagMask (t : BitVec 8) :
    ((61 : BitVec 8) >>> shiftCount 8 t &&&
      (if (t.setWidth 64).toNat < 6 then 1 else 0) = 1) ↔ validTag t := by
  revert t
  decide +kernel

theorem validTag_lt {t : BitVec 8} (h : validTag t) : t.toNat < 6 := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;> decide

def lengthTable : Vector (BitVec 64) 6 := #v[1, 0, 33, 33, 65, 33]

set_option maxRecDepth 4096 in
theorem lengthTable_load {mem : Ram}
    (loaded : ∀ x ∈ Extracted.programImage, mem[x.1]? = some x.2) (i : Fin 6) :
    let a := wordAddr 0x202548 64 i.val
    Readable mem a 8 ∧ memLoad mem a 64 = lengthTable[i] := by
  let sec : ImageSection := ⟨Extracted.rodataAddress, Extracted.rodataBytes⟩
  have hs : sec ∈ Extracted.programSections := by simp [sec, Extracted.programSections]
  have contents : ∀ j : Fin 6,
      chunkedRead sec.bytes (0x2548 + 8 * j.val) 8 = wordBytes lengthTable[j] := by
    decide +kernel
  have inImage := codeRange_sub_section hs (0x2548 + 8 * i.val) 8 (contents i)
    (by decide +kernel) (by
      have sz : sec.bytes.size = 15952 := by decide +kernel
      rw [sz]
      omega)
    (p := wordAddr 0x202548 64 i.val) (by finite_cases i <;> rfl)
  have bytes : Bytes mem (wordAddr 0x202548 64 i.val) 8 (storedByte lengthTable[i]) := by
    intro j hj
    apply loaded (wordAddr 0x202548 64 i.val + BitVec.ofNat 64 j, storedByte lengthTable[i] j)
    apply inImage
    have h := mem_codeRange (wordAddr 0x202548 64 i.val) (wordBytes lengthTable[i]) j
      (by simp only [wordBytes, List.length_ofFn]; omega)
    simpa only [wordBytes, List.getElem_ofFn] using h
  exact ⟨⟨by exact (by decide : ∀ j : Fin 6, (wordAddr 0x202548 64 j.val).toNat + 8 ≤ 2 ^ 32) i, fun j hj => by rw [bytes j hj]; rfl⟩,
    bytes.memLoad (by decide) (by decide)⟩

theorem lengthTable_address (t : BitVec 64) :
    t <<< 3 + 0x202548 = wordAddr 0x202548 64 t.toNat := by
  simp only [wordAddr]
  bv_omega

end K256.Proofs.Sec1.Parser
