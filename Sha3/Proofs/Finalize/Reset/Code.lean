import Sha3.Proofs.Finalize.Reset.Prefix
import Sha3.Proofs.Permutation.Code
import X86Proofs.Program.ReadWrite.Bytes

namespace Sha3.Proofs.Finalize.Reset

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

def jumpDisplacement (v : Variant) (keccak : Bool := false) (fullState : Bool := false) : BitVec 32
    :=
  (0x200188 - (epilogueAddress (keccak := keccak) (fullState := fullState) v true + 23)).setWidth 32

def tailBytes (v : Variant) (keccak : Bool := false) (fullState : Bool := false) : List UInt8 :=
  prefixBytes ++ [0xff, 0x25] ++ immBytes 32 (jumpDisplacement (keccak := keccak) (fullState :=
      fullState) v)

theorem tail_image (v : Variant) (keccak : Bool := false) (fullState : Bool := false) :
    let p := epilogueAddress (keccak := keccak) (fullState := fullState) v true
    let offset := p.toNat - Extracted.textAddress.toNat
    p = Extracted.textAddress + BitVec.ofNat 64 offset ∧
      offset + (tailBytes (keccak := keccak) (fullState := fullState) v).length ≤
          Extracted.textBytes.size ∧
      Extracted.textBytes.toListFrom offset (tailBytes (keccak := keccak) (fullState := fullState)
          v).length = tailBytes (keccak := keccak) (fullState := fullState) v := by
  cases v <;> cases keccak <;> cases fullState <;> decide +kernel

theorem tail_subset (v : Variant) (keccak : Bool := false) (fullState : Bool := false) :
    ∀ x ∈ codeRange (epilogueAddress (keccak := keccak) (fullState := fullState) v true) (tailBytes
        (keccak := keccak) (fullState := fullState) v), x ∈ Extracted.programImage := by
  obtain ⟨hp, hbound, hslice⟩ := tail_image (keccak := keccak) (fullState := fullState) v
  rw [hp]
  exact textSlice_subset_programImage hbound hslice

theorem prefix_subset (v : Variant) (keccak : Bool := false) (fullState : Bool := false) :
    ∀ x ∈ codeRange (epilogueAddress (keccak := keccak) (fullState := fullState) v true)
        prefixBytes, x ∈ Extracted.programImage := by
  intro x hx
  apply tail_subset (keccak := keccak) (fullState := fullState) v x
  exact codeRange_mem_of_take (all := tailBytes (keccak := keccak) (fullState := fullState) v) (by
      cases v <;> cases keccak <;> cases fullState <;> decide +kernel) x hx

theorem jump_subset (v : Variant) (keccak : Bool := false) (fullState : Bool := false) :
    ∀ x ∈ codeRange (epilogueAddress (keccak := keccak) (fullState := fullState) v true + 17)
      ([0xff, 0x25] ++ immBytes 32 (jumpDisplacement (keccak := keccak) (fullState := fullState)
          v)), x ∈ Extracted.programImage := by
  intro x hx
  apply tail_subset (keccak := keccak) (fullState := fullState) v x
  exact codeRange_mem_of_drop (all := tailBytes (keccak := keccak) (fullState := fullState) v) 17
      (by cases v <;> cases keccak <;> cases fullState <;> decide +kernel) x hx

theorem jump_pointer (v : Variant) (keccak : Bool := false) (fullState : Bool := false) :
    (epilogueAddress (keccak := keccak) (fullState := fullState) v true + 17) + 6 +
        (jumpDisplacement (keccak := keccak) (fullState := fullState) v).signExtend 64 = 0x200188 :=
        by
  cases v <;> cases keccak <;> cases fullState <;> decide +kernel

theorem prefix_boundary (boundary : ReturnBoundary) (hboundary : ¬ InProgram boundary.rip)
    (v : Variant) (keccak : Bool := false) (fullState : Bool := false) :
    ∀ x ∈ [epilogueAddress (keccak := keccak) (fullState := fullState) v true + 5, epilogueAddress
        (keccak := keccak) (fullState := fullState) v true + 8,
      epilogueAddress (keccak := keccak) (fullState := fullState) v true + 10, epilogueAddress
          (keccak := keccak) (fullState := fullState) v true + 14,
      epilogueAddress (keccak := keccak) (fullState := fullState) v true + 15, epilogueAddress
          (keccak := keccak) (fullState := fullState) v true + 17], x ≠ boundary.rip := by
  intro x hx he
  apply hboundary
  rw [← he]
  have hcases : ∀ off ∈ ([5, 8, 10, 14, 15, 17] : List Nat),
      InProgram (epilogueAddress (keccak := keccak) (fullState := fullState) v true + BitVec.ofNat
          64 off) := by
    intro off hoff
    have hm : (epilogueAddress (keccak := keccak) (fullState := fullState) v true + BitVec.ofNat 64
        off, (tailBytes (keccak := keccak) (fullState := fullState) v)[off]'(by
        cases v <;> cases keccak <;> cases fullState <;> simp_all [tailBytes, prefixBytes] <;>
            omega)) ∈ Extracted.programImage :=
      tail_subset (keccak := keccak) (fullState := fullState) v _ (mem_codeRange _ _ off (by
        cases v <;> cases keccak <;> cases fullState <;> simp_all [tailBytes, prefixBytes] <;>
            omega))
    exact ⟨_, hm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hcases _ (by simp)

theorem memset_pointer_data {s : RamState} (hcode : CodeIn Extracted.programImage s) :
    MemReadable s 0x200188 8 ∧ (Operand.mem 0x200188 : Operand 64).read s = 0x106a20 := by
  have loaded : ProgramLoaded s := fun address byte hin ↦ (hcode (address, byte) hin).2
  have hb : ∀ i : Fin 8,
      s.external[(0x200188 : BitVec 64) + BitVec.ofNat 64 i.val]? =
        some (storedByte (0x106a20 : BitVec 64) i.val) := by
    intro i
    exact programLoaded_fetchByte loaded
      ((by decide +kernel : ∀ i : Fin 8,
        Extracted.programSections.fetchByte ((0x200188 : BitVec 64) + BitVec.ofNat 64 i.val) =
          some (storedByte (0x106a20 : BitVec 64) i.val)) i)
  refine ⟨⟨by decide +kernel, ?_⟩, ?_⟩
  · intro i hi
    rw [hb ⟨i, hi⟩]
    rfl
  · change memLoad s.external 0x200188 64 = _
    rw [← memLoad_memStore (∅ : Ram) (0x200188 : BitVec 64) (by decide) (by decide)
      (0x106a20 : BitVec 64)]
    apply memLoad_congr
    intro i hi
    simp only [memByte, PhysicalMemory.read, hb ⟨i, hi⟩,
      memStore_getElem?_self _ _ _ (by decide) i hi]

end Sha3.Proofs.Finalize.Reset
