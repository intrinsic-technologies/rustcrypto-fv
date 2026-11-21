import Sha3.Proofs.Update.Layout
import Sha3.Proofs.Image

namespace Sha3.Proofs.Update

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

def prologueBytes : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x50,
    0x48, 0x89, 0xd3, 0x49, 0x89, 0xf7, 0x0f, 0xb6, 0x07]

def cursorStoreBytes : List UInt8 := [0x88, 0x0f]

def epilogueBytes : List UInt8 :=
  [0x48, 0x83, 0xc4, 8, 0x5b, 0x41, 0x5c, 0x41, 0x5d,
    0x41, 0x5e, 0x41, 0x5f, 0x5d, 0xc3]

def epilogueCode (p : BitVec 64) : CodeMap := codeRange p epilogueBytes

theorem prologueCode_subset (v : Variant) :
    ∀ x ∈ codeRange v.updateAddress prologueBytes, x ∈ Extracted.programImage := by
  cases v
  · exact textSlice_subset_programImage (offset := 0x8a0) (len := 20)
      (by decide +kernel) (by decide +kernel)
  · exact textSlice_subset_programImage (offset := 0x580) (len := 20)
      (by decide +kernel) (by decide +kernel)
  · exact textSlice_subset_programImage (offset := 0x2b0) (len := 20)
      (by decide +kernel) (by decide +kernel)
  · exact textSlice_subset_programImage (offset := 0x0) (len := 20)
      (by decide +kernel) (by decide +kernel)

theorem cursorStoreCode_subset (v : Variant) :
    ∀ x ∈ codeRange (cursorWriteAddress v) cursorStoreBytes, x ∈ Extracted.programImage := by
  cases v
  · exact textSlice_subset_programImage (offset := 0xba3) (len := 2)
      (by decide +kernel) (by decide +kernel)
  · exact textSlice_subset_programImage (offset := 0x883) (len := 2)
      (by decide +kernel) (by decide +kernel)
  · exact textSlice_subset_programImage (offset := 0x563) (len := 2)
      (by decide +kernel) (by decide +kernel)
  · exact textSlice_subset_programImage (offset := 0x293) (len := 2)
      (by decide +kernel) (by decide +kernel)

theorem epilogueCode_subset (v : Variant) :
    ∀ x ∈ epilogueCode (cursorWriteAddress v + 2), x ∈ Extracted.programImage := by
  cases v
  · exact textSlice_subset_programImage (offset := 0xba5) (len := 15)
      (by decide +kernel) (by decide +kernel)
  · exact textSlice_subset_programImage (offset := 0x885) (len := 15)
      (by decide +kernel) (by decide +kernel)
  · exact textSlice_subset_programImage (offset := 0x565) (len := 15)
      (by decide +kernel) (by decide +kernel)
  · exact textSlice_subset_programImage (offset := 0x295) (len := 15)
      (by decide +kernel) (by decide +kernel)

theorem prologuePC_inProgram (v : Variant) {k : Nat} (hk : k < 20) :
    InProgram (v.updateAddress + BitVec.ofNat 64 k) := by
  have hl : k < prologueBytes.length := hk
  exact ⟨prologueBytes[k], prologueCode_subset v _ (mem_codeRange _ _ k hl)⟩

theorem epiloguePC_inProgram (v : Variant) {k : Nat} (hk : k < 15) :
    InProgram (cursorWriteAddress v + 2 + BitVec.ofNat 64 k) := by
  have hl : k < epilogueBytes.length := hk
  exact ⟨epilogueBytes[k], epilogueCode_subset v _ (mem_codeRange _ _ k hl)⟩

end Sha3.Proofs.Update
