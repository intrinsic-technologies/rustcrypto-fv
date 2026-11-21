import P256.Proofs.Sec1.Decompress.Convert.Code
import P256.Proofs.Program.Code

set_option autoImplicit false

open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice)

namespace P256.Proofs.Sec1.SquareRoot.Montgomery

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def Entry (entry : BitVec 64) : Prop := entry = 0x1145e0 ∨ entry = 0x108f70

def routineOffset (entry : BitVec 64) : Nat :=
  if entry = 0x1145e0 then 0x145e0 else 0x8f70

theorem entry_address {entry : BitVec 64} (hentry : Entry entry) :
    Extracted.textAddress + BitVec.ofNat 64 (routineOffset entry) = entry := by
  rcases hentry with rfl | rfl <;> decide +kernel

theorem routineOffset_bound {entry : BitVec 64} (hentry : Entry entry) :
    routineOffset entry + 1469 < 118431 := by
  rcases hentry with rfl | rfl <;> decide +kernel

theorem instruction_bytes {entry : BitVec 64} (hentry : Entry entry)
    (offset count : Nat) (hsize : offset + count ≤ 1469) :
    Extracted.textBytes.toListFrom (routineOffset entry + offset) count =
      Extracted.textBytes.toListFrom (0x145e0 + offset) count := by
  rcases hentry with rfl | rfl
  · rfl
  · exact P256.Proofs.Sec1.Decompress.Convert.conversion_slice_eq offset count hsize

theorem code_slice {entry : BitVec 64} (hentry : Entry entry) {s : RamState}
    (loaded : ProgramLoaded s) (offset : Nat) (bytes : List UInt8)
    (hsize : offset + bytes.length ≤ 1469)
    (hbytes : Extracted.textBytes.toListFrom (0x145e0 + offset) bytes.length = bytes) :
    CodeIn (codeRange (entry + BitVec.ofNat 64 offset) bytes) s := by
  have code := programText_slice (programLoaded_codeIn loaded)
    (routineOffset entry + offset) bytes (by have := routineOffset_bound hentry; omega)
    ((instruction_bytes hentry offset bytes.length hsize).trans hbytes)
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, entry_address hentry] at code
  exact code

theorem instruction_in_program {entry : BitVec 64} (hentry : Entry entry)
    (offset : Nat) (hoffset : offset < 1469) :
    InProgram (entry + BitVec.ofNat 64 offset) := by
  have h := inProgram_of_textOffset (routineOffset entry + offset)
    (by have := routineOffset_bound hentry; omega)
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, entry_address hentry] at h
  exact h

theorem instruction_ne_boundary {entry : BitVec 64} {boundary : ReturnBoundary}
    (hentry : Entry entry) (hout : ¬ InProgram boundary.rip)
    (offset : Nat) (hoffset : offset < 1469) :
    entry + BitVec.ofNat 64 offset ≠ boundary.rip :=
  boundary_ne_program hout (instruction_in_program hentry offset hoffset)

end P256.Proofs.Sec1.SquareRoot.Montgomery
