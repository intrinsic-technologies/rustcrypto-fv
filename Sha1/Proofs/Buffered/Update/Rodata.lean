import Sha1.Spec.Program
import X86Proofs.Program.ReadWrite.Bytes
import X86Proofs.Program.Entry

namespace Sha1.Proofs.Buffered

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem bytes_of_word_code {s : RamState} {address value : BitVec 64}
    (h : CodeIn (codeRange address
      (List.ofFn fun i : Fin 8 ↦ storedByte value i.val)) s) :
    Bytes s.external address 8 (storedByte value) := by
  intro i hi
  have hb := (h _ (mem_codeRange address
    (List.ofFn fun j : Fin 8 ↦ storedByte value j.val) i
    (by simpa only [List.length_ofFn] using hi))).2
  rw [List.getElem_ofFn] at hb
  exact hb

theorem memcpy_pointer_bytes {s : RamState} (h : CodeIn Extracted.programImage s) :
    Bytes s.external 0x200000 8 (storedByte (0x103730#64)) := by
  have hs := h.slice_of_section
    (sec := ⟨Extracted.rodataAddress, Extracted.rodataBytes⟩)
    (by simp [Extracted.programSections]) 0x0 8 (by decide +kernel)
  have he : Extracted.rodataBytes.toListFrom 0x0 8 =
      List.ofFn (fun i : Fin 8 ↦ storedByte (0x103730#64) i.val) := by decide +kernel
  apply bytes_of_word_code
  simpa [he, Extracted.rodataAddress] using hs

theorem memset_pointer_bytes {s : RamState} (h : CodeIn Extracted.programImage s) :
    Bytes s.external 0x200008 8 (storedByte (0x1036e0#64)) := by
  have hs := h.slice_of_section
    (sec := ⟨Extracted.rodataAddress, Extracted.rodataBytes⟩)
    (by simp [Extracted.programSections]) 0x8 8 (by decide +kernel)
  have he : Extracted.rodataBytes.toListFrom 0x8 8 =
      List.ofFn (fun i : Fin 8 ↦ storedByte (0x1036e0#64) i.val) := by decide +kernel
  apply bytes_of_word_code
  simpa [he, Extracted.rodataAddress] using hs

theorem memcpy_pointer {s : RamState} (h : CodeIn Extracted.programImage s) :
    (Operand.mem 0x200000 : Operand 64).read s = 0x103730 :=
  (memcpy_pointer_bytes h).memLoad (by decide) (by decide)

theorem memset_pointer {s : RamState} (h : CodeIn Extracted.programImage s) :
    (Operand.mem 0x200008 : Operand 64).read s = 0x1036e0 :=
  (memset_pointer_bytes h).memLoad (by decide) (by decide)

theorem memcpy_pointer_readable {s : RamState} (h : CodeIn Extracted.programImage s) :
    MemReadable s 0x200000 8 :=
  (memcpy_pointer_bytes h).readable (by decide)

theorem memset_pointer_readable {s : RamState} (h : CodeIn Extracted.programImage s) :
    MemReadable s 0x200008 8 :=
  (memset_pointer_bytes h).readable (by decide)

end Sha1.Proofs.Buffered
