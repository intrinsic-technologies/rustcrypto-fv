import Md5.Proofs.Machine
import X86Proofs.Program.ReadWrite.Bytes

namespace Md5.Proofs.Buffered

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

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
    Bytes s.external 0x200000 8 (storedByte (0x1024b0#64)) := by
  have hs := h.slice_of_section
    (sec := ⟨Extracted.rodataAddress, Extracted.rodataBytes⟩)
    (by simp [Extracted.programSections]) 0x0 8 (by decide +kernel)
  have he : Extracted.rodataBytes.toListFrom 0x0 8 =
      List.ofFn (fun i : Fin 8 ↦ storedByte (0x1024b0#64) i.val) := by decide +kernel
  apply bytes_of_word_code
  simpa [he, Extracted.rodataAddress] using hs

theorem memset_pointer_bytes {s : RamState} (h : CodeIn Extracted.programImage s) :
    Bytes s.external 0x200008 8 (storedByte (0x102460#64)) := by
  have hs := h.slice_of_section
    (sec := ⟨Extracted.rodataAddress, Extracted.rodataBytes⟩)
    (by simp [Extracted.programSections]) 0x8 8 (by decide +kernel)
  have he : Extracted.rodataBytes.toListFrom 0x8 8 =
      List.ofFn (fun i : Fin 8 ↦ storedByte (0x102460#64) i.val) := by decide +kernel
  apply bytes_of_word_code
  simpa [he, Extracted.rodataAddress] using hs

theorem memcpy_pointer {s : RamState} (h : CodeIn Extracted.programImage s) :
    (Operand.mem 0x200000 : Operand 64).read s = 0x1024b0 :=
  (memcpy_pointer_bytes h).memLoad (by decide) (by decide)

theorem memset_pointer {s : RamState} (h : CodeIn Extracted.programImage s) :
    (Operand.mem 0x200008 : Operand 64).read s = 0x102460 :=
  (memset_pointer_bytes h).memLoad (by decide) (by decide)

theorem memcpy_pointer_readable {s : RamState} (h : CodeIn Extracted.programImage s) :
    MemReadable s 0x200000 8 :=
  (memcpy_pointer_bytes h).readable (by decide)

theorem memset_pointer_readable {s : RamState} (h : CodeIn Extracted.programImage s) :
    MemReadable s 0x200008 8 :=
  (memset_pointer_bytes h).readable (by decide)

end Md5.Proofs.Buffered
