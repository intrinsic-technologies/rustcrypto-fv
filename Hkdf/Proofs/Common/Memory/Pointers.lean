import Hkdf.Proofs.Common.Machine.Entry
import X86Proofs.Program.ReadWrite.Bytes

set_option autoImplicit false

namespace Hkdf.Proofs.Common.Memory

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Machine (rodataBytes_size)

theorem rodata_loaded {s : RamState} (loaded : ProgramLoaded s) {offset : Nat}
    (bound : offset < 4968) :
    s.external[Extracted.rodataAddress + BitVec.ofNat 64 offset]? =
      some (Extracted.rodataBytes.toList[offset]'(by
        simpa only [chunked_toList_length, rodataBytes_size] using bound)) := by
  apply loaded
  apply List.mem_flatMap.mpr
  refine ⟨⟨Extracted.rodataAddress, Extracted.rodataBytes⟩,
    by simp [Extracted.programSections], ?_⟩
  exact mem_codeRange _ _ _ _

theorem memset_pointer {s : RamState} (loaded : ProgramLoaded s) :
    MemReadable s 0x201338 8 ∧ (Operand.mem 0x201338 : Operand 64).read s = 0x10dd10 := by
  have bytes : ∀ i : Fin 8,
      Extracted.rodataBytes.toList[4920 + i.val]'(by
        rw [chunked_toList_length, rodataBytes_size]
        omega) = storedByte (0x10dd10 : BitVec 64) i.val := by decide +kernel
  have stored : Bytes s.external 0x201338 8 (storedByte (0x10dd10 : BitVec 64)) := by
    intro i hi
    have byte := rodata_loaded loaded (offset := 4920 + i) (by omega)
    rw [bytes ⟨i, hi⟩] at byte
    simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, Extracted.rodataAddress,
      BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using byte
  exact ⟨stored.readable (by decide), stored.memLoad (by decide) (by decide)⟩

theorem memcpy_pointer {s : RamState} (loaded : ProgramLoaded s) :
    MemReadable s 0x201318 8 ∧ (Operand.mem 0x201318 : Operand 64).read s = 0x10dd60 := by
  have bytes : ∀ i : Fin 8,
      Extracted.rodataBytes.toList[4888 + i.val]'(by
        rw [chunked_toList_length, rodataBytes_size]
        omega) = storedByte (0x10dd60 : BitVec 64) i.val := by decide +kernel
  have stored : Bytes s.external 0x201318 8 (storedByte (0x10dd60 : BitVec 64)) := by
    intro i hi
    have byte := rodata_loaded loaded (offset := 4888 + i) (by omega)
    rw [bytes ⟨i, hi⟩] at byte
    simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, Extracted.rodataAddress,
      BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using byte
  exact ⟨stored.readable (by decide), stored.memLoad (by decide) (by decide)⟩

end Hkdf.Proofs.Common.Memory
