import P256.Spec.Program
import X86Proofs.Program.ReadWrite.Bytes

set_option autoImplicit false

namespace P256.Proofs.Program

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86Proofs

theorem memcpy_pointer {t : RamState} (loaded : ProgramLoaded t) :
    MemReadable t 0x2044f8 8 ∧ (Operand.mem 0x2044f8 : Operand 64).read t = 0x11c930 := by
  have hbytes : ∀ i : Fin 8,
      Extracted.programSections.fetchByte (0x2044f8 + BitVec.ofNat 64 i.val) =
        some (storedByte (0x11c930 : BitVec 64) i.val) := by decide +kernel
  have hb : Bytes t.external 0x2044f8 8 (storedByte (0x11c930 : BitVec 64)) :=
    fun i hi => loaded _ _ (hbytes ⟨i, hi⟩)
  exact ⟨hb.readable (by decide), hb.memLoad (by decide) (by decide)⟩

end P256.Proofs.Program
