import X86Proofs.Program.ReadWrite.Bytes

set_option autoImplicit false

namespace P256.Proofs.Common.Field.SquareRoot

open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem memLoad_setWidth_of_le (mem : Ram) (address : BitVec 64) {m n : Nat}
    (hle : n ≤ m) (hn : n % 8 = 0) :
    (memLoad mem address m).setWidth n = memLoad mem address n := by
  apply storedByte_injective hn
  intro i hi
  have hb : storedByte ((memLoad mem address m).setWidth n) i =
      storedByte (memLoad mem address m) i := by
    simp only [storedByte_eq_extract, BitVec.extractLsb'_setWidth_of_le (start := 8*i) (len := 8) (w' := n) (by omega)]
  rw [hb, storedByte_memLoad _ _ _ (by omega), storedByte_memLoad _ _ _ hi]

end P256.Proofs.Common.Field.SquareRoot
