import K256.Proofs.Sec1.Parser.Result.Copy
import K256.Proofs.Sec1.Wrapper.Copy.Execution

namespace K256.Proofs.Verify.Hash.Mark

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine

abbrev copied (m : Ram) (sp : BitVec 64) := memCopy m (sp + 8) (sp + 248) 104

abbrev marked (m : Ram) (sp : BitVec 64) (n : Nat) :=
  memStore (copied m sp) (sp + 8 + BitVec.ofNat 64 n) (128 : BitVec 8)

abbrev pushed (m : Ram) (sp : BitVec 64) (n : Nat) :=
  memStore (marked m sp n) (sp - 8) (0x1031c3 : BitVec 64)

theorem copied_load (m : Ram) (sp : BitVec 64) (off width : Nat)
    (within : off + width / 8 ≤ 104) :
    memLoad (copied m sp) (sp + BitVec.ofNat 64 (8 + off)) width =
      memLoad m (sp + BitVec.ofNat 64 (248 + off)) width := by
  simp only [BitVec.ofNat_add, ← BitVec.add_assoc]
  exact Sec1.Parser.Result.memLoad_memCopy _ _ _ (by decide) within

theorem remaining_xor (n : Nat) (h : n < 64) :
    BitVec.ofNat 64 n ^^^ 63 = BitVec.ofNat 64 (63 - n) := by
  have all : ∀ i : Fin 64, BitVec.ofNat 64 i.val ^^^ 63 = BitVec.ofNat 64 (63 - i.val) := by
    decide +kernel
  exact all ⟨n, h⟩

end K256.Proofs.Verify.Hash.Mark
