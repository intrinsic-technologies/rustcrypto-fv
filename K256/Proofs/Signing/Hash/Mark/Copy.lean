import K256.Proofs.Sec1.Parser.Result.Copy
import K256.Proofs.Sec1.Wrapper.Copy.Execution

namespace K256.Proofs.Signing.Hash.Mark

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine

abbrev copied (m : Ram) (sp : BitVec 64) := memCopy m (sp + 8) (sp + 488) 104

abbrev marked (m : Ram) (sp : BitVec 64) (n : Nat) :=
  memStore (copied m sp) (sp + 8 + BitVec.ofNat 64 n) (128 : BitVec 8)

abbrev pushed (m : Ram) (sp : BitVec 64) (n : Nat) :=
  memStore (marked m sp n) (sp - 8) (0x105612 : BitVec 64)

theorem copied_load (m : Ram) (sp : BitVec 64) (off width : Nat)
    (within : off + width / 8 ≤ 104) :
    memLoad (copied m sp) (sp + BitVec.ofNat 64 (8 + off)) width =
      memLoad m (sp + BitVec.ofNat 64 (488 + off)) width := by
  simp only [BitVec.ofNat_add, ← BitVec.add_assoc]
  exact Sec1.Parser.Result.memLoad_memCopy _ _ _ (by decide) within

end K256.Proofs.Signing.Hash.Mark
