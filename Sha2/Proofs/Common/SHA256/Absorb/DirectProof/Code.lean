import Sha2.Proofs.Common.SHA256.Absorb.Direct

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb.Direct

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem loaded_code_inProgram {s : RamState} {code : CodeMap}
    (witness : ProgramLoaded s) (loaded : ∀ t, ProgramLoaded t → CodeIn code t)
    {address : BitVec 64} {byte : UInt8} (member : (address, byte) ∈ code) :
    InProgram address := by
  apply Classical.byContradiction
  intro outside
  let t : RamState := {s with external := s.external.erase address}
  have valid : ProgramLoaded t := by
    intro a b present
    have different : address ≠ a := by
      intro same
      apply outside
      exact same ▸ (show InProgram a from ⟨b, present⟩)
    change (s.external.erase address)[a]? = some b
    rw [Std.ExtHashMap.getElem?_erase, ite_eq_right (by simpa only [beq_iff_eq] using different)]
    exact witness a b present
  have stored := (loaded t valid (address, byte) member).2
  change (s.external.erase address)[address]? = some byte at stored
  rw [Std.ExtHashMap.getElem?_erase_self] at stored
  contradiction

end Sha2.Proofs.Common.SHA256.Absorb.Direct
