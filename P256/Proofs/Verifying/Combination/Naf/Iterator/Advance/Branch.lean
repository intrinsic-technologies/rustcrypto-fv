import P256.Proofs.Verifying.Combination.Naf.Iterator.Advance.Steps

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Iterator.Advance

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar

variable [Bindings] {s : RamState} {boundary : ReturnBoundary}

theorem branch8 {offset : Nat} (cc : BitVec 4) (disp : BitVec 8) (taken : Bool)
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (rip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 offset)
    (condition : condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = taken)
    (size : offset + 2 ≤ 118431)
    (code : Extracted.textBytes.toListFrom offset 2 = jccOpcode8 cc :: immBytes 8 disp)
    (low : (branchTarget (Extracted.textAddress + BitVec.ofNat 64 offset) 2 (disp.signExtend 64)).toNat < 2^32)
    (next : (if taken then branchTarget (Extracted.textAddress + BitVec.ofNat 64 offset) 2 (disp.signExtend 64)
      else Extracted.textAddress + BitVec.ofNat 64 offset + 2) ≠ boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = (if taken then branchTarget (Extracted.textAddress + BitVec.ofNat 64 offset) 2 (disp.signExtend 64)
        else Extracted.textAddress + BitVec.ofNat 64 offset + 2) ∧ AgreesExcept [.rip] s t := by
  obtain ⟨t, run, readyT, loadedT, effect⟩ := step_nomem
    (jcc_rel8_effect_step _ cc disp) ready loaded ⟨rip, fun _ => low⟩ size code
    (by simpa only [jccEffect, branchEffect, condition, BitVec.ofNat_eq_ofNat] using next)
    (by simp [jccEffect, Component.Covers])
  exact ⟨t, run, readyT, loadedT, by simpa only [jccEffect, branchEffect, condition, BitVec.ofNat_eq_ofNat] using effect.rip,
    effect.agrees⟩

theorem branch32 {offset : Nat} (cc : BitVec 4) (disp : BitVec 32) (taken : Bool)
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (rip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 offset)
    (condition : condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = taken)
    (size : offset + 6 ≤ 118431)
    (code : Extracted.textBytes.toListFrom offset 6 = 0x0f :: jccOpcode32 cc :: immBytes 32 disp)
    (low : (branchTarget (Extracted.textAddress + BitVec.ofNat 64 offset) 6 (disp.signExtend 64)).toNat < 2^32)
    (next : (if taken then branchTarget (Extracted.textAddress + BitVec.ofNat 64 offset) 6 (disp.signExtend 64)
      else Extracted.textAddress + BitVec.ofNat 64 offset + 6) ≠ boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = (if taken then branchTarget (Extracted.textAddress + BitVec.ofNat 64 offset) 6 (disp.signExtend 64)
        else Extracted.textAddress + BitVec.ofNat 64 offset + 6) ∧ AgreesExcept [.rip] s t := by
  obtain ⟨t, run, readyT, loadedT, effect⟩ := step_nomem
    (jcc_rel32_effect_step _ cc disp) ready loaded ⟨rip, fun _ => low⟩ size code
    (by simpa only [jccEffect, branchEffect, condition, BitVec.ofNat_eq_ofNat] using next)
    (by simp [jccEffect, Component.Covers])
  exact ⟨t, run, readyT, loadedT, by simpa only [jccEffect, branchEffect, condition, BitVec.ofNat_eq_ofNat] using effect.rip,
    effect.agrees⟩

end P256.Proofs.Verifying.Combination.Naf.Iterator.Advance
