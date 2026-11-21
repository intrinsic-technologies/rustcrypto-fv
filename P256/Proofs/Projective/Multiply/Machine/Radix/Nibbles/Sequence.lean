import P256.Proofs.Projective.Multiply.Machine.Radix.Nibbles.Run

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Radix

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Spec.Program.Routines
open ProjectiveRadix
open Recenter (rawDigit)

theorem pairs_run [Bindings] {s t : RamState} {boundary : ReturnBoundary} {d n pc : Nat}
    (pre : CalleePre s boundary 0x10b720 32 65 136) (state : ExtractionState s t d n)
    (positive : 0 < n) (count : Nat) (hn : n+count ≤ 32)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 pc)
    (code : ∀ i, i < count → Extracted.textBytes.toListFrom (pc+21*i) 21 =
      pairBytes (BitVec.ofNat 8 (111-(n+i))) (BitVec.ofNat 8 (8+2*(n+i)))
        (BitVec.ofNat 8 (9+2*(n+i))))
    (bound : pc + 21*count < 118431) :
    ∃ fuel u, Advances boundary fuel t u ∧ ExtractionState s u d (n+count) ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 (pc+21*count) ∧
      AgreesExcept (digitComponents s) t u := by
  induction count with
  | zero => exact ⟨0,t,.refl _,state,rip,.refl _ _⟩
  | succ count ih =>
    obtain ⟨fuel,u,run,st,ip,agrees⟩ := ih (by omega) (fun i hi => code i (by omega)) (by omega)
    obtain ⟨fuel',v,run',st',ip',agrees'⟩ := pair_run pre st (by omega) (by omega) ip
      (code count (by omega)) (by omega)
    refine ⟨fuel+fuel',v,run.trans run',?_,?_,?_⟩
    · simpa only [Nat.add_assoc] using st'
    · simpa only [Nat.mul_succ,Nat.add_assoc] using ip'
    · exact (agrees.trans agrees').mono (by simp)

end P256.Proofs.Projective.Multiply.Machine.Radix
