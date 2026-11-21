import K256.Proofs.Common.Lift.Footprint

namespace K256.Proofs.Generate.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.Lift

theorem CallPre.of_stateOf {p : BitVec 64} {len : Nat} {target : RamState → BitVec 64}
    {L : List Reg} (hsp : ∀ s, pushAddr (stateOf p (entriesOf L s) s.external) = pushAddr s)
    (ht : ∀ s, target (stateOf p (entriesOf L s) s.external) = target s) :
    ∀ s : RamState, s.RIP = p → CallPre p len target (stateOf p (entriesOf L s) s.external) →
      CallPre p len target s :=
  fun s hrip h => ⟨StorePre.of_stateOf hsp s hrip h.1, ht s ▸ h.2⟩

end K256.Proofs.Generate.LIR
