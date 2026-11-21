import P256.Proofs.Nonce.Fill.Generate.Prepare
import P256.Proofs.Nonce.Fill.Generate.Value
import P256.Proofs.Nonce.Fill.Generate.Copy
import P256.Proofs.Nonce.Fill.Generate.Finish

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem generate [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {original state : State}
    (pre : Pre initial boundary orderAddress original)
    (input : Loop initial s orderAddress state) :
    ∃ fuel t, 0 < fuel ∧ Advances boundary fuel s t ∧
      Generated initial t orderAddress state := by
  obtain ⟨a, first, prepared⟩ := Generate.prepare pre input
  obtain ⟨valueFuel, b, second, hasValue⟩ := Generate.value pre prepared
  obtain ⟨copyFuel, c, third, copied⟩ := Generate.copy pre hasValue
  obtain ⟨t, fourth, generated⟩ := Generate.finish pre copied
  exact ⟨7 + valueFuel + copyFuel + 4, t, by omega,
    ((first.trans second).trans third).trans fourth, generated⟩

end P256.Proofs.Nonce.Fill
