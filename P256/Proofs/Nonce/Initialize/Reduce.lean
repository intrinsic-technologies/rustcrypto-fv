import P256.Proofs.Nonce.Initialize.Shift.Correct
import P256.Proofs.Nonce.Initialize.Reduce.Setup
import P256.Proofs.Nonce.Initialize.Reduce.Select

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem reduce_correct [Bindings] {initial : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {digest : ByteArray}
    (pre : InitializePre initial boundary orderAddress)
    (bytes : (registerRegion initial .rcx 32).HasBytes initial.external digest) :
    ∃ t, Reduce.Selected initial t boundary (Arith.uint digest % P256.Spec.Operations.domain.n) := by
  obtain ⟨s, ready, rip⟩ := Read.prepare_correct pre bytes
  obtain ⟨u, shifted, urip⟩ := Shift.correct pre ready rip
  obtain ⟨v, selection⟩ := Reduce.setup pre shifted urip
  obtain ⟨t, selected⟩ := Reduce.select_correct pre selection
  have value := Reduce.selected_toNat (Field.readLimbs u (stackPtr u + 8))
  rw [value, Field.readLimbs_toNat shifted.value] at selected
  exact ⟨t, selected⟩

end P256.Proofs.Nonce.Initialize
