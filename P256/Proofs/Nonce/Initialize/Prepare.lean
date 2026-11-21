import P256.Proofs.Nonce.Initialize.Prepare.Store
import P256.Proofs.Nonce.Initialize.Prepare.Length

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Prepare

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} (pre : InitializePre s boundary orderAddress) :
    ∃ t, LengthReady s t boundary ∧ t.RIP = 0x107916 := by
  obtain ⟨a, fa, ra, ga⟩ := entry pre
  obtain ⟨b, fb, rb⟩ := head pre fa ra ga
  obtain ⟨c, fc, rc⟩ := load_order pre fb rb
  obtain ⟨d, fd, rd⟩ := store_order pre fc rc
  obtain ⟨e, fe, re⟩ := length_guard pre fd rd
  obtain ⟨f, ff, rf⟩ := scan_correct pre fe re
  exact length_correct pre ff rf

end P256.Proofs.Nonce.Initialize.Prepare
