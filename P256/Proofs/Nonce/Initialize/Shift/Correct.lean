import P256.Proofs.Nonce.Initialize.Shift.Result
import P256.Proofs.Nonce.Initialize.Conversions.ShiftZero

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Shift

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem correct [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {digest : ByteArray}
    (pre : InitializePre initial boundary orderAddress)
    (state : Read.ShiftReady initial s boundary digest) (rip : s.RIP = 0x107999) :
    ∃ t, ReducedInput initial t boundary digest ∧ t.RIP = 0x10799e := by
  obtain ⟨entry, frame, cp, count, integer, effect⟩ := call pre state rip
  obtain ⟨t, ret, value⟩ := Conversions.shift_zero_correct cp count integer
  exact ⟨t, result pre state frame effect ret value⟩

end P256.Proofs.Nonce.Initialize.Shift
