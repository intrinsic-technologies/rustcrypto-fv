import P256.Proofs.Nonce.UpdateValue.State
import P256.Proofs.Program.ScalarFrame.Output

set_option autoImplicit false

namespace P256.Proofs.Nonce.UpdateValue

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem state_readable [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {state : State} (pre : UpdateValuePre initial boundary state)
    (frame : FrameState initial s) {offset len : Nat} (bound : offset + len ≤ 64) :
    MemReadable s (initial.regValue .rdi + BitVec.ofNat 64 offset) len := by
  apply readable_of_grow ?_ frame.allocated
  have low : (initial.regValue .rdi).toNat + 64 < 2^32 := pre.stateBounded
  have address : (initial.regValue .rdi + BitVec.ofNat 64 offset).toNat =
      (initial.regValue .rdi).toNat + offset := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : offset < 2^64),
      Nat.mod_eq_of_lt (by omega)]
  apply memoryRegion_memReadable pre.stateBounded pre.stateAllocated
  · rw [address]
    change (initial.regValue .rdi).toNat ≤ _
    omega
  · rw [address]
    change (initial.regValue .rdi).toNat + offset + len ≤ (initial.regValue .rdi).toNat + 64
    omega

end P256.Proofs.Nonce.UpdateValue
