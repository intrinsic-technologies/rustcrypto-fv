import Hkdf.Proofs.Program
import X86Proofs.Program.Execution

set_option autoImplicit false

namespace Hkdf.Proofs.Common.Memory

open Hkdf.Spec Hkdf.Proofs.Program Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem memReadable_sub {s : RamState} {a : BitVec 64} {len : Nat}
    (h : MemReadable s a len) (offset count : Nat) (hb : offset + count ≤ len) :
    MemReadable s (a + BitVec.ofNat 64 offset) count := by
  refine ⟨?_, ?_⟩
  · have hlow := h.low
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · intro i hi
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact h.mem (offset + i) (by omega)

end Hkdf.Proofs.Common.Memory
