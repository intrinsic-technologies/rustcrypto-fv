import P256.Proofs.Signing.Core.Iteration.Components.Constructor.Serialize.Correct

import P256.Proofs.SecretKeyFromBytes.Encoding

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Components.Constructor.Serialize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program (CalleePre CalleeResult)
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open P256.Proofs.SecretKeyFromBytes.Encoding (natToOctets_size natToOctets_getElem)

theorem serialize_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {d reserve : Nat} (pre : CalleePre s boundary 0x115960 32 32 reserve)
    (scalar : Nat256At s (s.regValue .rsi) d) :
    ∃ t, CalleeResult s t boundary 32 reserve ∧
      (registerRegion s .rdi 32).HasBytes t.external (Standards.SECG.ECC.Encoding.natToOctets 32 d) := by
  obtain ⟨t, result, bytes, _, _⟩ := scalar_encode_correct pre scalar
  refine ⟨t, result, natToOctets_size 32 d, ?_⟩
  intro i
  have hi : i.val < 32 := by simpa only [natToOctets_size] using i.isLt
  change t.external[BitVec.ofNat 64 ((s.regValue .rdi).toNat + i.val)]? = _
  rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    ByteArray.getElem_eq_getElem_data, natToOctets_getElem 32 d i.val hi]
  exact bytes i.val hi

end P256.Proofs.Signing.Core.Iteration.Components.Constructor.Serialize
