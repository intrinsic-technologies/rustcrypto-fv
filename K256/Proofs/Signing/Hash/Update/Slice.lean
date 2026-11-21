import K256.Proofs.Signing.Hash.State

namespace K256.Proofs.Signing.Hash

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
open K256.Proofs.Verify.Hash

namespace Update

abbrev target (size : Nat) : Label :=
  if size < 64 then .l1054c0 else .l105509

structure Slice (sp src : BitVec 64) (n : Nat) (a : Values Value Reg.count) : Prop where
  rsp : a[4] = ⟨64, sp⟩
  direction : a[22] = ⟨1, 0⟩
  limit : a[3] = ⟨64, sp + 1152⟩
  size : a[5] = ⟨64, BitVec.ofNat 64 n⟩
  source : a[6] = ⟨64, src⟩
  buffered : a[12] = ⟨64, 0⟩
  rest : a[13] = ⟨64, BitVec.ofNat 64 n - 64⟩
  slice : a[14] = ⟨64, sp + 1136⟩
  memcpy : a[15] = ⟨64, 0x12a820⟩

end Update
end K256.Proofs.Signing.Hash
