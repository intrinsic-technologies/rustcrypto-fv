import X86Proofs.Step.Address

set_option autoImplicit false

namespace P256.Proofs.Common.Encoding.Parser.LengthCheck

open X86Proofs X86 X86.Machine X86.UserProcess X86.Helpers
open scoped X86.Runtime.Syntax

theorem readSIB_noBase_run [Bindings] (s t u : RamState) (ip : BitVec 64) (disp : BitVec 32)
    (hsib : (Mem_Fetch ip 8).run s = (.ok 0xcd, t))
    (hdisp : (Mem_Fetch (ip + (1 : BitVec 64)) 32).run t = (.ok disp, u)) (hmode : In64BitMode t) :
    (Read_SIB (rexContext s.DS 0x48) 0 1 ip).run s =
      (.ok (nullDataSegment u.DS, disp.signExtend 64,
        (Operand.reg 1 : Operand 64).read t, 8, ip + (5 : BitVec 64), false), u) := by
  unfold Read_SIB
  refine (specM_bind_run _ _ hsib).trans ?_
  simp (config := { decide := true }) only [X86.Runtime.sliceInclusive,
    X86.Runtime.CheckedSlice.read, slice_eq_pure, pure_bind, Int.reduceToNat, Int.reduceSub,
    Int.reduceAdd, rexContext, legacyContext, Runtime.Unsigned, rexB, rexR, HOr.hOr, OrOp.or, strictOr]
  spec_run [Read_GPR => readGPR64_run _ _ hmode,
    MonadState.get => get_run _,
    Get_Effective_Segment => getEffectiveSegment_run _ _ rfl rfl,
    Mem_Fetch => hdisp]

theorem effectiveAddress_noBase_run [Bindings] (s t u : RamState) (ip : BitVec 64)
    (disp : BitVec 32) (hsib : (Mem_Fetch ip 8).run s = (.ok 0xcd, t))
    (hdisp : (Mem_Fetch (ip + (1 : BitVec 64)) 32).run t = (.ok disp, u)) (hmode : In64BitMode t) :
    (Effective_Address 64 (rexContext s.DS 0x48) 0 4 1 ip).run s =
      (.ok (disp.signExtend 64 + (Operand.reg 1 : Operand 64).read t * (8 : BitVec 64),
        nullDataSegment u.DS, ip + (5 : BitVec 64), false, false), u) := by
  have hs := readSIB_noBase_run s t u ip disp hsib hdisp hmode
  unfold Effective_Address
  simp (config := { decide := true }) only [assert_of_true, ↓reduceIte, pure_bind]
  spec_run [Read_SIB => hs,
    Get_Effective_Segment => getEffectiveSegment_run _ _ rfl rfl]

end P256.Proofs.Common.Encoding.Parser.LengthCheck
