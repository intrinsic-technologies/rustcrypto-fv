import Md5.Proofs.Buffered.FinalizeReset.Prepare.Geometry

namespace Md5.Proofs.Buffered.FinalizeReset.Prepare

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

theorem memset_run {variant : Variant} [bindings : Bindings] (hstride : UnitStringStride bindings)
    {boundary : ReturnBoundary} {s v : RamState} {n : Nat}
    (hs : Storage s variant) (hp : (.reg 15 : Operand 64).read s = BitVec.ofNat 64 n)
    (hn : n < 64) (hdf : DirectionFlagClear s.RFLAGS)
    (he : (setupEffect s variant).Holds s v) (hr : ReadyToStep v)
    (hc : CodeIn Extracted.programImage v) (hout : ¬ InProgram boundary.rip) :
    ∃ t, MemsetSiteResult boundary (variant.address 0x1007e6) v t := by
  cases variant with
  | saved =>
    have hsite := setup_memset_pre hs hp hn hdf he
    have hsp : stackPtr v = stackPtr s := he.agrees.read (n := 64) (r := 4) (by
      simp [setupEffect, Effect.components, Write.component, Operand.component])
    have hpush : pushAddr v = pushAddr s := by simp only [pushAddr, hsp]
    have hslot := (pushRange hs).of_agrees he.agrees
    have htarget : callMemPtr 0x1007e0 (.rip 0xff822) v = 0x102460 := by
      change (Operand.mem 0x200008 : Operand 64).read v = _
      exact memset_pointer hc
    have hpre : Stack.CallMemPre 0x1007e0 (.rip 0xff822) v := by
      refine ⟨⟨⟨he.rip, ?_⟩, ?_⟩, ?_⟩
      · rw [hpush]
        exact ⟨hslot.readable.low, hslot.readable.mem, hslot.tables⟩
      · rw [htarget]; decide
      · exact memset_pointer_readable hc
    have hbytes : CodeIn (codeRange 0x1007e0 (encodeCallM64 (.rip 0xff822))) v :=
      program_text_slice hc 0x7e0 6 (by decide +kernel)
    exact memset_call hstride (outside_text_range_of_not_inProgram hout 0x102460 0x1024a5 (by decide) (by decide +kernel))
      (Stack.call_m64_rip_effect_step 0x1007e0 0xff822) hr hc hbytes hpre hsite htarget
      (text_address_ne_return hout 0x7e6 (by decide +kernel))
  | direct =>
    have hsite := setup_memset_pre hs hp hn hdf he
    have hsp : stackPtr v = stackPtr s := he.agrees.read (n := 64) (r := 4) (by
      simp [setupEffect, Effect.components, Write.component, Operand.component])
    have hpush : pushAddr v = pushAddr s := by simp only [pushAddr, hsp]
    have hslot := (pushRange hs).of_agrees he.agrees
    have htarget : callMemPtr 0x100e90 (.rip 0xff172) v = 0x102460 := by
      change (Operand.mem 0x200008 : Operand 64).read v = _
      exact memset_pointer hc
    have hpre : Stack.CallMemPre 0x100e90 (.rip 0xff172) v := by
      refine ⟨⟨⟨he.rip, ?_⟩, ?_⟩, ?_⟩
      · rw [hpush]
        exact ⟨hslot.readable.low, hslot.readable.mem, hslot.tables⟩
      · rw [htarget]; decide
      · exact memset_pointer_readable hc
    have hbytes : CodeIn (codeRange 0x100e90 (encodeCallM64 (.rip 0xff172))) v :=
      program_text_slice hc 0xe90 6 (by decide +kernel)
    exact memset_call hstride (outside_text_range_of_not_inProgram hout 0x102460 0x1024a5 (by decide) (by decide +kernel))
      (Stack.call_m64_rip_effect_step 0x100e90 0xff172) hr hc hbytes hpre hsite htarget
      (text_address_ne_return hout 0xe96 (by decide +kernel))

end Md5.Proofs.Buffered.FinalizeReset.Prepare
