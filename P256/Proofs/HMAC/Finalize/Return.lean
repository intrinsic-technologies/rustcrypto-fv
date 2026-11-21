import P256.Proofs.HMAC.Interface
import P256.Proofs.HMAC.Finalize.Digest.Frame
import P256.Proofs.HMAC.Finalize.Return.Epilogue

set_option autoImplicit false

namespace P256.Proofs.HMAC.Finalize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Program.ScalarFrame (workRegion)
open P256.Proofs.Common

theorem finalize_return [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} (pre : HashCalleePre initial boundary 0x100f10 168 672)
    (state : Compressed initial s message) (rip : s.RIP = paddingEnd true)
    (small : message.size % 64 < 56)
    (entryRun : ∃ fuel, Advances boundary fuel initial s) :
    ∃ t, HashCalleeResult initial t boundary 672 (P256.Spec.Operations.hash message) := by
  have digestPre := Digest.Outer.pre pre state.toFrameState state.outputPointer rip
  obtain ⟨fuel, t, run, ready, _, effect⟩ :=
    Digest.Outer.run boundary pre.outerBoundary s (readyToStep state.machine state.bindingsSupported)
      (Digest.Outer.code state.loaded) digestPre
  have frame := Digest.Outer.frame pre state.toFrameState state.outputPointer ready effect
  have address : stackPtr s + 136 = stackPtr initial - 192#64 :=
    stack_address state.rsp (by decide : 136 ≤ 328)
  have output := Digest.Outer.output digestPre (address.symm ▸ state.hash) effect
  have digest := SHA256.serializeHash_tail_compressions message
  rw [ite_eq_left small] at digest
  rw [digest] at output
  have region : registerRegion s .rbx 32 = registerRegion initial .rsi 32 := by
    unfold registerRegion
    rw [state.outputPointer]
  rw [region] at output
  apply Return.finish pre frame effect.rip ?_ output
  obtain ⟨before, entryRun⟩ := entryRun
  exact ⟨before + fuel, entryRun.trans run⟩

end P256.Proofs.HMAC.Finalize
