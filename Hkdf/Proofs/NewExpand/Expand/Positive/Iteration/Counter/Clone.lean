import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Counter.Frame
import Hkdf.Proofs.Common.Memory.Copy
import Hkdf.Proofs.Common.State
import Hkdf.Proofs.Common.StreamPadding.Execution.Calls

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Counter

open Hkdf.Spec.Program Hkdf.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Machine

private abbrev cloneLayout : StackCallLayout 2264 144 144 0 :=
  ⟨544, 264, 456, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem clone [bindings : Bindings] {entry s : RamState} {boundary : ReturnBoundary}
    {length : Nat} {key message : ByteArray}
    (ctx : StackContext entry boundary length) (stride : UnitStringStride bindings)
    (running : RunningFrame entry boundary length s) (sp : stackPtr s = base entry)
    (pc : s.RIP = 0x10f958) (memcpy : s.regValue .rbx = 0x10dd60)
    (src : s.regValue .rsi = base entry + 272) (dest : s.regValue .rdi = base entry + 80)
    (count : s.regValue .rdx = 144) (hmac : HmacAt s (base entry + 272) key message) :
    ∃ t, RunningFrame entry boundary length t ∧ t.RIP = 0x10f95a ∧
      stackPtr t = base entry ∧ PreservesABI s t ∧
      HmacAt t (base entry + 80) key message ∧
      MemoryWriteFrame s t #v[⟨(base entry + 80).toNat, 144⟩, ⟨(base entry - 8).toNat, 8⟩] := by
  have target : (Operand.reg 3 : Operand 64).read s = 0x10dd60 := memcpy
  obtain ⟨c, runningC, call, ret⟩ := enter_call ctx running sp 0xf958 2 (by decide) pc
    (call_r64_effect_step 0x10f958 0xd3 rfl rfl)
    (programText_slice (programLoaded_codeIn running.loaded) 0xf958 [0xff, 0xd3] (by decide) (by decide +kernel))
    (fun pushed => ⟨pushed, by change (s.regValue .rbx).toNat < 2^32; rw [memcpy]; decide⟩)
    (by change s.regValue .rbx ≠ _; rw [memcpy]
        exact boundary_ne_program ctx.outside (inProgram_of_textOffset 0xdd60 (by decide)))
  have spC : stackPtr c = stackPtr entry - 544 := by
    rw [show stackPtr c = pushAddr s from call.writes.1, pushAddr, sp, base, BitVec.sub_sub]
    rfl
  have inputC : c.regValue .rsi = base entry + 272 :=
    (call.agrees.read (n := 64) (r := 6) (by simp [callEffect, pushEffect_components])).trans src
  have outputC : c.regValue .rdi = base entry + 80 :=
    (call.agrees.read (n := 64) (r := 7) (by simp [callEffect, pushEffect_components])).trans dest
  have countC : c.regValue .rdx = 144 :=
    (call.agrees.read (n := 64) (r := 2) (by simp [callEffect, pushEffect_components])).trans count
  have outputC' : c.regValue .rdi = stackPtr entry - 456 :=
    outputC.trans (base_add (off := 80) (by decide))
  have callee := callee_pre_of_stack stride ctx.stack ctx.stackAvoid ctx.outside
    runningC.machine runningC.directionFlag runningC.loaded runningC.allocated cloneLayout
    (call.rip.trans target) spC (inputC.trans (base_add (off := 272) (by decide))) outputC'
    (by rw [ret]; exact inProgram_of_textOffset 0xf95a (by decide))
  obtain ⟨t, result, copied, _⟩ := Memory.memcpy_correct callee countC (by decide)
  have runningT := runningC.of_callee result (by
    intro r hr a ha
    exact ⟨_, by simp [regions], stack_layout_within ctx.stack cloneLayout spC outputC' r hr a ha⟩)
  obtain ⟨frame, abi⟩ := call_result callee call result running.directionFlag
  have inputHmac : HmacAt c (base entry + 272) key message := by
    apply hmac.of_copy
    rw [← sp]
    exact StreamPadding.Execution.call_local_agrees call 272 144 (by unfold OffsetsApart; decide +kernel) (by decide)
  have hmacT : HmacAt t (base entry + 80) key message := by
    apply inputHmac.of_copy
    simpa only [inputC, outputC] using copied
  have zeroStack : Stack.region c 0 = ⟨(base entry - 8).toNat, 8⟩ := by
    have spC' : stackPtr c = base entry - 8 := by rw [spC, base, BitVec.sub_sub]; rfl
    change (⟨(stackPtr c).toNat - 0, (stackPtr c).toNat + 8 - ((stackPtr c).toNat - 0)⟩ : MemoryRegion) = _
    rw [spC']
    congr 1 <;> omega
  refine ⟨t, runningT, result.rip.trans (congrArg ReturnBoundary.rip ret),
    result.rsp.trans (congrArg ReturnBoundary.rsp ret), abi, hmacT, ?_⟩
  simpa only [registerRegion, outputC, zeroStack] using frame

end Hkdf.Proofs.NewExpand.Expand.Counter
