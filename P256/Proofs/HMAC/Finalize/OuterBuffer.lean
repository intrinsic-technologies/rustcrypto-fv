import P256.Proofs.HMAC.Interface
import P256.Proofs.HMAC.Finalize.OuterBuffer.Machine
import P256.Proofs.HMAC.Finalize.OuterBuffer.Copy
import P256.Proofs.Common.Memory.LoadByte

set_option autoImplicit false

namespace P256.Proofs.HMAC.Finalize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Program.ScalarFrame (workRegion)
open P256.Proofs.Common

theorem outer_buffer [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {key input : ByteArray}
    (pre : HmacFinalizePre initial boundary key input)
    (state : Compressed initial s (keyPad key 0x36 ++ input))
    (outer : Sha256StateAt s (stackPtr initial - 152#64) (keyPad key 0x5c))
    (rip : s.RIP = paddingEnd false) :
    ∃ fuel t, Advances boundary fuel s t ∧
      Buffered initial t (keyPad key 0x5c ++ P256.Spec.Operations.hash (keyPad key 0x36 ++ input)) ∧
      t.RIP = paddingStart true := by
  obtain ⟨serializeFuel, u, serializeRun, serialized, next⟩ :=
    OuterBuffer.serialize pre state outer rip
  have machinePre : OuterBuffer.Machine.Pre u := by
    refine ⟨next,
      ScalarFrame.stack_readable (stackPre pre.toHashCalleePre) serialized.toFrameState (by decide) (by decide),
      ScalarFrame.stack_writable (stackPre pre.toHashCalleePre) serialized.toFrameState (by decide) (by decide) (by decide),
      ScalarFrame.stack_code (stackPre pre.toHashCalleePre) serialized.toFrameState (by decide) (by decide)
        (codeOffset := 0x1182) (by decide), ?_⟩
    have position := serialized.outer.position
    simp only [keyPad_size, Nat.reduceMod, UInt8.reduceOfNat] at position
    have address : stackPtr u + 239 = stackPtr initial - 152 + 63 := by
      rw [serialized.rsp]
      bv_omega
    rw [address]
    exact Common.Memory.memLoad8_of_byte position
  obtain ⟨machineFuel, v, machineRun, ready, _, effect⟩ :=
    OuterBuffer.Machine.run boundary pre.outerBoundary u
      (readyToStep serialized.machine serialized.bindingsSupported)
      (OuterBuffer.Machine.code serialized.loaded) machinePre
  have agrees := OuterBuffer.Machine.effect_agrees effect
  have appended := OuterBuffer.append_state pre.toHashCalleePre serialized ready agrees
    (OuterBuffer.Machine.effect_words effect) (OuterBuffer.Machine.effect_position effect)
  have rsp : stackPtr v = stackPtr u := agrees.read (n := 64) (r := 4)
    (by simp [OuterBuffer.appendComponents])
  have source : v.regValue .rsi = stackPtr v + 176 := by
    rw [rsp]
    exact effect.writes.2.2.2.2.1
  have destination : v.regValue .rdi = stackPtr v + 72 := by
    rw [rsp]
    exact effect.writes.2.2.2.1
  have count : v.regValue .rcx = 13 := effect.writes.2.1
  obtain ⟨t, copyRun, result, finalRip⟩ := OuterBuffer.copy_state pre.toHashCalleePre
    appended.toFrameState effect.rip source destination count appended.outputPointer appended.outer
  exact ⟨serializeFuel + machineFuel + 13, t,
    (serializeRun.trans machineRun).trans copyRun, result, finalRip⟩

end P256.Proofs.HMAC.Finalize
