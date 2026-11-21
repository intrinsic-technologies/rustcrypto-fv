import P256.Proofs.Signing.Wrapper.Hash.Finalize.Interface
import P256.Proofs.Signing.Wrapper.Hash.Finalize.Compress.Preserve
import P256.Proofs.Signing.Wrapper.Hash.Call.Arguments

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash.Call

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Prepared [Bindings] (initial start s : RamState)
    (message : ByteArray) : Prop extends Frame initial start s where
  rip : s.RIP = 0x102a39
  input : s.regValue .rsi = stackPtr initial - 152
  output : s.regValue .rdi = stackPtr initial - 456
  digestPointer : s.regValue .rdx = stackPtr initial - 520
  digestLength : s.regValue .rcx = 32
  entropyPointer : s.regValue .r8 = 1
  entropyLength : s.regValue .r9 = 0
  status : s.regValue .rbp = 0
  digest : (MemoryRegion.mk (stackPtr initial - 520).toNat 32).HasBytes
    s.external (Operations.hash message)
  savedOutput : memLoad s.external (stackPtr initial - 208) 64 = initial.regValue .rcx
  savedCapacity : memLoad s.external (stackPtr initial - 200) 64 = initial.regValue .r8

theorem prepare [Bindings] {initial start s : RamState} {secret message : ByteArray}
    (pre : HashEntry initial start secret message)
    (state : Finalize.Result initial start s message) :
    ∃ t, Prepared initial start t message := by
  obtain ⟨fuel, t, run, ready, _, effect⟩ := arguments_run (returnBoundary initial)
    (outside pre.context) s (readyToStep state.machine state.bindingsSupported)
    (arguments_code state.loaded) ⟨state.rip⟩
  have agrees : AgreesExcept [.reg 5,.reg 7,.reg 6,.reg 2,.reg 1,.reg 8,.reg 9,.flags,.rip] s t :=
    effect.agrees
  have memory := agrees.external (by simp [Component.Covers])
  have writes := effect.writes
  change t.regValue .rbp = 0 ∧ t.regValue .rdi = stackPtr s + 64 ∧
    t.regValue .rsi = stackPtr s + 368 ∧ t.regValue .rdx = stackPtr s ∧
    t.regValue .rcx = 32 ∧ t.regValue .r8 = 1 ∧ t.regValue .r9 = 0 at writes
  have frame := state.toFrame.after_registers pre.context run ready agrees
    (by simp [Component.Covers]) (by simp)
  refine ⟨t, {
    toFrame := frame
    rip := effect.rip
    input := writes.2.2.1.trans (ScalarFrame.scalar_stack_address state.rsp (by decide) (by decide))
    output := writes.2.1.trans (ScalarFrame.scalar_stack_address state.rsp (by decide) (by decide))
    digestPointer := writes.2.2.2.1.trans state.rsp
    digestLength := writes.2.2.2.2.1
    entropyPointer := writes.2.2.2.2.2.1
    entropyLength := writes.2.2.2.2.2.2
    status := writes.1
    digest := ?_
    savedOutput := (Finalize.Compress.work_read pre frame.stackFrame (offset := 208) (by decide)).trans pre.output
    savedCapacity := (Finalize.Compress.work_read pre frame.stackFrame (offset := 200) (by decide)).trans pre.capacity
  }⟩
  rw [memory]
  have digest := state.digest
  change (MemoryRegion.mk (stackPtr initial - 520#64 + 0#64).toNat 32).HasBytes
    s.external (Operations.hash message) at digest
  change (MemoryRegion.mk (stackPtr initial - 520#64).toNat 32).HasBytes
    s.external (Operations.hash message)
  simpa only [BitVec.add_zero] using digest

end P256.Proofs.Signing.Wrapper.Hash.Call
