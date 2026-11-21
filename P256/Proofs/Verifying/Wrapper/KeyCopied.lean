import P256.Proofs.Verifying.Wrapper.KeyBuffer
import P256.Proofs.Verifying.Wrapper.CopyFrame
import P256.Proofs.Verifying.Wrapper.KeyCopy.Run

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure KeyCopied [Bindings] (initial s : RamState) (key : ByteArray) : Prop
    extends ReturnState initial s where
  execution : ∃ fuel, Advances (returnBoundary initial) fuel initial s
  frame : MemoryWriteFrame initial s (wrapperRegions verifyingKeyVerify initial)
  rip : s.RIP = 0x1030e6
  output : s.regValue .r12 = initial.regValue .rcx
  capacity : s.regValue .r13 = initial.regValue .r8
  pointers : s.regValue .r14 = initial.regValue .rdi
  lengths : s.regValue .rbx = initial.regValue .rdx
  count : s.regValue .r15 = 3
  bytes : (MemoryRegion.mk (stackPtr s).toNat 65).HasBytes s.external key

theorem copy_key [bindings : Bindings] {initial : RamState} {key signature message : ByteArray}
    {slices : Array Input}
    (hb : MachineRamUnitStrideDecodable bindings initial)
    (hm : SupportedIntegerMachineState bindings.processor initial)
    (call : ValidCallWithSlices verifyingKeyVerify initial [key, signature, message] slices) :
    ∃ t, KeyCopied initial t key := by
  obtain ⟨s,state⟩ := guards_correct hb hm call
  obtain ⟨fuel,t,run,ready,ag,rip,bytes⟩ := KeyCopy.copy_correct (key_buffer_pre call state)
    state.loaded (outer_boundary call hm hb) (readyToStep state.machine state.bindingsSupported)
  have st := state.toReturnState.after_copy call ready ag
  have sp : stackPtr t = stackPtr s := ag.read (n := 64) (r := 4) (by simp [KeyCopy.components])
  obtain ⟨nf,full⟩ := state.execution
  refine ⟨t,st,⟨nf+fuel,full.trans run⟩,
    memoryWriteFrame_trans state.frame (copy_frame call state.rsp ag),rip,
    (ag.read (n := 64) (r := 12) (by simp [KeyCopy.components])).trans state.output,
    (ag.read (n := 64) (r := 13) (by simp [KeyCopy.components])).trans state.capacity,
    (ag.read (n := 64) (r := 14) (by simp [KeyCopy.components])).trans state.pointers,
    (ag.read (n := 64) (r := 3) (by simp [KeyCopy.components])).trans state.lengths,
    (ag.read (n := 64) (r := 15) (by simp [KeyCopy.components])).trans state.count,
    state.keySize,?_⟩
  intro i
  have bound : i.val < 65 := by have := i.isLt; have := state.keySize; omega
  have equal := bytes i.val bound
  have original := state.bytes.2 i
  change t.external[BitVec.ofNat 64 ((stackPtr t).toNat+i.val)]? = _
  change s.external[BitVec.ofNat 64 ((s.regValue .rdx).toNat+i.val)]? = _ at original
  simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, sp] at original ⊢
  exact equal.trans original

end P256.Proofs.Verifying.Wrapper
