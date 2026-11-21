import P256.Proofs.Signing.Wrapper.Entry.Decode.Call
import P256.Proofs.SecretKeyFromBytes.Scalar.Representation

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Entry.Decode

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program Prelude
open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SecretKeyFromBytes.Scalar

structure ReadState [Bindings] (initial s : RamState) (secret : ByteArray) : Prop extends
    State initial s 520 where
  rip : s.RIP = 0x102466
  status : (Operand.reg 0 : Operand 8).read s = 255
  value : Nat256At s (stackPtr initial-520) (Arith.uint secret)
  pointers : s.regValue .r12 = initial.regValue .rdi
  lengths : s.regValue .r15 = initial.regValue .rdx
  count : s.regValue .r13 = 2
  output : s.regValue .rbx = initial.regValue .rcx
  capacity : s.regValue .r14 = initial.regValue .r8

theorem read_result [Bindings] {initial t u : RamState} {secret message : ByteArray}
    (context : Context initial secret message) (state : CalleeEntry initial t secret)
    (result : ReadBe.Result t u (returnBoundary initial) secret) : ReadState initial u secret := by
  obtain ⟨slices,call⟩ := context.call
  have hs : Stack.Valid initial 5112 := call.stackAvailable.1
  have bounds := stack_bounds hs
  have spn : (stackPtr t).toNat = (stackPtr initial).toNat-528 := by
    rw [state.rsp]; exact stack_sub_toNat hs (by decide)
  have dst : t.regValue .rdx = stackPtr initial-520 := state.destination
  have dn : (t.regValue .rdx).toNat = (stackPtr initial).toNat-520 := by
    rw [dst]; exact stack_sub_toNat hs (by decide)
  have resultMemory : MemoryWriteFrame t u #v[workRegion initial] := by
    intro a ha
    apply result.frame a
    intro region hr hin
    apply ha (workRegion initial) (by simp)
    have choice : region = registerRegion t .rdx 32 ∨ region = Stack.region t 128 := by simpa using hr
    change (stackPtr initial).toNat-5112 ≤ a.toNat ∧ a.toNat < (stackPtr initial).toNat-5112+5064
    rcases choice with rfl | rfl
    · change (t.regValue .rdx).toNat ≤ a.toNat ∧ a.toNat < (t.regValue .rdx).toNat+32 at hin
      rw [dn] at hin
      constructor <;> omega
    · change (stackPtr t).toNat-128 ≤ a.toNat ∧ a.toNat <
        (Stack.region t 128).start+(Stack.region t 128).size at hin
      rw [stack_region_end] at hin
      change (stackPtr t).toNat-128 ≤ a.toNat ∧ a.toNat < (stackPtr t).toNat+8 at hin
      rw [spn] at hin
      constructor <;> omega
  obtain ⟨n,hn⟩ := state.execution
  obtain ⟨m,hm⟩ := result.execution
  have su : State initial u 520 := by
    refine ⟨⟨n+m,hn.trans hm⟩,result.bindingsSupported,result.machine,
      result.loaded,result.directionFlag,?_,?_,?_,?_,?_,?_,?_,?_,
      fun a ha => result.allocated a (state.allocated a ha),
      memoryWriteFrame_trans state.frame (work_frame hs resultMemory)⟩
    · have h : stackPtr u = stackPtr t+8 := result.rsp
      rw [h,state.rsp]
      simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
      rfl
    · exact (work_read hs resultMemory (by decide)).trans state.savedRbx
    · exact (work_read hs resultMemory (by decide)).trans state.savedR12
    · exact (work_read hs resultMemory (by decide)).trans state.savedR13
    · exact (work_read hs resultMemory (by decide)).trans state.savedR14
    · exact (work_read hs resultMemory (by decide)).trans state.savedR15
    · exact (work_read hs resultMemory (by decide)).trans state.savedRbp
    · have h := work_read hs resultMemory (offset:=0) (by decide)
      simp only [BitVec.sub_zero] at h
      exact h.trans state.returnAddress
  refine ⟨su,result.rip.trans state.decoderReturn,result.status,?_,?_,?_,?_,?_,?_⟩
  · apply nat256At_of_memLoad_limbs
    · have valid := (arguments_iff secret message).mp call.argumentsValid
      exact Nat.lt_trans valid.2.2 (by decide +kernel : Operations.domain.n < 2^256)
    · intro i hi
      exact su.allocated _ ((stack_sub_readable hs (offset:=520) (len:=32)
        (by decide) (by decide)).mem i hi)
    · simpa only [state.destination] using result.value
  · exact (result.calleeSaved .r12 (by simp)).trans state.pointers
  · exact (result.calleeSaved .r15 (by simp)).trans state.lengths
  · exact (result.calleeSaved .r13 (by simp)).trans state.count
  · exact (result.calleeSaved .rbx (by simp)).trans state.output
  · exact (result.calleeSaved .r14 (by simp)).trans state.capacity

end P256.Proofs.Signing.Wrapper.Entry.Decode
