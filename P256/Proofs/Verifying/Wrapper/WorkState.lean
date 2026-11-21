import P256.Proofs.Verifying.Wrapper.Work
import P256.Proofs.Verifying.Wrapper.ReturnState

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem work_contains {initial : RamState} (stack : Stack.Valid initial 10280)
    {offset len : Nat} {a : BitVec 64} (within : offset ≤ 10280)
    (extent : len+40 ≤ offset)
    (covered : (Component.mem (stackPtr initial-BitVec.ofNat 64 offset) len).Covers a) :
    (workRegion initial).Contains a.toNat := by
  obtain ⟨i,hi,rfl⟩ := covered
  have bounds := stack_bounds stack
  have low := stack_sub_toNat stack within
  rw [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : i < 2^64),
    Nat.mod_eq_of_lt (by rw [low]; omega),low]
  change (stackPtr initial).toNat-10280 ≤ _ ∧
    _ < (stackPtr initial).toNat-10280+(10280-40)
  constructor <;> omega

theorem ReturnState.after_work [Bindings] {initial s t : RamState} {cs : List Component}
    {key signature message : ByteArray} {slices : Array Input}
    (call : ValidCallWithSlices verifyingKeyVerify initial [key,signature,message] slices)
    (state : ReturnState initial s) (ready : ReadyToStep t) (ag : AgreesExcept cs s t)
    (frame : MemoryWriteFrame s t #v[workRegion initial])
    (rsp : Component.reg 4 ∉ cs) (rbp : Component.reg 5 ∉ cs) (df : Component.df ∉ cs) :
    ReturnState initial t := by
  have outer := work_frame call.stackAvailable.1 frame
  refine ⟨bindingsSupported_of_ready_agrees state.bindingsSupported ready ag,
    supportedMachine_of_ready_agrees state.machine ready ag,?_,
    ag.directionFlagClear df state.directionFlag,
    (ag.read (n := 64) rsp).trans state.rsp,?_,?_,
    (ag.read (n := 64) rbp).trans state.rbp,fun a ha => ag.grow a (state.allocated a ha)⟩
  · intro a b byte
    rw [outer a]
    · exact state.loaded a b byte
    intro region member contained
    have hr : region ∈ #v[heapRegion verifyingKeyVerify initial,allocatorStateRegion,
        randomSourceRegion,callStack verifyingKeyVerify initial] := by
      simp_all [wrapperRegions]
    exact (call.separation.2 region hr).2 a contained (.inl ⟨b,byte⟩)
  · intro entry member
    have bound : entry.2 ≤ 40 := by
      simp only [savedRegisters,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl <;> decide
    exact (work_read call.stackAvailable.1 frame bound).trans (state.saved entry member)
  · have h := work_read call.stackAvailable.1 frame (offset := 0) (by decide)
    change memLoad t.external (stackPtr initial-0#64) 64 =
      memLoad s.external (stackPtr initial-0#64) 64 at h
    simp only [BitVec.sub_zero] at h
    exact h.trans state.returnAddress

end P256.Proofs.Verifying.Wrapper
