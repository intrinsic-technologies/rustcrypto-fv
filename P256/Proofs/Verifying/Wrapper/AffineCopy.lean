import P256.Proofs.Verifying.Wrapper.WorkState
import P256.Proofs.Program.StackBuffer
import P256.Proofs.Common.Instructions.RepMovsqAny
import P256.Proofs.Sec1.Representation

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Standards.SECG.ECC

theorem affine_copy [Bindings] {initial s : RamState} {key signature message : ByteArray}
    {slices : Array Input} {point : Curve.Point}
    (call : ValidCallWithSlices verifyingKeyVerify initial [key,signature,message] slices)
    (state : ReturnState initial s) (outside : ¬ InProgram (returnBoundary initial).rip)
    (rip : s.RIP = 0x103115) (source : s.regValue .rsi = stackPtr initial-200)
    (destination : s.regValue .rdi = stackPtr initial-112) (count : s.regValue .rcx = 9)
    (represented : Sec1.AffineAt s (stackPtr initial-200) point) :
    ∃ t, Advances (returnBoundary initial) 9 s t ∧ ReturnState initial t ∧
      t.RIP = 0x103118 ∧ Sec1.AffineAt t (stackPtr initial-112) point ∧
      AgreesExcept [.reg 6,.reg 7,.reg 1,.mem (stackPtr initial-112) 72,.rip] s t ∧
      MemoryWriteFrame s t #v[workRegion initial] := by
  have hn : (rcx.read s).toNat = 9 := by
    change (s.regValue .rcx).toNat = 9
    rw [count]
    rfl
  have src : MemReadable s (rsi.read s) 72 := by
    change MemReadable s (s.regValue .rsi) 72
    rw [source]
    exact readable_of_grow (stack_sub_readable call.stackAvailable.1
      (offset := 200) (len := 72) (by decide) (by decide)) state.allocated
  have dst : P256.Proofs.Common.Instructions.CrossPageStore.Writable s (rdi.read s) 72 := by
    change P256.Proofs.Common.Instructions.CrossPageStore.Writable s (s.regValue .rdi) 72
    rw [destination]
    exact stack_buffer_writable call.stackAvailable.1 (call_stack_avoids call) state.allocated
      (by decide) (by decide) (by decide)
  have disjoint : (rsi.read s).toNat+72 ≤ (rdi.read s).toNat ∨
      (rdi.read s).toNat+72 ≤ (rsi.read s).toNat := by
    left
    change (s.regValue .rsi).toNat+72 ≤ (s.regValue .rdi).toNat
    rw [source,destination]
    change (stackPtr initial-200#64).toNat+72 ≤ (stackPtr initial-112#64).toNat
    have bounds := stack_bounds call.stackAvailable.1
    change 10280 ≤ (stackPtr initial).toNat ∧ (stackPtr initial).toNat+8 < 2^32 at bounds
    rw [stack_sub_toNat call.stackAvailable.1 (by decide : 200 ≤ verifyingKeyVerify.minStackBytes),
      stack_sub_toNat call.stackAvailable.1 (by decide : 112 ≤ verifyingKeyVerify.minStackBytes)]
    omega
  have codeApart : RangeApart (rdi.read s) 72 0x103115 3 := by
    change RangeApart (s.regValue .rdi) 72 _ _
    rw [destination]
    intro i hi j hj he
    apply call_stack_avoids call (stackPtr initial-112+BitVec.ofNat 64 i) ?_ (.inl ?_)
    · exact stack_buffer_contains call.stackAvailable.1 (by decide : 112 ≤ verifyingKeyVerify.minStackBytes)
        (by decide : 72 ≤ 112+8)
        (memoryRegion_contains_add (stack_buffer_bounded call.stackAvailable.1
          (offset := 112) (len := 72) (by decide) (by decide))
          (Nat.le_refl _) (Nat.le_refl _) hi)
    · rw [he]
      have address : 0x103115+BitVec.ofNat 64 j =
          Extracted.textAddress+BitVec.ofNat 64 (0x3115+j) := by
        rw [BitVec.ofNat_add,← BitVec.add_assoc]
        rfl
      rw [address]
      exact inProgram_of_textOffset _ (by omega)
  have pc := P256.Proofs.Common.Instructions.RepMovsqAny.pre_of_memory rip
    state.directionFlag.df hn src dst disjoint codeApart
  obtain ⟨run,ready,effect,bytes⟩ :=
    P256.Proofs.Common.Instructions.RepMovsqAny.rep_movsq_execution
      state.bindingsSupported.stringStride (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0x3115 [0xf3,0x48,0xa5]
        (by decide) (by decide +kernel)) pc hn
      (boundary_ne_program outside (inProgram_of_textOffset 0x3115 (by decide)))
      (boundary_ne_program outside (inProgram_of_textOffset 0x3118 (by decide)))
  simp only [show max 9 1 = 9 from rfl] at run ready effect bytes
  generalize hu : nextStates 9 s = t at run ready effect bytes
  have ag : AgreesExcept [.reg 6,.reg 7,.reg 1,.mem (stackPtr initial-112) 72,.rip] s t := by
    simpa only [repMovsqEffect_components,hn,Nat.reduceMul,
      show rdi.read s = stackPtr initial-112 from destination] using effect.agrees
  have frame : MemoryWriteFrame s t #v[workRegion initial] := by
    apply ag.memoryWriteFrame
    intro c hc a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    exact ⟨workRegion initial,by simp,work_contains call.stackAvailable.1
      (by decide) (by decide) ha⟩
  refine ⟨t,run,state.after_work call ready ag frame (by simp) (by simp) (by simp),
    effect.rip,?_,ag,frame⟩
  apply represented.of_bytes_eq
  intro i hi
  have eq := bytes i (by omega)
  change t.external[s.regValue .rdi+BitVec.ofNat 64 i]? =
    s.external[s.regValue .rsi+BitVec.ofNat 64 i]? at eq
  simpa only [source,destination] using eq

end P256.Proofs.Verifying.Wrapper
