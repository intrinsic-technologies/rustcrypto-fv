import P256.Proofs.Verifying.Message.Interface
import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Verifying.Message.Restore

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message

open P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem restore_frame [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre initial boundary 0x10d570 72 24 9992)
    (state : Frame initial s) (rip : s.RIP = 0x10e194) :
    ∃ t, Advances boundary 8 s t ∧ ReadyToStep t ∧
      t.RIP = (returnBoundary initial).rip ∧ stackPtr t = (returnBoundary initial).rsp ∧
      t.external = s.external ∧
      AgreesExcept [.reg 3,.reg 4,.reg 5,.reg 12,.reg 13,.reg 14,.reg 15,.flags,.rip] s t ∧
      CalleeSavedRegistersUnchanged initial t := by
  have top : stackPtr s + 1176 = stackPtr initial := by
    rw [state.rsp]
    exact BitVec.sub_add_cancel _ _
  obtain ⟨t, run, ready, ripT, rspT, memory, agrees, bx, r12, r13, r14, r15, bp⟩ :=
    restore (readyToStep state.machine state.bindingsSupported) state.loaded pre.outerBoundary rip
      (fun offset member => by
        have bound : offset ≤ 1176 := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          omega
        rw [ScalarFrame.scalar_stack_address state.rsp (by decide) bound]
        exact readable_of_grow (stack_sub_readable pre.stack (by omega : 1176 - offset ≤ 9992)
          (by omega : 8 ≤ (1176 - offset) + 8))
          state.allocated)
      (by rw [top]; exact state.returnAddress) pre.returnInProgram
  refine ⟨t, run, ready, ripT, ?_, memory, agrees, ?_⟩
  · change stackPtr t = stackPtr initial + 8
    rw [rspT, state.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  · intro reg member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [bx]
      change memLoad s.external (stackPtr s + BitVec.ofNat 64 1128) 64 = initial.regValue .rbx
      rw [ScalarFrame.scalar_stack_address state.rsp (by decide) (by decide : 1128 ≤ 1176)]
      exact state.saved (.rbx,48) (by simp [savedRegisters])
    · rw [bp]
      change memLoad s.external (stackPtr s + BitVec.ofNat 64 1168) 64 = initial.regValue .rbp
      rw [ScalarFrame.scalar_stack_address state.rsp (by decide) (by decide : 1168 ≤ 1176)]
      exact state.saved (.rbp,8) (by simp [savedRegisters])
    · rw [r12]
      change memLoad s.external (stackPtr s + BitVec.ofNat 64 1136) 64 = initial.regValue .r12
      rw [ScalarFrame.scalar_stack_address state.rsp (by decide) (by decide : 1136 ≤ 1176)]
      exact state.saved (.r12,40) (by simp [savedRegisters])
    · rw [r13]
      change memLoad s.external (stackPtr s + BitVec.ofNat 64 1144) 64 = initial.regValue .r13
      rw [ScalarFrame.scalar_stack_address state.rsp (by decide) (by decide : 1144 ≤ 1176)]
      exact state.saved (.r13,32) (by simp [savedRegisters])
    · rw [r14]
      change memLoad s.external (stackPtr s + BitVec.ofNat 64 1152) 64 = initial.regValue .r14
      rw [ScalarFrame.scalar_stack_address state.rsp (by decide) (by decide : 1152 ≤ 1176)]
      exact state.saved (.r14,24) (by simp [savedRegisters])
    · rw [r15]
      change memLoad s.external (stackPtr s + BitVec.ofNat 64 1160) 64 = initial.regValue .r15
      rw [ScalarFrame.scalar_stack_address state.rsp (by decide) (by decide : 1160 ≤ 1176)]
      exact state.saved (.r15,16) (by simp [savedRegisters])

end P256.Proofs.Verifying.Message
