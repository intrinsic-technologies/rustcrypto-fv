import P256.Proofs.Signing.Wrapper.Hash.Finalize.Pad.Fill.Pre
import P256.Proofs.HMAC.Finalize.Padding.Fill.Call

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash.Finalize.Pad.Fill

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem call [Bindings] {initial start s : RamState} {secret message : ByteArray}
    (pre : HashEntry initial start secret message)
    (state : Marked initial start s message) :
    ∃ t, Advances (returnBoundary initial) 1 s t ∧ ReadyToStep t ∧
      (callEffect (fun _ => 0x11c810) 0x102895 s).Holds s t ∧
      Frame initial start t 528 := by
  have pointer := HMAC.Finalize.Padding.memset_pointer state.loaded
  have target :
      callMemPtr (0x10288f) (.rip 0x101cbb) s = 0x11c810 := by
    change (Operand.mem (0x10288f + 6 +
      (0x101cbb : BitVec 32).signExtend 64) : Operand 64).read s = _
    change (Operand.mem 0x204550 : Operand 64).read s = _
    exact pointer.2
  have push : pushAddr s = stackPtr initial - 528 := by
    change stackPtr s - 8 = _
    rw [state.rsp]
    bv_omega
  have writable : MemWritable s (pushAddr s) 8 := by
    rw [push]
    exact P256.Proofs.Program.writable_of_grow
      (stack_sub_writable8 (stack pre.context)
        (fun a ha hp => stack_avoids pre.context a ha (.inr hp)) (by decide) (by decide))
      state.allocated
  have apart : RangeApart (pushAddr s) 8 (0x10288f) 6 := by
    rw [push]
    intro i hi j hj he
    apply stack_avoids pre.context (stackPtr initial - 528 + BitVec.ofNat 64 i)
    · exact stack_buffer_contains (stack pre.context) (offset := 528) (len := 8)
        (by decide) (by decide) (memoryRegion_contains_add
          (stack_buffer_bounded (stack pre.context) (by decide) (by decide))
          (Nat.le_refl _) (Nat.le_refl _) hi)
    · left
      change stackPtr initial - 528 + BitVec.ofNat 64 i = _ at he
      rw [he]
      have h := inProgram_of_textOffset (0x288f + j) (by omega)
      simp only [BitVec.ofNat_add, ← BitVec.add_assoc] at h
      exact h
  have pointerReadable : MemReadable s
      ((AddrMode.rip 0x101cbb).addr s (0x10288f + 6)) 8 := by
    change MemReadable s (0x10288f + 6 + (0x101cbb : BitVec 32).signExtend 64) 8
    change MemReadable s 0x204550 8
    exact pointer.1
  obtain ⟨call, step, ready, effect⟩ :=
    call_m64_effect_step (0x10288f) (.rip 0x101cbb)
      trivial rfl rfl s (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0x288f _
        (by decide) (by decide +kernel))
      ⟨⟨⟨state.rip, writable, apart⟩, by rw [target]; decide⟩, pointerReadable⟩
  have entry : call.RIP = 0x11c810 := effect.rip.trans target
  have run : Advances (returnBoundary initial) 1 s call := Advances.of_step step (.inl (by
    rw [entry]
    exact boundary_ne_program (outside pre.context) (inProgram_of_textOffset 0x1c810 (by decide))))
  have callFrame : Frame initial start call 528 :=
    state.toFrame.after_effect pre.context run ready effect.agrees
      (by
        intro c hc a ha
        simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl
        · exact ha.elim
        · refine ⟨workRegion initial, by simp, ?_⟩
          rw [push] at ha
          exact work_contains pre.context (by decide) (by decide) ha
        · exact ha.elim)
      (effect.writes.1.trans push) (by simp)
  exact ⟨call, run, ready, ⟨entry, effect.writes, effect.flags, effect.agrees⟩, callFrame⟩

end P256.Proofs.Signing.Wrapper.Hash.Finalize.Pad.Fill
