import P256.Proofs.Verifying.Message.Hash.Finalize.Pad.Fill.Pre

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash.Finalize.Pad.Fill

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem call [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} (pre : Message.Pre initial boundary message)
    (state : Marked initial s boundary message) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧
      (callEffect (fun _ => 0x11c810) 0x10d774 s).Holds s t ∧
      ScalarFrame.FrameState initial t 24 9992 1184 := by
  have pointer := HMAC.Finalize.Padding.memset_pointer state.loaded
  have target :
      callMemPtr (0x10d76e) (.rip 0xf6ddc) s = 0x11c810 := by
    change (Operand.mem (0x10d76e + 6 +
      (0xf6ddc : BitVec 32).signExtend 64) : Operand 64).read s = _
    change (Operand.mem 0x204550 : Operand 64).read s = _
    exact pointer.2
  have writable : MemWritable s (pushAddr s) 8 := by
    rw [ScalarFrame.scalar_call_address state.toFrameState]
    exact P256.Proofs.Program.writable_of_grow
      (stack_sub_writable8 pre.stack
        (fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp)) (by decide) (by decide))
      state.allocated
  have apart : RangeApart (pushAddr s) 8 (0x10d76e) 6 := by
    rw [ScalarFrame.scalar_call_address state.toFrameState]
    intro i hi j hj he
    apply pre.avoids (Stack.region initial 9992) (by simp)
      (stackPtr initial - 1184 + BitVec.ofNat 64 i)
    · exact ScalarFrame.stack_contains pre.toCalleePre (offset := 1184) (len := 8)
        (by decide) (by decide) ⟨i, hi, rfl⟩
    · left
      change stackPtr initial - 1184 + BitVec.ofNat 64 i = _ at he
      rw [he]
      have h := inProgram_of_textOffset (0xd76e + j) (by omega)
      simp only [BitVec.ofNat_add, ← BitVec.add_assoc] at h
      exact h
  have pointerReadable : MemReadable s
      ((AddrMode.rip 0xf6ddc).addr s (0x10d76e + 6)) 8 := by
    change MemReadable s (0x10d76e + 6 + (0xf6ddc : BitVec 32).signExtend 64) 8
    change MemReadable s 0x204550 8
    exact pointer.1
  obtain ⟨call, step, ready, effect⟩ :=
    call_m64_effect_step (0x10d76e) (.rip 0xf6ddc)
      trivial rfl rfl s (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0xd76e _
        (by decide) (by decide +kernel))
      ⟨⟨⟨state.rip, writable, apart⟩, by rw [target]; decide⟩, pointerReadable⟩
  have entry : call.RIP = 0x11c810 := effect.rip.trans target
  have run : Advances boundary 1 s call := Advances.of_step step (.inl (by
    rw [entry]
    exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1c810 (by decide))))
  have callFrame := state.toFrameState.after_call pre.toCalleePre (by decide) (by decide) ready effect
  exact ⟨call, run, ready, ⟨entry, effect.writes, effect.flags, effect.agrees⟩, callFrame⟩

end P256.Proofs.Verifying.Message.Hash.Finalize.Pad.Fill
