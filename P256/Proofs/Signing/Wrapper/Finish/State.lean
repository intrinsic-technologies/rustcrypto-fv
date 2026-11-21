import P256.Proofs.Signing.Wrapper.Finish.Memory

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem after [Bindings] {initial t u : RamState} {cs : List Component}
    (pre : Pre initial) (state : State initial t) (ready : ReadyToStep u)
    (agrees : AgreesExcept cs t u)
    (writes : WritesWithin cs #v[registerRegion initial .rcx 72])
    (registers : ∀ r ∈ [4,5], Component.reg r ∉ cs)
    (df : Component.df ∉ cs) : State initial u := by
  have frame := agrees.memoryWriteFrame writes
  refine ⟨bindingsSupported_of_ready_agrees state.bindingsSupported ready agrees,
    supportedMachine_of_ready_agrees state.machine ready agrees, ?_,
    agrees.directionFlagClear df state.directionFlag,
    (agrees.read (n := 64) (registers 4 (by simp))).trans state.rsp,
    (frame_read_saved pre frame (off := 208) (by decide)).trans state.output,
    (frame_read_saved pre frame (off := 200) (by decide)).trans state.capacity,
    (frame_read_saved pre frame (off := 48) (by decide)).trans state.savedRbx,
    (frame_read_saved pre frame (off := 40) (by decide)).trans state.savedR12,
    (frame_read_saved pre frame (off := 32) (by decide)).trans state.savedR13,
    (frame_read_saved pre frame (off := 24) (by decide)).trans state.savedR14,
    (frame_read_saved pre frame (off := 16) (by decide)).trans state.savedR15,
    (frame_read_saved pre frame (off := 8) (by decide)).trans state.savedRbp,
    ?_, ?_, fun a ha => agrees.grow a (state.allocated a ha)⟩
  · intro a b hf
    rw [frame a]
    · exact state.loaded a b hf
    · intro r hr ha
      have hr' : r = registerRegion initial .rcx 72 := by simpa using hr
      subst r
      exact pre.avoids _ (by simp) a ha (.inl ⟨b,hf⟩)
  · have h := frame_read_saved pre frame (off := 0) (by decide)
    simp only [BitVec.sub_zero] at h
    exact h.trans state.returnAddress
  · exact (agrees.read (n := 64) (registers 5 (by simp))).trans state.rbp

theorem State.after_registers [Bindings] {initial t u : RamState} {cs : List Component}
    (state : State initial t) (ready : ReadyToStep u) (agrees : AgreesExcept cs t u)
    (memory : ∀ c ∈ cs, ∀ a, ¬ c.Covers a)
    (registers : ∀ r ∈ [4,5], Component.reg r ∉ cs)
    (df : Component.df ∉ cs) : State initial u := by
  have hm := agrees.external memory
  refine ⟨bindingsSupported_of_ready_agrees state.bindingsSupported ready agrees,
    supportedMachine_of_ready_agrees state.machine ready agrees, ?_,
    agrees.directionFlagClear df state.directionFlag,
    (agrees.read (n := 64) (registers 4 (by simp))).trans state.rsp,
    by simpa only [hm] using state.output,
    by simpa only [hm] using state.capacity,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    (agrees.read (n := 64) (registers 5 (by simp))).trans state.rbp,
    fun a ha => agrees.grow a (state.allocated a ha)⟩
  · simpa only [ProgramLoaded, hm] using state.loaded
  · simpa only [hm] using state.savedRbx
  · simpa only [hm] using state.savedR12
  · simpa only [hm] using state.savedR13
  · simpa only [hm] using state.savedR14
  · simpa only [hm] using state.savedR15
  · simpa only [hm] using state.savedRbp
  · simpa only [hm] using state.returnAddress

end P256.Proofs.Signing.Wrapper.Finish
