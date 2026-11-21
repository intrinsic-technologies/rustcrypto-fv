import P256.Proofs.Nonce.UpdateValue.Prepare.Pad
import P256.Proofs.Nonce.UpdateValue.Prepare.PadSetup

set_option autoImplicit false

namespace P256.Proofs.Nonce.UpdateValue.Prepare

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem inner_pad [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {state : State} (pre : UpdateValuePre initial boundary state)
    (input : Keyed initial s state) :
    ∃ fuel t, Advances boundary fuel s t ∧ InnerPadded initial t state := by
  obtain ⟨fuel, u, run, ready, _, effect⟩ := PadSetup.inner_run boundary pre.outerBoundary s
    (readyToStep input.machine input.bindingsSupported) (PadSetup.inner_code input.loaded) input.rip
  have agrees : AgreesExcept [.reg 0, .rip] s u := effect.agrees
  have context := input.toContext.after_agrees pre ready agrees
    (by intro r member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> simp)
    (by intro c member a covered
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> exact covered.elim)
  have memory : u.external = s.external := agrees.external (by simp [Component.Covers])
  have bytes : (MemoryRegion.mk (scratch initial + 8).toNat 64).HasBytes u.external
      (HMAC.keyPad state.key 0) := by rw [memory]; exact input.key
  obtain ⟨t, loopRun, contextT, post, bytesT⟩ := pad_run (loop := .valueInner) pre context
    rfl effect.rip effect.writes 0 bytes
  exact ⟨fuel + 112, t, run.trans loopRun, contextT, post.rip, bytesT⟩

end P256.Proofs.Nonce.UpdateValue.Prepare
