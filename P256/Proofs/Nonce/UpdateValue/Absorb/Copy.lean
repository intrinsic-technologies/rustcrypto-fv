import P256.Proofs.Nonce.UpdateValue.Absorb.State
import P256.Proofs.Nonce.UpdateValue.Absorb.Copy.Setup
import P256.Proofs.Nonce.UpdateValue.Copy

set_option autoImplicit false

namespace P256.Proofs.Nonce.UpdateValue.Absorb

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

private def copyLayout : StackCallLayout 1168 168 168 0 :=
  ⟨496, 384, 216, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

theorem copy [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {state : State} (pre : UpdateValuePre initial boundary state)
    (buffered : Buffered initial s state) :
    ∃ fuel t, Advances boundary fuel s t ∧ Absorbed initial t state := by
  obtain ⟨setupFuel, u, setupRun, ready, _, effect⟩ := Copy.Setup.run boundary pre.outerBoundary s
    (readyToStep buffered.machine buffered.bindingsSupported) (Copy.Setup.code buffered.loaded) buffered.rip
  have agrees : AgreesExcept [.reg 14, .reg 6, .reg 2, .reg 7, .rip] s u := effect.agrees
  have memory : u.external = s.external := agrees.external (by simp [Component.Covers])
  have frame : FrameState initial u := buffered.toFrameState.after_registers ready agrees
    (by simp [Component.Covers]) (by simp)
  have values := effect.writes
  change u.regValue .r14 = stackPtr s + 272 ∧ u.regValue .rsi = stackPtr s + 104 ∧
    u.regValue .rdx = 168 ∧ u.regValue .rdi = stackPtr s + 272 at values
  have sourceAddr : scratch initial + 104#64 = stackPtr initial - 384#64 := by
    simp only [scratch, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have targetAddr : scratch initial + 272#64 = stackPtr initial - 216#64 := by
    simp only [scratch, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have source : u.regValue .rsi = stackPtr initial - 384 := by
    have h := values.2.1.trans (congrArg (· + 104) (show stackPtr s = scratch initial from buffered.rsp))
    simpa only [BitVec.ofNat_eq_ofNat, sourceAddr] using h
  have destination : u.regValue .rdi = stackPtr initial - 216 := by
    have h := values.2.2.2.trans (congrArg (· + 272) (show stackPtr s = scratch initial from buffered.rsp))
    simpa only [BitVec.ofNat_eq_ofNat, targetAddr] using h
  obtain ⟨t, result⟩ := memcpy_call pre frame copyLayout rfl
    (by decide) (by decide) 0xabab 0xf9947 (by decide)
    (by decide +kernel) (by decide +kernel) effect.rip source destination values.2.2.1
  obtain ⟨fuel, run⟩ := result.execution
  refine ⟨setupFuel + fuel, t, setupRun.trans run, result.toFrameState, result.rip,
    (result.calleeSaved .rbx (by simp)).trans
      ((agrees.read (n := 64) (r := 3) (by simp)).trans buffered.valuePointer),
    (result.calleeSaved .r14 (by simp)).trans
      (values.1.trans (congrArg (· + 272) buffered.rsp)), ?_, ?_⟩
  · apply buffered.drbg.copy
    intro i hi
    rw [← show u.external = s.external from memory]
    apply result.writes
    intro region member inside
    have eq : region = ScalarFrame.workRegion initial 1168 := by simpa using member
    subst region
    exact pre.separation _
      (memoryRegion_contains_add pre.stateBounded (Nat.le_refl _) (Nat.le_refl _) hi)
      (work_substack pre inside)
  · have hmac : HMAC.HmacStateAt u (scratch initial + 104) state.key state.value :=
      buffered.hmac.copy (fun _ _ => by rw [memory])
    apply hmac.copy
    simpa only [BitVec.ofNat_eq_ofNat, sourceAddr, targetAddr, copyLayout] using result.copied

end P256.Proofs.Nonce.UpdateValue.Absorb
