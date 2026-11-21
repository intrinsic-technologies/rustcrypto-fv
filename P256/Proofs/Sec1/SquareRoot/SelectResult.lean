import P256.Proofs.Sec1.SquareRoot.SelectCall
import P256.Proofs.Sec1.SquareRoot.SelectPrepare

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program

theorem select_stage [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {beta : Nat} {select : Bool} (pre : Pre s boundary)
    (state : SelectCallState s t beta select) :
    ∃ n u, Advances boundary n t u ∧ FrameState s u ∧ u.RIP = 0x114599 ∧
      u.regValue .rbp = (if select then 1 else 0) ∧
      Field.MontgomeryAt u (stackPtr s - 536) (if select then beta else 0) := by
  obtain ⟨v, run, saved, rsp, effect⟩ := call_entry pre state.toFrameState 0x14594 0x4c27
    (by decide) (by decide +kernel) (inProgram_of_textOffset 0x191c0 (by decide)) state.rip
  have dst : v.regValue .rdi = stackPtr s - 536 :=
    (effect.agrees.read (r := 7) (n := 64) (by simp)).trans state.rdi
  have src : v.regValue .rdx = stackPtr s - 576 :=
    (effect.agrees.read (r := 2) (n := 64) (by simp)).trans state.rdx
  have si : v.regValue .rsi = 4 :=
    (effect.agrees.read (r := 6) (n := 64) (by simp)).trans state.rsi
  have cx : v.regValue .rcx = 4 :=
    (effect.agrees.read (r := 1) (n := 64) (by simp)).trans state.rcx
  have r8 : v.regValue .r8 = if select then 1 else 0 :=
    (effect.agrees.read (r := 8) (n := 64) (by simp)).trans state.r8
  have bp : v.regValue .rbp = if select then 1 else 0 :=
    (effect.agrees.read (r := 5) (n := 64) (by simp)).trans state.rbp
  have ret : (returnBoundary v).rip = 0x114599 := (callEffect_stack effect).1
  have cp := select_call_pre pre saved rsp effect.rip si cx src dst
    (by rw [ret]; exact inProgram_of_textOffset 0x14599 (by decide))
  have bytes {offset len i : Nat} (ho : offset ≤ 584) (hl : len ≤ offset + 8) (hi : i < len) :=
    ScalarFrame.call_byte (by decide : 584 + 16 ≤ 2^64) state.rsp effect ho hl hi
  have zero : Field.MontgomeryAt v (stackPtr s - 536) 0 :=
    state.zero.of_bytes_eq (fun i hi => bytes (by decide) (by decide) hi)
  have candidate : Field.MontgomeryAt v (stackPtr s - 576) beta :=
    state.candidate.of_bytes_eq (fun i hi => bytes (by decide) (by decide) hi)
  obtain ⟨u, result, selected⟩ := LimbSelect.limb_select32_correct cp r8
  obtain ⟨n, execution⟩ := result.execution
  refine ⟨1+n, u, run.trans execution,
    stack_result_frame pre saved rsp dst (by decide) (by decide) (by decide) result,
    result.rip.trans ret, (result.calleeSaved .rbp (by simp)).trans bp, ?_⟩
  cases select
  · apply zero.of_bytes_eq
    intro i hi
    have h := selected i hi
    simpa only [dst, Bool.false_eq_true, ↓reduceIte] using h
  · apply candidate.of_bytes_eq
    intro i hi
    have h := selected i hi
    simpa only [dst, src, ↓reduceIte] using h

end P256.Proofs.Sec1.SquareRoot
