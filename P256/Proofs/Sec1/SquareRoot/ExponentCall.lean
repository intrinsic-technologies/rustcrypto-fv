import P256.Proofs.Sec1.SquareRoot.Call
import P256.Proofs.Sec1.SquareRoot.PrepareInterface
import P256.Proofs.Sec1.SquareRoot.Value
import P256.Proofs.Field.Preserve

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program

def exponentLayout : StackCallLayout 2176 144 32 1584 :=
  ⟨592, 392, 248, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

theorem exponent_stage [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (pre : Pre s boundary) (state : ExponentCallState s t x)
    (correct : ∀ v, ExponentPre v boundary x →
      ∃ u, CalleeResult v u boundary 32 1584 ∧
        Field.MontgomeryAt u (v.regValue .rdi) (candidate x)) :
    ∃ n u, Advances boundary n t u ∧ FrameState s u ∧ u.RIP = 0x11448f ∧
      u.regValue .r14 = stackPtr s - 248 ∧
      Field.MontgomeryAt u (stackPtr s - 392) x ∧
      Field.MontgomeryAt u (stackPtr s - 248) (candidate x) := by
  obtain ⟨v, run, saved, rsp, effect⟩ := call_entry pre state.frame 0x1448a 0x711
    (by decide) (by decide +kernel) (inProgram_of_textOffset 0x14ba0 (by decide)) state.rip
  have vin : v.regValue .rsi = stackPtr s - 392 :=
    (effect.agrees.read (r := 6) (n := 64) (by simp)).trans state.rsi
  have vout : v.regValue .rdi = stackPtr s - 248 :=
    (effect.agrees.read (r := 7) (n := 64) (by simp)).trans state.rdi
  have ret : (returnBoundary v).rip = 0x11448f := (callEffect_stack effect).1
  have base : CalleePre v boundary 0x114ba0 144 32 1584 :=
    CalleePre.of_stack pre exponentLayout saved.bindingsSupported saved.machine saved.directionFlag
      saved.loaded saved.allocated effect.rip rsp vin vout
      (by rw [ret]; exact inProgram_of_textOffset 0x1448f (by decide))
  have bytes {offset len i : Nat} (ho : offset ≤ 584) (hl : len ≤ offset + 8) (hi : i < len) :=
    ScalarFrame.call_byte (by decide : 584 + 16 ≤ 2^64) state.frame.rsp effect ho hl hi
  have residue : ResidueAt v (v.regValue .rsi) x := by
    rw [vin]
    constructor
    · exact state.input.1.of_bytes_eq (fun i hi => bytes (by decide) (by decide) hi)
    · intro i hi
      have params := state.input.2 i hi
      change t.external[(stackPtr s - 392 + 32) + BitVec.ofNat 64 i]? = _ at params
      have he : stackPtr s - 392 + 32 = stackPtr s - 360 := by
        simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
        rfl
      change v.external[(stackPtr s - 392 + 32) + BitVec.ofNat 64 i]? = _
      rw [he] at params ⊢
      exact (bytes (by decide) (by decide) hi).trans params
  have cp : ExponentPre v boundary x := by
    refine ⟨base, residue, ?_, ?_, ?_⟩
    · exact (effect.agrees.read (r := 2) (n := 64) (by simp)).trans state.rdx
    · exact (effect.agrees.read (r := 1) (n := 64) (by simp)).trans state.rcx
    · have vr8 : v.regValue .r8 = stackPtr s - 360 :=
        (effect.agrees.read (r := 8) (n := 64) (by simp)).trans state.r8
      rw [vin, vr8]
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rfl
  obtain ⟨u, result, value⟩ := correct v cp
  obtain ⟨n, execution⟩ := result.execution
  refine ⟨1+n, u, run.trans execution,
    stack_result_frame pre saved rsp vout (by decide) (by decide) (by decide) result,
    result.rip.trans ret, ?_, ?_, ?_⟩
  · exact (result.calleeSaved .r14 (by simp)).trans
      ((effect.agrees.read (r := 14) (n := 64) (by simp)).trans state.r14)
  · apply state.input.1.of_bytes_eq
    intro i hi
    exact (stack_result_byte pre rsp vout result (by decide) (by decide) (by decide)
      (by decide) hi).trans (bytes (by decide) (by decide) hi)
  · simpa only [vout] using value

end P256.Proofs.Sec1.SquareRoot
