import P256.Proofs.Verifying.Combination.Naf.Machine.Finish.Memory
import X86Proofs.Instructions.Test.Generated.RR.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Machine

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open Iterator.Advance (step_nomem branch8)

theorem finish_select [Bindings] {s t : RamState} {boundary : ReturnBoundary} {c : Nat}
    (pre : Pre s boundary) (state : FrameState s t) (rip : t.RIP = 0x10f4da)
    (carry : c ≤ 1) (value : t.regValue .r13 = BitVec.ofNat 64 c) :
    ∃ u, Advances boundary 2 t u ∧ FrameState s u ∧
      u.RIP = (if c=0 then 0x10f4f5 else 0x10f4df) ∧ AgreesExcept [.flags,.rip] t u := by
  obtain ⟨a, runA, readyA, loadedA, effectA⟩ := step_nomem (offset := 0xf4da)
    (test_r64_r64_effect_step 0x10f4da 0x4d 0xed (by simp [RexWPrefix]) rfl)
    (readyToStep state.machine state.bindingsSupported) state.loaded rip (by decide) (by decide +kernel)
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf4dd (by decide)))
    (by simp [Component.Covers])
  have zf : condHolds 4 (StatusFlags.ofRFLAGS a.RFLAGS) = decide (c=0) := by
    have h := effectA.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS a.RFLAGS).ZF = ((t.regValue .r13 &&& t.regValue .r13) == 0) at h
    rw [value] at h
    have cases : c=0 ∨ c=1 := by omega
    rcases cases with rfl | rfl <;> simpa [condHolds] using h
  obtain ⟨u, runU, readyU, _, ripU, agreesU⟩ := branch8 (offset := 0xf4dd) 4 0x16 (decide (c=0))
    readyA loadedA effectA.rip zf (by decide) (by decide +kernel) (by decide +kernel)
    (by by_cases hc : c=0
        · simpa [hc, branchTarget, Extracted.textAddress] using
            boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf4f5 (by decide))
        · simpa [hc, branchTarget, Extracted.textAddress] using
            boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf4df (by decide)))
  have agrees : AgreesExcept [.flags,.rip] t u := (effectA.agrees.trans agreesU).mono (by simp)
  refine ⟨u, runA.trans runU, state.after_registers readyU agrees (by simp [Component.Covers]) (by simp), ?_, agrees⟩
  by_cases hc : c=0 <;> simpa [hc, branchTarget, Extracted.textAddress] using ripU

end P256.Proofs.Verifying.Combination.Naf.Machine
