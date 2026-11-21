import P256.Proofs.Verifying.Combination.Prologue
import P256.Proofs.Program.ScalarFrame.Call

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem call_copy [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (state : State s t) (pc : Nat)
    (bound : pc + 3 < 118431)
    (bytes : Extracted.textBytes.toListFrom pc 3 = [0x41, 0xff, 0xd6])
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 pc)
    (target : t.regValue .r14 = 0x11c930) :
    ∃ u, Advances boundary 1 t u ∧ State s u 6560 ∧
      (callEffect (fun _ => 0x11c930)
        (Extracted.textAddress + BitVec.ofNat 64 pc + 3) t).Holds t u := by
  have addr : pushAddr t = stackPtr s - 6560 := scalar_call_address state
  have push : PushPre (Extracted.textAddress + BitVec.ofNat 64 pc) 3 t := by
    refine ⟨rip, ?_, ?_⟩
    · rw [addr]
      exact writable_of_grow (stack_sub_writable8 pre.stack
        (fun a ha hp => pre.avoids (Stack.region s 8808) (by simp) a ha (.inr hp))
        (by decide) (by decide)) state.allocated
    · rw [addr]
      intro i hi j hj he
      apply pre.avoids (Stack.region s 8808) (by simp) _
        (stack_contains pre (offset := 6560) (by decide) (by decide) ⟨i, hi, rfl⟩) (.inl ?_)
      change InProgram (stackPtr s - 6560 + BitVec.ofNat 64 i)
      rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact inProgram_of_textOffset (pc + j) (by omega)
  obtain ⟨u, run, ready, effect⟩ :=
    (call_r64_rex_effect_step _ 0x41 0xd6 (by simp [RexPrefix]) rfl rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) pc _ (by change pc + 3 ≤ 118431; omega) bytes)
      ⟨push, by change (t.regValue .r14).toNat < 2^32; rw [target]; decide⟩
      (by change t.regValue .r14 ≠ boundary.rip; rw [target]
          exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1c930 (by decide)))
  have effect' : (callEffect (fun _ => 0x11c930)
      (Extracted.textAddress + BitVec.ofNat 64 pc + 3) t).Holds t u := by
    change (callEffect (fun w => w.regValue .r14)
      (Extracted.textAddress + BitVec.ofNat 64 pc + 3) t).Holds t u at effect
    simpa only [callEffect, pushEffect, target] using effect
  exact ⟨u, run, FrameState.after_call pre (by decide) (by decide) state ready effect', effect'⟩

end P256.Proofs.Verifying.Combination
