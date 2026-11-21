import P256.Proofs.Field.Montgomery.Wrapper.State
import P256.Proofs.Program.Call

set_option autoImplicit false

namespace P256.Proofs.Field.Montgomery.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {entryPC : BitVec 64}

theorem call_address (state : FrameState s t) : pushAddr t = stackPtr s - 144 := by
  simp only [pushAddr, state.rsp, scratch, BitVec.sub_sub, BitVec.reduceAdd]
  rfl

theorem call_state {target : RamState → BitVec 64} {ret : BitVec 64}
    (pre : CalleePre s boundary entryPC 32 32 280) (state : FrameState s t)
    (ready : ReadyToStep u) (effect : (callEffect target ret t).Holds t u) :
    SavedState s u := by
  apply state.toSavedState.after_agrees pre ready effect.agrees
  · intro c hc a ha
    simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact ha.elim
    · obtain ⟨i, hi, rfl⟩ := ha
      rw [call_address state]
      exact ⟨workRegion s, by simp,
        ScalarFrame.Work.contains pre (by decide) (by decide) ⟨i, hi, rfl⟩⟩
    · exact ha.elim
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact effect.agrees.read (r := 5) (n := 64) (by simp)
      | exact effect.agrees.read (r := 12) (n := 64) (by simp)
      | exact effect.agrees.read (r := 13) (n := 64) (by simp)
      | exact effect.agrees.read (r := 14) (n := 64) (by simp)
      | exact effect.agrees.read (r := 15) (n := 64) (by simp)
  all_goals simp

theorem call_reduction (square : Bool) (pre : CalleePre s boundary entryPC 32 32 280)
    (state : FrameState s t) (rip : t.RIP = (if square then 0x11387d else 0x11390d)) :
    ∃ u, Advances boundary 1 t u ∧ ReadyToStep u ∧
      (callEffect (fun _ => 0x113c10) (if square then 0x113882 else 0x113912) t).Holds t u := by
  obtain ⟨u, run, ready, _, effect, _⟩ := call_rel32_exists pre.stack
    (pre.avoids _ (by simp)) pre.outerBoundary
    (readyToStep state.machine state.bindingsSupported) state.loaded state.allocated
    136 (if square then 0x1387d else 0x1390d) (if square then 0x38e else 0x2fe) state.rsp (by cases square <;> exact rip) (by cases square <;> decide) (by cases square <;> decide) (by cases square <;> decide)
    (by cases square <;> decide +kernel) (by cases square <;> exact inProgram_of_textOffset 0x13c10 (by decide))
  exact ⟨u, run, ready, by cases square <;> exact effect⟩

end P256.Proofs.Field.Montgomery.Wrapper
