import P256.Proofs.Verifying.Combination.PointDouble
import P256.Proofs.Projective.Add

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame
open P256.Proofs.Projective.Multiply.Machine.Loop (CallSite call_return_program)

def pointAddSite : CallSite 0x1051f0 :=
  ⟨0xf2b0, 0xffff5f3b, by decide, by decide +kernel, by decide⟩

def pointAddLayout : StackCallLayout 1432 96 96 920 :=
  ⟨416, 144, 336, by decide, by decide, by decide, by decide,
    by decide, by decide, Or.inr (by decide)⟩

theorem point_add [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {point selected : Projective}
    (pre : Return.Pre s boundary) (state : State s t) (rip : t.RIP = 0x10f2b0)
    (dst : t.regValue .rdi = stackPtr s - 336)
    (src : t.regValue .rsi = stackPtr s - 144)
    (value : ProjectiveAt t (stackPtr s - 336) point)
    (chosen : ProjectiveAt t (stackPtr s - 144) selected) :
    ∃ u, PointCallResult s t u boundary 0x10f2b5 336 (point.add selected) := by
  obtain ⟨v, run, ready, effect⟩ := projective_call pre state pointAddSite
    (inProgram_of_textOffset 0x51f0 (by decide)) rip
  have stateV := state.after_call pre (by decide) (by decide) ready effect
  have dstV : v.regValue .rdi = stackPtr s - 336 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans dst
  have srcV : v.regValue .rsi = stackPtr s - 144 :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans src
  have cp := CalleePre.of_stack pre pointAddLayout
    stateV.bindingsSupported stateV.machine stateV.directionFlag stateV.loaded stateV.allocated
    effect.rip stateV.rsp srcV dstV (call_return_program pointAddSite effect)
  have valueV : ProjectiveAt v (v.regValue .rdi) point := by
    rw [dstV]
    exact value.of_bytes_eq (fun i hi => scalar_call_byte (frameOffset := 408)
      (by decide) state effect (by decide) (by decide) hi)
  have chosenV : ProjectiveAt v (v.regValue .rsi) selected := by
    rw [srcV]
    exact chosen.of_bytes_eq (fun i hi => scalar_call_byte (frameOffset := 408)
      (by decide) state effect (by decide) (by decide) hi)
  obtain ⟨u, result, valueU⟩ := Projective.projective_add_correct cp valueV chosenV
  exact ⟨u, finish_call pre state run ready effect dstV
    (by decide) (by decide) (by decide) result valueU⟩

end P256.Proofs.Verifying.Combination.Loop.Multi
