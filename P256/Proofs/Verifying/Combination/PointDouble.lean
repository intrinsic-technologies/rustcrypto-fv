import P256.Proofs.Verifying.Combination.PointCall
import P256.Proofs.Projective.Multiply.Machine.Loop.Call.Site
import P256.Proofs.Projective.Double
import P256.Proofs.Program.CalleeStack

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame
open P256.Proofs.Projective.Multiply.Machine.Loop (CallSite call_return_program)

theorem projective_call [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {target : BitVec 64} (pre : Return.Pre s boundary) (state : State s t)
    (site : CallSite target) (targetProg : InProgram target)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 site.offset) :
    ∃ v, Advances boundary 1 t v ∧ ReadyToStep v ∧
      (callEffect (fun _ => target) site.returnRip t).Holds t v := by
  have low := Program.inProgram_low targetProg
  have step := scalar_call (frameOffset := 408) pre (by decide) (by decide) state
    site.offset site.disp (Nat.le_of_lt site.bounded) site.bytes
    (by rw [site.target_eq]; exact low) (by rw [site.target_eq]; exact targetProg) rip
  simpa only [site.target_eq, CallSite.returnRip] using step

def pointDoubleSite : CallSite 0x105d80 :=
  ⟨0xf190, 0xffff6beb, by decide, by decide +kernel, by decide⟩

def pointDoubleLayout : StackCallLayout 1432 0 96 1016 :=
  ⟨416, 144, 144, by decide, by decide, by decide, by decide,
    by decide, by decide, Or.inl (by decide)⟩

theorem point_double [Bindings] {s t : RamState} {boundary : ReturnBoundary} {point : Projective}
    (pre : Return.Pre s boundary) (state : State s t) (rip : t.RIP = 0x10f190)
    (dst : t.regValue .rdi = stackPtr s - 144)
    (input : ProjectiveAt t (stackPtr s - 144) point) :
    ∃ u, PointCallResult s t u boundary 0x10f195 144 point.double := by
  obtain ⟨v, run, ready, effect⟩ := projective_call pre state pointDoubleSite
    (inProgram_of_textOffset 0x5d80 (by decide)) rip
  have stateV := state.after_call pre (by decide) (by decide) ready effect
  have dstV : v.regValue .rdi = stackPtr s - 144 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans dst
  have cp := CalleePre.of_stack (childInputRegister := .rdi) pre pointDoubleLayout
    stateV.bindingsSupported stateV.machine stateV.directionFlag stateV.loaded stateV.allocated
    effect.rip stateV.rsp dstV dstV (call_return_program pointDoubleSite effect)
  have inputV : ProjectiveAt v (v.regValue .rdi) point := by
    rw [dstV]
    exact input.of_bytes_eq (fun i hi => scalar_call_byte (frameOffset := 408)
      (by decide) state effect (by decide) (by decide) hi)
  obtain ⟨u, result, value⟩ := Projective.projective_double_correct cp inputV
  exact ⟨u, finish_call pre state run ready effect dstV
    (by decide) (by decide) (by decide) result value⟩

end P256.Proofs.Verifying.Combination.Loop.Multi
