import P256.Proofs.Projective.Multiply.Machine.Loop.Call.Result
import P256.Proofs.Projective.Multiply.Machine.Loop.Call.Site
import P256.Proofs.Projective.Add
import P256.Proofs.Program.CalleeStack

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Loop

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

def addLayout : StackCallLayout 1400 96 96 920 :=
  ⟨384, 240, 144, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem add_call [Bindings] {s t : RamState} {boundary : ReturnBoundary} {left right : Projective}
    (pre : Pre s boundary) (state : FrameState s t 96 1400 376)
    (site : CallSite 0x1051f0)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 site.offset)
    (dst : t.regValue .rdi = stackPtr s - 144)
    (src : t.regValue .rsi = stackPtr s - 240)
    (leftAt : ProjectiveAt t (stackPtr s - 144) left)
    (rightAt : ProjectiveAt t (stackPtr s - 240) right) :
    ∃ u, PointCallResult s t u boundary site.returnRip 144 (left.add right) := by
  obtain ⟨v, run, ready, effect⟩ := call_site pre state site
    (inProgram_of_textOffset 0x51f0 (by decide)) rip
  have stateV := state.after_call pre.toCalleePre (by decide) (by decide) ready effect
  have dstV : v.regValue .rdi = stackPtr s - 144 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans dst
  have srcV : v.regValue .rsi = stackPtr s - 240 :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans src
  have cp := CalleePre.of_stack pre.toCalleePre addLayout stateV.bindingsSupported stateV.machine stateV.directionFlag
    stateV.loaded stateV.allocated effect.rip stateV.rsp srcV dstV (call_return_program site effect)
  have leftV : ProjectiveAt v (v.regValue .rdi) left := by
    rw [dstV]
    exact leftAt.of_bytes_eq (fun i hi => scalar_call_byte (by decide) state effect (by decide) (by decide) hi)
  have rightV : ProjectiveAt v (v.regValue .rsi) right := by
    rw [srcV]
    exact rightAt.of_bytes_eq (fun i hi => scalar_call_byte (by decide) state effect (by decide) (by decide) hi)
  obtain ⟨u, result, value⟩ := projective_add_correct cp leftV rightV
  exact ⟨u, finish_call pre state run ready effect dstV (by decide) (by decide) (by decide) result value⟩

def initialAdd : CallSite 0x1051f0 :=
  ⟨0x32ea, 0x1f01, by decide +kernel, by decide +kernel, by decide +kernel⟩

def roundAdd : CallSite 0x1051f0 :=
  ⟨0x33a8, 0x1e43, by decide +kernel, by decide +kernel, by decide +kernel⟩

end P256.Proofs.Projective.Multiply.Machine.Loop
