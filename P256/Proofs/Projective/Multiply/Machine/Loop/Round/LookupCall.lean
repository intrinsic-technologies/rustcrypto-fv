import P256.Proofs.Projective.Multiply.Machine.Loop.Call.Result
import P256.Proofs.Projective.Multiply.Machine.Loop.Call.Site
import P256.Proofs.Projective.Multiply.Machine.Loop.Memory
import P256.Proofs.Projective.Multiply.Machine.Lookup
import P256.Proofs.Program.CalleeStackInput

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Loop.Round

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

def lookupLayout : StackBufferLayout 1400 96 496 :=
  ⟨384, 240, by decide, by decide, by decide, by decide⟩

def lookupSite : CallSite 0x1044a0 :=
  ⟨0x339d, 0x10fe, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem lookup_call [bindings : Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {table : Fin 8 → Projective} {digit : BitVec 8}
    (pre : Pre s boundary) (state : FrameState s t 96 1400 376)
    (rip : t.RIP = 0x10339d)
    (dst : t.regValue .rdi = stackPtr s - 240)
    (src : t.regValue .rsi = s.regValue .rsi)
    (input : Lookup.TableAt s (s.regValue .rsi) table)
    (digitAt : (t.regValue .rdx).setWidth 8 = digit) :
    ∃ u, PointCallResult s t u boundary 0x1033a2 240
      (ProjectiveLookup.signedLookup table digit) := by
  obtain ⟨v, run, ready, effect⟩ := call_site pre state lookupSite
    (inProgram_of_textOffset 0x44a0 (by decide)) rip
  have stateV := state.after_call pre.toCalleePre (by decide) (by decide) ready effect
  have dstV : v.regValue .rdi = stackPtr s - 240 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans dst
  have srcV : v.regValue .rsi = s.regValue .rsi :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans src
  have cp := CalleePre.of_input_and_stack pre.toCalleePre lookupLayout
    stateV.bindingsSupported stateV.machine stateV.directionFlag stateV.loaded stateV.allocated
    effect.rip stateV.rsp srcV dstV (call_return_program lookupSite effect)
  have tableV : Lookup.TableAt v (v.regValue .rsi) table := by
    rw [srcV]
    exact table_at pre.toCalleePre stateV input
  have digitV : (v.regValue .rdx).setWidth 8 = digit := by
    have dx : v.regValue .rdx = t.regValue .rdx := effect.agrees.read (n := 64) (r := 2) (by simp)
    rw [dx]
    exact digitAt
  obtain ⟨u, result, value⟩ := Lookup.lookup_correct bindings v boundary table digit cp tableV digitV
  exact ⟨u, finish_call pre state run ready effect dstV
    (by decide) (by decide) (by decide) result value⟩

end P256.Proofs.Projective.Multiply.Machine.Loop.Round
