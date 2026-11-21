import P256.Proofs.Projective.Multiply.Machine.Loop.Call.Result
import P256.Proofs.Projective.Multiply.Machine.Loop.Call.Site
import P256.Proofs.Projective.Double
import P256.Proofs.Program.CalleeStack

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Loop

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

def doubleLayout : StackCallLayout 1400 0 96 1016 :=
  ⟨384, 336, 336, by decide, by decide, by decide, by decide, by decide, by decide, Or.inl (by decide)⟩

theorem double_call [Bindings] {s t : RamState} {boundary : ReturnBoundary} {point : Projective}
    (pre : Pre s boundary) (state : FrameState s t 96 1400 376)
    (site : CallSite 0x105d80)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 site.offset)
    (dst : t.regValue .rdi = stackPtr s - 336)
    (input : ProjectiveAt t (stackPtr s - 336) point) :
    ∃ u, PointCallResult s t u boundary site.returnRip 336 point.double := by
  obtain ⟨v, run, ready, effect⟩ := call_site pre state site
    (inProgram_of_textOffset 0x5d80 (by decide)) rip
  have stateV := state.after_call pre.toCalleePre (by decide) (by decide) ready effect
  have dstV : v.regValue .rdi = stackPtr s - 336 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans dst
  have cp := CalleePre.of_stack (childInputRegister := .rdi) pre.toCalleePre doubleLayout
    stateV.bindingsSupported stateV.machine stateV.directionFlag stateV.loaded stateV.allocated
    effect.rip stateV.rsp dstV dstV (call_return_program site effect)
  have inputV : ProjectiveAt v (v.regValue .rdi) point := by
    rw [dstV]
    exact input.of_bytes_eq (fun i hi =>
      scalar_call_byte (by decide) state effect (by decide) (by decide) hi)
  obtain ⟨u, result, value⟩ := projective_double_correct cp inputV
  exact ⟨u, finish_call pre state run ready effect dstV
    (by decide) (by decide) (by decide) result value⟩

def firstDouble : CallSite 0x105d80 :=
  ⟨0x334b, 0x2a30, by decide +kernel, by decide +kernel, by decide +kernel⟩

def nextDouble (index : Fin 3) : CallSite 0x105d80 :=
  ⟨0x3353+8*index.val, BitVec.ofNat 32 (0x2a28-8*index.val), by have := index.isLt; omega,
    by rcases index with ⟨i, hi⟩; have cases : i=0 ∨ i=1 ∨ i=2 := by omega
       rcases cases with rfl | rfl | rfl <;> dsimp only [Fin.val_mk] <;> decide +kernel,
    by rcases index with ⟨i, hi⟩; have cases : i=0 ∨ i=1 ∨ i=2 := by omega
       rcases cases with rfl | rfl | rfl <;> dsimp only [Fin.val_mk] <;> decide +kernel⟩

end P256.Proofs.Projective.Multiply.Machine.Loop
