import Hkdf.Proofs.Key.Hash.Copy.Setup
import Hkdf.Proofs.Common.Instructions.RepMovsq.Memory

set_option autoImplicit false

namespace Hkdf.Proofs.Key.Hash.Copy

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.Instructions

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x116432
  direction : DirectionFlagClear s.RFLAGS
  sourcePointer : s.regValue .r12 = rspOf s + 232
  source : MemReadable s (rspOf s + 232) 104
  destination : CrossPageStore.Writable s (rspOf s + 64) 104
  disjoint : (rspOf s + 64).toNat + 104 ≤ (rspOf s + 232).toNat
  codeApart : RangeApart (rspOf s + 64) 104 0x11643f 3

theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x11643f [0xf3, 0x48, 0xa5]) s :=
  programText_slice (programLoaded_codeIn loaded) 0x1643f [0xf3, 0x48, 0xa5]
    (by decide +kernel) (by decide +kernel)

theorem run [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    (stride : UnitStringStride bindings) (outside : ¬ InProgram boundary.rip)
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (pre : Pre s) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ t.RIP = 0x116442 ∧
      AgreesExcept [.reg 1, .reg 6, .reg 7, .mem (rspOf s + 64) 104, .rip] s t ∧
      (∀ i < 104, t.external[rspOf s + 64 + BitVec.ofNat 64 i]? =
        s.external[rspOf s + 232 + BitVec.ofNat 64 i]?) := by
  obtain ⟨setupFuel, u, setupRun, setupReady, _, setup⟩ :=
    Setup.run boundary outside s ready (Setup.code loaded) pre.rip
  have setupFrame : AgreesExcept [.reg 7, .reg 1, .reg 6, .rip] s u := by
    simpa only [Setup.effect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.cons_append, List.nil_append] using setup.agrees
  have external : u.external = s.external :=
    setupFrame.external (by simp [Component.Covers])
  have rdiValue : rdi.read u = rspOf s + 64 := setup.writes.1
  have count : (rcx.read u).toNat = 13 := by
    have word : rcx.read u = 13 := setup.writes.2.1
    rw [word]
    rfl
  have rsiValue : rsi.read u = rspOf s + 232 :=
    setup.writes.2.2.trans pre.sourcePointer
  have source : MemReadable u (rsi.read u) (8 * 13) := by
    rw [rsiValue]
    exact pre.source.of_external_eq external
  have destination : CrossPageStore.Writable u (rdi.read u) (8 * 13) := by
    rw [rdiValue]
    exact ⟨pre.destination.toMemReadable.of_external_eq external, pre.destination.tables⟩
  have repPre :=
    RepMovsq.pre_of_memory setup.rip
      (by rw [setupFrame.rflags (by simp) (by simp)]; exact pre.direction)
      count source destination
      (by rw [rdiValue, rsiValue]; exact .inr pre.disjoint)
      (by rw [rdiValue]; exact pre.codeApart)
  have repCode : CodeIn (codeRange 0x11643f [0xf3, 0x48, 0xa5]) u :=
    (code loaded).of_external_eq external
  obtain ⟨run, finalReady, effect, copied⟩ :=
    RepMovsq.rep_movsq_execution stride setupReady repCode repPre count
      (boundary_ne_program outside (inProgram_of_textOffset 0x1643f (by decide)))
      (boundary_ne_program outside (inProgram_of_textOffset 0x16442 (by decide)))
  have repFrame : AgreesExcept [.reg 6, .reg 7, .reg 1,
      .mem (rspOf s + 64) 104, .rip] u (nextStates 13 u) := by
    simpa only [repMovsqEffect_components, count, rdiValue, Nat.reduceMul, show max 13 1 = 13 from rfl] using effect.agrees
  refine ⟨setupFuel + 13, nextStates 13 u, ?_, finalReady, effect.rip, ?_, ?_⟩
  · exact setupRun.trans run
  · exact (setupFrame.trans repFrame).mono (by simp)
  · intro i hi
    have byte := copied i hi
    rw [rdiValue, rsiValue, external] at byte
    exact byte

end Hkdf.Proofs.Key.Hash.Copy
