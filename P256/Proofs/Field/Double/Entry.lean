import P256.Proofs.Field.Interface
import P256.Proofs.Program.CalleeRegisters
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Field.Double

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem enter [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x1137f0 32 32 16) :
    ∃ t, Advances boundary 2 s t ∧ BinaryFieldPre t boundary 0x113e10 16 ∧
      AgreesExcept [.reg 2, .rip] s t ∧ t.regValue .rdx = t.regValue .rsi := by
  obtain ⟨a, runa, readya, effecta⟩ :=
    (mov_r64_r64_effect_step 0x1137f0 0x48 0xf2
      (by constructor <;> decide +kernel) rfl).advances
      (readyToStep pre.machine pre.bindingsSupported)
      (programText_slice (programLoaded_codeIn pre.loaded) 0x137f0 _
        (by decide) (by decide +kernel)) pre.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x137f3 (by decide)))
  have aga : AgreesExcept [.reg 2, .rip] s a := effecta.agrees
  have memorya := aga.external (by simp [Component.Covers])
  obtain ⟨t, runt, readyt, effectt⟩ :=
    (jmp_rel32_effect_step 0x1137f3 1560 (by decide +kernel)).advances readya
      (programText_slice ((programLoaded_codeIn pre.loaded).of_external_eq memorya)
        0x137f3 _ (by decide) (by decide +kernel)) effecta.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x13e10 (by decide)))
  have agt : AgreesExcept [.rip] a t := effectt.agrees
  have ag : AgreesExcept [.reg 2, .rip] s t :=
    (aga.trans agt).mono (by simp)
  have child := pre.after_registers readyt ag (ag.external (by simp [Component.Covers]))
    (ag.read (n := 64) (r := 4) (by simp)) (ag.read (n := 64) (r := 6) (by simp))
    (ag.read (n := 64) (r := 7) (by simp))
    (ag.directionFlagClear (by simp) pre.directionFlag) effectt.rip
  have right : t.regValue .rdx = t.regValue .rsi := by
    have source : t.regValue .rsi = s.regValue .rsi :=
      ag.read (n := 64) (r := 6) (by simp)
    rw [source]
    exact (agt.read (n := 64) (r := 2) (by simp)).trans effecta.writes
  have region : registerRegion t .rdx 32 = registerRegion t .rsi 32 := by
    simp only [registerRegion, right]
  refine ⟨t, runa.trans runt, ⟨child, ?_, ?_, ?_, ?_⟩, ag, right⟩
  · simpa only [region] using child.inputBounded
  · simpa only [region] using child.inputAllocated
  · rw [region]
    exact child.separation ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide)
  · rw [region]
    exact child.separation ⟨0, by decide⟩ ⟨2, by decide⟩ (by decide)

end P256.Proofs.Field.Double
