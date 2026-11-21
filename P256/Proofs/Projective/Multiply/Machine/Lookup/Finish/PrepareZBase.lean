import P256.Proofs.Projective.Multiply.Machine.Lookup.Interface
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.Instructions.MovzxByte
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Add.Generated.Imm32.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Projective.Multiply.Machine.Lookup.Finishing

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def prepareZBase0Bytes : List UInt8 := [0x48,0x8d,0x9c,0x24,0x18,0x1,0x0,0x0]

def prepareZBase0Effect (s : RamState) : Effect :=
  { rip := 0x104889
    writes := [⟨(Operand.reg 3 : Operand 64), (s.regValue .rsp) + 280⟩] }

set_option maxHeartbeats 800000 in
theorem prepareZBase0_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x104881)
      (codeRange 0x104881 prepareZBase0Bytes) (Effect.post prepareZBase0Effect) := by
  advance_begin (lea_r64_effect_step 0x104881 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d32 280)) (by decide +kernel) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x4889 (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [prepareZBase0Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareZBase0Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [prepareZBase0Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareZBase0Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]

end P256.Proofs.Projective.Multiply.Machine.Lookup.Finishing
