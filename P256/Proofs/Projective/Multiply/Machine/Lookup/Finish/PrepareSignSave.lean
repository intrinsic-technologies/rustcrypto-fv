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

def prepareSignSave0Bytes : List UInt8 := [0x89,0xc5]

def prepareSignSave0Effect (s : RamState) : Effect :=
  { rip := 0x10483e
    writes := [⟨(Operand.reg 5 : Operand 64), ((s.regValue .rax).setWidth 32).setWidth 64⟩] }

set_option maxHeartbeats 800000 in
theorem prepareSignSave0_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10483c)
      (codeRange 0x10483c prepareSignSave0Bytes) (Effect.post prepareSignSave0Effect) := by
  advance_begin (mov_r32_r32_effect_step 0x10483c 0xc5 rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x483e (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [prepareSignSave0Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareSignSave0Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [prepareSignSave0Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [prepareSignSave0Effect]
    all_goals solve_by_elim (maxDepth := 20) only [And.intro, Or.inl, Or.inr, Eq.refl]

end P256.Proofs.Projective.Multiply.Machine.Lookup.Finishing
