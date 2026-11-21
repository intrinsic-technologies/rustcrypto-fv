import Sha2.Proofs.Wrapper512.Dispatch.Initialize

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Machine.Stages

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Wrapper512

 theorem subframe [Bindings] {v : Variant} {initial s : RamState}
    {inputs : Array Input} (ctx : Context v initial inputs) (ready : ReadyToStep s)
    (loaded : ProgramLoaded s) (rip : s.RIP = v.pc 0xa)
    (rsp : stackPtr s = stackPtr initial - 48) :
    ∃ t, Advances (returnBoundary initial) 1 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = v.pc 0x11 ∧ stackPtr t = stackPtr initial - BitVec.ofNat 64 632 ∧
      AgreesExcept [.reg 4, .flags, .rip] s t := by
  obtain ⟨t, step, readyT, effect⟩ :=
    (sub_r64_imm32_effect_step (v.pc 0xa) 0x48 0xec 584
      (by constructor <;> decide) (by decide) (by decide)).advances ready
      (programText_slice (programLoaded_codeIn loaded) (v.textOffset + 0xa)
        [0x48,0x81,0xec,0x48,0x02,0x00,0x00]
        (by cases v <;> decide) (by cases v <;> decide +kernel)) rip
      (boundary_ne_program (Sha2.Proofs.Wrapper512.Dispatch.returnBoundary_of_call ctx.machine ctx.call) (by
        have hnext : InProgram (v.pc 0x11) := Variant.pc_inProgram v (by decide)
        simpa [subR64Imm32Effect, Variant.pc_add] using hnext))
  have agrees : AgreesExcept [.reg 4, .flags, .rip] s t := effect.agrees
  have loadedT : ProgramLoaded t := by
    intro address byte hfetch
    rw [agrees.external (by simp [Component.Covers])]
    exact loaded address byte hfetch
  have rspT : stackPtr t = stackPtr initial - BitVec.ofNat 64 632 := by
    have h := effect.writes
    simp only [subR64Imm32Effect, Write.AllHold, Operand.read] at h
    change t.regValue .rsp = s.regValue .rsp - BitVec.signExtend 64 584 at h
    rw [← stackPtr_eq_regValue_rsp t, ← stackPtr_eq_regValue_rsp s, rsp] at h
    rw [h]
    change stackPtr initial - BitVec.ofNat 64 48 - BitVec.signExtend 64 (BitVec.ofNat 32 584) = _
    have hs : BitVec.signExtend 64 (BitVec.ofNat 32 584) = BitVec.ofNat 64 584 := by decide +kernel
    rw [hs, BitVec.sub_sub]
    rfl
  have ripT : t.RIP = v.pc 0x11 := by
    rw [effect.rip]
    exact Variant.pc_add v 0xa 7
  exact ⟨t, step, readyT, loadedT, ripT, rspT, agrees⟩

end Sha2.Proofs.Wrapper512.Machine.Stages
