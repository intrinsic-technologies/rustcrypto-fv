import P256.Proofs.Generate.Wrapper.Tail.Registers
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace P256.Proofs.Generate.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program

theorem encode_arguments [Bindings] {initial s : RamState}
    (state : State initial s 264) (outside : ¬ InProgram (returnBoundary initial).rip)
    (rip : s.RIP = 0x106dad) (buffer : s.regValue .r15 = stackPtr initial-184) :
    ∃ t, State initial t 264 ∧ t.RIP = 0x106db5 ∧
      t.regValue .rdi = stackPtr initial-256 ∧ t.regValue .rsi = stackPtr initial-184 ∧
      t.regValue .r15 = stackPtr initial-184 ∧ t.external = s.external := by
  obtain ⟨a,runA,readyA,effectA⟩ :=
    (lea_r64_effect_step 0x106dad 0x48 (by simp [RexWPrefix]) 7
      (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0x6dad _
        (by decide) (by decide +kernel)) rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x6db2 (by decide)))
  have ga : AgreesExcept [.reg 7,.rip] s a := effectA.agrees
  have ma := ga.external (by simp [Component.Covers])
  obtain ⟨t,runT,readyT,effectT⟩ :=
    (mov_r64_r64_effect_step 0x106db2 0x4c 0xfe (by simp [RexWPrefix]) rfl).advances
      readyA (programText_slice ((programLoaded_codeIn state.loaded).of_external_eq ma)
        0x6db2 _ (by decide) (by decide +kernel)) effectA.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x6db5 (by decide)))
  have gt : AgreesExcept [.reg 6,.rip] a t := effectT.agrees
  have ag : AgreesExcept [.reg 7,.reg 6,.rip] s t :=
    (ga.trans gt).mono (by simp)
  refine ⟨t,state.after_registers (runA.trans runT) readyT ag
    (by simp [Component.Covers]) (by simp) (by simp),effectT.rip,?_,?_,?_,
    ag.external (by simp [Component.Covers])⟩
  · have dst : a.regValue .rdi = stackPtr s+8 := effectA.writes
    rw [state.rsp] at dst
    have h : t.regValue .rdi = stackPtr initial - 264 + 8 := (gt.read (n := 64) (r := 7) (by simp)).trans dst
    simpa only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd] using h
  · exact effectT.writes.trans ((ga.read (n := 64) (r := 15) (by simp)).trans buffer)
  · exact (ag.read (n := 64) (r := 15) (by simp)).trans buffer

end P256.Proofs.Generate.Wrapper
