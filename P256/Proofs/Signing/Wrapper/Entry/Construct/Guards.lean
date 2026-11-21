import P256.Proofs.Signing.Wrapper.Entry.Construct.Memory
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Entry.Construct

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

theorem count_branch [Bindings] {initial s : RamState} {secret message : ByteArray}
    (ctx : Context initial secret message) (state : State initial s 520)
    (rip : s.RIP=0x1026fc) (value : s.regValue .r13=2) :
    ∃ t, Advances (returnBoundary initial) 2 s t ∧ State initial t 520 ∧
      t.RIP=0x102706 ∧ AgreesExcept [.flags,.rip] s t := by
  obtain ⟨slices,call⟩ := ctx.call
  have outside := outer_boundary call ctx.machine ctx.bindingsSupported
  obtain ⟨a,runA,readyA,effectA⟩ := (cmp_r64_imm8_effect_step 0x1026fc 0x49 0xfd 1 (by simp [RexWPrefix]) rfl rfl).advances
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x26fc _
      (by decide) (by decide +kernel)) rip
    (boundary_ne_program outside (inProgram_of_textOffset 0x2700 (by decide)))
  have agA : AgreesExcept [.flags,.rip] s a := effectA.agrees
  have memory := agA.external (by simp [Component.Covers])
  have zf : (StatusFlags.ofRFLAGS a.RFLAGS).ZF=false := by
    have h := effectA.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS a.RFLAGS).ZF=(subSpec (s.regValue .r13) 1).2.ZF at h
    rw [value] at h
    exact h
  have next : (jccEffect 0x102700 6 4 ((0x425 : BitVec 32).signExtend 64) a).rip=0x102706 := by
    simp [jccEffect,branchEffect,condHolds,zf]
  obtain ⟨t,runB,readyB,effectB⟩ := (jcc_rel32_effect_step 0x102700 4 0x425).advances readyA
    (programText_slice ((programLoaded_codeIn state.loaded).of_external_eq memory)
      0x2700 _ (by decide) (by decide +kernel)) ⟨effectA.rip,by intro; decide⟩
    (by rw [next]; exact boundary_ne_program outside (inProgram_of_textOffset 0x2706 (by decide)))
  have ag : AgreesExcept [.flags,.rip] s t := (agA.trans effectB.agrees).mono (by simp [jccEffect])
  exact ⟨t,runA.trans runB,after ctx state (runA.trans runB) readyB ag
    (by intro c hc a ha; simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
        rcases hc with rfl | rfl <;> exact ha.elim)
    (by simp) (by simp),effectB.rip.trans next,ag⟩

end P256.Proofs.Signing.Wrapper.Entry.Construct
