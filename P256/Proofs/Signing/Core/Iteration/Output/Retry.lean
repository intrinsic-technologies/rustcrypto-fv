import P256.Proofs.Signing.Core.Iteration.Output.Control
import P256.Proofs.Signing.Core.Iteration.Output.Blocks.Retry

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Output

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Program

variable [Bindings] {s t : RamState} {boundary : ReturnBoundary} {state : Nonce.State}
  {secret nonce x y : Nat} {digest : ByteArray}

theorem retry_correct (pre : SignPre s boundary) (input : Computed s t state secret nonce digest x y)
    (rip : t.RIP = 0x10d33e) (tag : memLoad t.external (frameBase s + 528) 64 = 1)
    (null : memLoad t.external (frameBase s + 536) 64 = 0) :
    ∃ fuel u, Advances boundary fuel t u ∧ u.RIP = 0x10caa5 ∧ Loop s u state := by
  obtain ⟨n,a,runA,fa,ipa,r12,_,aga⟩ := dispatch pre input.frame rip tag
  have ipa' : a.RIP = 0x10d358 := by simpa using ipa
  have zero : a.regValue .r12 = 0 := r12.trans null
  obtain ⟨b,runB,readyB,eb⟩ :=
    (test_r64_r64_effect_step 0x10d358 0x4d 0xe4 (by simp [RexWPrefix]) rfl).advances
      (readyToStep fa.machine fa.bindingsSupported)
      (programText_slice (programLoaded_codeIn fa.loaded) 0xd358 _ (by decide) (by decide +kernel)) ipa'
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xd35b (by decide)))
  have ab : AgreesExcept [.flags,.rip] a b := eb.agrees
  have fb := after_registers fa readyB eb.agrees (by simp [Component.Covers])
    (by simp) (by simp) (by simp) (by simp)
  have flag : (StatusFlags.ofRFLAGS b.RFLAGS).ZF = true := by
    have h := eb.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS b.RFLAGS).ZF = (testSpec (oracleBit a.oracle) (a.regValue .r12) (a.regValue .r12)).ZF at h
    rw [zero] at h
    exact h
  obtain ⟨c,stepC,readyC,ec⟩ := jcc_rel32_effect_step 0x10d35b 4 0xfffff73f b readyB
    (programText_slice (programLoaded_codeIn fb.loaded) 0xd35b _ (by decide) (by decide +kernel))
    ⟨eb.rip,fun _ => by decide⟩
  have ipc : c.RIP = 0x10caa0 := by
    have h := ec.rip
    change c.RIP = (if (StatusFlags.ofRFLAGS b.RFLAGS).ZF then 0x10caa0 else 0x10d361) at h
    simpa only [flag,ite_true] using h
  have runC : Advances boundary 1 b c := Advances.of_step stepC (.inl (by
    rw [ipc]; exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xcaa0 (by decide))))
  have ac0 : AgreesExcept [.rip] b c := ec.agrees
  have fc := after_registers fb readyC ac0 (by simp [Component.Covers])
    (by simp) (by simp) (by simp) (by simp)
  obtain ⟨m,u,runU,readyU,_,eu⟩ := Blocks.Retry_correct boundary pre.outerBoundary c readyC
    (programText_slice (programLoaded_codeIn fc.loaded) 0xcaa0 Blocks.RetryBytes (by decide) (by decide +kernel)) ⟨ipc⟩
  have ag : AgreesExcept [.reg 12,.reg 3,.flags,.rip] t u :=
    (((aga.trans ab).trans ac0).trans eu.agrees).mono
      (by simp [Blocks.RetryEffect,Effect.components])
  have memory := ag.external (by simp [Component.Covers])
  have fu := after_registers input.frame readyU ag (by simp [Component.Covers])
    (by simp) (by simp) (by simp) (by simp)
  refine ⟨n+1+1+m,u,((runA.trans runB).trans runC).trans runU,eu.rip,
    ⟨fu,?_,?_,?_,?_,?_,?_,?_⟩⟩
  · exact NextNonce.arguments_copy input.arguments (fun _ _ => congrArg (·[_]?) memory)
  · exact input.generator.copy (fun _ _ => congrArg (·[_]?) memory)
      ⟨input.generator.2.1.1,fun i hi => by rw [memory]; exact input.generator.2.1.2 i hi⟩
  · exact (ag.read (n:=64) (r:=5) (by simp)).trans input.rbp
  · have h : u.regValue .rbx = stackPtr c + 40 := eu.writes
    exact h.trans (congrArg (·+40) fc.rsp)
  · exact (ag.read (n:=64) (r:=13) (by simp)).trans input.r13
  · exact (ag.read (n:=64) (r:=14) (by simp)).trans input.r14
  · exact (ag.read (n:=64) (r:=15) (by simp)).trans input.r15

end P256.Proofs.Signing.Core.Iteration.Output
