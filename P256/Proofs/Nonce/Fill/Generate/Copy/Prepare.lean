import P256.Proofs.Nonce.Fill.Generate.Interface
import P256.Proofs.Nonce.Fill.Call
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Generate.Copy

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program

structure Prepared [Bindings] (initial s : RamState) (orderAddress : BitVec 64)
    (state : State) : Prop extends Frame initial s, Slots initial s where
  rip : s.RIP = 0x1073d0
  rdi : s.regValue .rdi = initial.regValue .rsi
  rsi : s.regValue .rsi = initial.regValue .rdi + 40
  rdx : s.regValue .rdx = 32
  rbx : s.regValue .rbx = 0x11c930
  rbp : s.regValue .rbp = 32
  r15 : s.regValue .r15 = 32
  generator : GeneratorAt s (initial.regValue .rdi) orderAddress (updateValue state)

theorem prepare [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {original state : State}
    (pre : Pre initial boundary orderAddress original)
    (input : HasValue initial s orderAddress state) :
    ∃ t, Advances boundary 3 s t ∧ Prepared initial t orderAddress state := by
  obtain ⟨a, ra, readya, ea⟩ :=
    (mov_r64_r64_effect_step 0x1073c7 0x4c 0xf7 (by simp [RexWPrefix]) rfl).advances
      (readyToStep input.machine input.bindingsSupported)
      (programText_slice (programLoaded_codeIn input.toFrame.loaded) 0x73c7 _
        (by decide) (by decide +kernel)) input.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x73ca (by decide)))
  have aa : AgreesExcept [.reg 7, .rip] s a := ea.agrees
  have fa := input.toFrame.after_registers readya aa (by simp [Component.Covers]) (by simp)
  obtain ⟨b, rb, readyb, eb⟩ :=
    (mov_r64_r64_effect_step 0x1073ca 0x4c 0xe6 (by simp [RexWPrefix]) rfl).advances
      readya
      (programText_slice (programLoaded_codeIn fa.loaded) 0x73ca _
        (by decide) (by decide +kernel)) ea.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x73cd (by decide)))
  have ab : AgreesExcept [.reg 6, .rip] a b := eb.agrees
  have fb := fa.after_registers readyb ab (by simp [Component.Covers]) (by simp)
  obtain ⟨t, rt, readyt, et⟩ :=
    (mov_r64_r64_effect_step 0x1073cd 0x4c 0xfa (by simp [RexWPrefix]) rfl).advances
      readyb
      (programText_slice (programLoaded_codeIn fb.loaded) 0x73cd _
        (by decide) (by decide +kernel)) eb.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x73d0 (by decide)))
  have agt : AgreesExcept [.reg 2, .rip] b t := et.agrees
  have ft := fb.after_registers readyt agt (by simp [Component.Covers]) (by simp)
  have agrees := (aa.trans ab).trans agt
  have memory := agrees.external (by simp [Component.Covers])
  refine ⟨t, (ra.trans rb).trans rt, ft, input.toSlots.of_memory_eq memory, et.rip,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((ab.trans agt).read (n := 64) (r := 7) (by simp)).trans
      (ea.writes.trans input.r14)
  · exact (agt.read (n := 64) (r := 6) (by simp)).trans
      (eb.writes.trans ((aa.read (n := 64) (r := 12) (by simp)).trans input.r12))
  · exact et.writes.trans
      (((aa.trans ab).read (n := 64) (r := 15) (by simp)).trans input.r15)
  · exact (agrees.read (n := 64) (r := 3) (by simp)).trans input.rbx
  · exact (agrees.read (n := 64) (r := 5) (by simp)).trans input.rbp
  · exact (agrees.read (n := 64) (r := 15) (by simp)).trans input.r15
  · simpa only [GeneratorAt, DrbgAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, memory]
      using input.generator

end P256.Proofs.Nonce.Fill.Generate.Copy
