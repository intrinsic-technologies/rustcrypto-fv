import P256.Proofs.Program.Code
import P256.Proofs.Program.State
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Finish.Return

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem control [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (outside : ¬ InProgram boundary.rip) (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (rip : s.RIP=0x106cab) (capacity : 7<(s.regValue .r8).toNat) :
    ∃ t, Advances boundary 6 s t ∧ ReadyToStep t ∧ t.RIP=0x106cd5 ∧
      t.regValue .rax=32 ∧ AgreesExcept [.reg 0,.reg 2,.flags,.rip] s t := by
  obtain ⟨a,ha,ra,ea⟩ := (xor_r32_r32_effect_step 0x106cab 0xd2 (by decide)).advances ready
    (programText_slice (programLoaded_codeIn loaded) 0x6cab _ (by decide) (by decide +kernel))
    rip (boundary_ne_program outside (inProgram_of_textOffset 0x6cad (by decide)))
  have fa : AgreesExcept [.reg 2,.flags,.rip] s a := ea.agrees
  have ma := fa.external (by simp [Component.Covers])
  have dx : a.regValue .rdx=0 := by
    have h := ea.writes
    change a.regValue .rdx = (((Operand.reg 2 : Operand 32).read s) ^^^
      ((Operand.reg 2 : Operand 32).read s)).setWidth 64 at h
    simpa only [BitVec.xor_self,BitVec.setWidth_zero,BitVec.ofNat_eq_ofNat] using h
  obtain ⟨b,hb,rb,eb⟩ := (mov_r32_imm32_effect_step 0x106cad 0xb8 (by decide) 32).advances ra
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq ma) 0x6cad _
      (by decide) (by decide +kernel)) ea.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0x6cb2 (by decide)))
  have fb : AgreesExcept [.reg 0,.rip] a b := eb.agrees
  have mb := (fb.external (by simp [Component.Covers])).trans ma
  have ax : b.regValue .rax=32 := eb.writes
  have dxB : b.regValue .rdx=0 := (fb.read (n := 64) (r := 2) (by simp)).trans dx
  obtain ⟨c,hc,rc,ec⟩ := (cmp_r32_imm8_effect_step 0x106cb2 0xfa 1
    (by decide) (by decide)).advances rb
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq mb) 0x6cb2 _
      (by decide) (by decide +kernel)) eb.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0x6cb5 (by decide)))
  have fc : AgreesExcept [.flags,.rip] b c := ec.agrees
  have mc := (fc.external (by simp [Component.Covers])).trans mb
  have zf : (StatusFlags.ofRFLAGS c.RFLAGS).ZF=false := by
    have h := ec.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS c.RFLAGS).ZF=(cmpSpec ((b.regValue .rdx).setWidth 32) 1).ZF at h
    rw [h,dxB]; decide +kernel
  obtain ⟨d,step,rd,raw⟩ := jcc_rel8_effect_step 0x106cb5 5 0x18 c rc
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq mc) 0x6cb5 _
      (by decide) (by decide +kernel)) ⟨ec.rip,by intro; decide⟩
  have ed := jccEffect_taken (show condHolds 5 (StatusFlags.ofRFLAGS c.RFLAGS)=true by
    change (!(StatusFlags.ofRFLAGS c.RFLAGS).ZF)=true; rw [zf]; rfl) raw
  have hd : Advances boundary 1 c d := Advances.of_step step (.inl (by
    rw [ed.rip]
    exact boundary_ne_program outside (inProgram_of_textOffset 0x6ccf (by decide))))
  have fd : AgreesExcept [.rip] c d := ed.agrees
  have md := (fd.external (by simp [Component.Covers])).trans mc
  have cap : 7<(d.regValue .r8).toNat := by
    have eq : d.regValue .r8=s.regValue .r8 := (((fa.trans fb).trans fc).trans fd).read (n := 64) (r := 8) (by simp)
    rw [eq]
    exact capacity
  obtain ⟨e,he,re,ee⟩ := (cmp_r64_imm8_effect_step 0x106ccf 0x49 0xf8 7
    (by simp [RexWPrefix]) (by decide) (by decide)).advances rd
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq md) 0x6ccf _
      (by decide) (by decide +kernel)) ed.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0x6cd3 (by decide)))
  have fe : AgreesExcept [.flags,.rip] d e := ee.agrees
  have me := (fe.external (by simp [Component.Covers])).trans md
  have cf : (StatusFlags.ofRFLAGS e.RFLAGS).CF=false := by
    have h := ee.flags.1
    change (StatusFlags.ofRFLAGS e.RFLAGS).CF=decide ((d.regValue .r8).toNat<7) at h
    rw [h]; exact decide_eq_false (by omega)
  have zfE : (StatusFlags.ofRFLAGS e.RFLAGS).ZF=false := by
    have h := ee.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS e.RFLAGS).ZF=((d.regValue .r8-7)==0) at h
    rw [h]
    apply Bool.eq_false_iff.mpr
    intro hz
    have eq : d.regValue .r8=7 := by
      simpa only [BitVec.ofNat_eq_ofNat,BitVec.reduceAdd] using BitVec.sub_eq_iff_eq_add.mp (of_decide_eq_true hz)
    rw [eq] at cap
    contradiction
  obtain ⟨t,step,rt,raw⟩ := jcc_rel8_effect_step 0x106cd3 6 0x37 e re
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq me) 0x6cd3 _
      (by decide) (by decide +kernel)) ⟨ee.rip,by intro; decide⟩
  have et := jccEffect_not_taken (show condHolds 6 (StatusFlags.ofRFLAGS e.RFLAGS)=false by
    change ((StatusFlags.ofRFLAGS e.RFLAGS).CF || (StatusFlags.ofRFLAGS e.RFLAGS).ZF)=false
    rw [cf,zfE]; rfl) raw
  have ht : Advances boundary 1 e t := Advances.of_step step (.inl (by
    rw [et.rip]
    exact boundary_ne_program outside (inProgram_of_textOffset 0x6cd5 (by decide))))
  refine ⟨t,((((ha.trans hb).trans hc).trans hd).trans he).trans ht,rt,et.rip,?_,?_⟩
  · exact ((((fc.trans fd).trans fe).trans et.agrees).read (n := 64) (r := 0) (by simp)).trans ax
  · exact (((((fa.trans fb).trans fc).trans fd).trans fe).trans et.agrees).mono (by simp)

end P256.Proofs.EcdhWrapper.Finish.Return
