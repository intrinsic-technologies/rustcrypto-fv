import P256.Proofs.EcdhWrapper.Nonzero.Choice
import P256.Proofs.EcdhWrapper.Nonzero.Memory
import P256.Proofs.Common.Instructions.ByteLogic.AndReg
import P256.Proofs.Common.Instructions.ByteOps.Effects
import P256.Proofs.Common.Instructions.MovzxByte
import P256.Proofs.Common.Der.Decode.Header.Control

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Scalar

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions.ByteLogic
open P256.Proofs.Common.Instructions.ByteOps.ByteOps
open P256.Proofs.Common.Instructions.MovzxByte
open P256.Proofs.Common.Der.Decode.Header

theorem validity_arguments [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (outside : ¬InProgram boundary.rip) (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (rip : s.RIP = 0x106963) (al : (s.regValue .rax).setWidth 8 = 1)
    (bpl : (s.regValue .rbp).setWidth 8 = 1) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ t.RIP = 0x106969 ∧
      t.regValue .rdi = 1 ∧ AgreesExcept [.reg 0,.reg 7,.flags,.rip] s t := by
  obtain ⟨a,runA,readyA,ea⟩ :=
    (and_r8_r8_rex_effect_step 0x106963 0x40 0xe8 (by simp [RexPrefix]) rfl).advances
      ready (programText_slice (programLoaded_codeIn loaded) 0x6963 _
        (by decide) (by decide +kernel)) rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x6966 (by decide)))
  have ga : AgreesExcept [.reg 0,.flags,.rip] s a := ea.agrees
  have memory := ga.external (by simp [Component.Covers])
  obtain ⟨t,runT,readyT,et⟩ := (movzx_r32_r8_effect_step 0x106966 0xf8 rfl (by decide)).advances
    readyA (programText_slice ((programLoaded_codeIn loaded).of_external_eq memory)
      0x6966 _ (by decide) (by decide +kernel)) ea.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0x6969 (by decide)))
  refine ⟨t,runA.trans runT,readyT,et.rip,?_,
    (ga.trans et.agrees).mono (by simp [movzxR32R8Effect,Effect.components,gprNumber,modrmReg,modrmRm])⟩
  have value : a.regValue .rax =
      mergeGPR 8 ((s.regValue .rax).setWidth 8 &&& (s.regValue .rbp).setWidth 8)
        (s.regValue .rax) := ea.writes
  have result : t.regValue .rdi = ((a.regValue .rax).setWidth 8).setWidth 64 := et.writes
  rw [result,value,mergeGPR_low8,al,bpl]
  rfl

theorem validity_branch [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (outside : ¬InProgram boundary.rip) (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (rip : s.RIP = 0x10696e) (al : (s.regValue .rax).setWidth 8 = 1) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ t.RIP = 0x106976 ∧
      AgreesExcept [.flags,.rip] s t := by
  obtain ⟨a,runA,readyA,ea⟩ := (cmp_al_imm8_effect_step 0x10696e 1).advances
    ready (programText_slice (programLoaded_codeIn loaded) 0x696e _
      (by decide) (by decide +kernel)) rip
    (boundary_ne_program outside (inProgram_of_textOffset 0x6970 (by decide)))
  have ga : AgreesExcept [.flags,.rip] s a := ea.agrees
  have memory := ga.external (by simp [Component.Covers])
  have flag : (StatusFlags.ofRFLAGS a.RFLAGS).ZF = true := by
    have h := ea.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS a.RFLAGS).ZF =
      (cmpSpec ((s.regValue .rax).setWidth 8) 1).ZF at h
    rw [h,cmpSpec_ZF,al]
    rfl
  obtain ⟨t,runT,readyT,et⟩ := (jcc_rel32_not_taken_effect_step 0x106970 5 0x378).advances
    readyA (programText_slice ((programLoaded_codeIn loaded).of_external_eq memory)
      0x6970 _ (by decide) (by decide +kernel)) ⟨ea.rip,by simp [condHolds,flag]⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6976 (by decide)))
  exact ⟨t,runA.trans runT,readyT,et.rip,(ga.trans et.agrees).mono (by simp)⟩

theorem validity [bindings : Bindings] {initial s : RamState} {secret peer : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (outside : ¬InProgram (returnBoundary initial).rip)
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome)
    (rip : s.RIP = 0x106963) (rsp : stackPtr s = stackPtr initial-504)
    (al : (s.regValue .rax).setWidth 8 = 1) (bpl : (s.regValue .rbp).setWidth 8 = 1) :
    ∃ t, Advances (returnBoundary initial) 10 s t ∧ ReadyToStep t ∧
      t.RIP = 0x106976 ∧ stackPtr t = stackPtr s ∧
      AgreesExcept (Nonzero.clobbers initial) s t := by
  obtain ⟨a,ra,readyA,ripA,diA,ga⟩ := validity_arguments outside ready loaded rip al bpl
  have memA := ga.external (by simp [Component.Covers])
  have loadedA : ProgramLoaded a := by simpa only [ProgramLoaded,memA] using loaded
  have spA : stackPtr a = stackPtr initial-504 :=
    (ga.read (n := 64) (r := 4) (by simp)).trans rsp
  obtain ⟨b,rb,readyB,ripB,spB,valueB,gb⟩ := Nonzero.choice_at call outside readyA loadedA
    (fun x hx => ga.grow x (grow x hx)) 0x6969 0x12702
    (by decide) (by decide +kernel) (by decide) ripA spA
  have total : AgreesExcept (Nonzero.clobbers initial) s b :=
    (ga.trans gb).mono (by simp [Nonzero.clobbers])
  have alB : (b.regValue .rax).setWidth 8 = 1 := by rw [valueB,diA]; rfl
  obtain ⟨t,rt,readyT,ripT,gt⟩ := validity_branch outside readyB
    (Nonzero.loaded_after call total loaded) ripB alB
  refine ⟨t,(ra.trans rb).trans rt,readyT,ripT,?_,(total.trans gt).mono (by simp [Nonzero.clobbers])⟩
  exact (gt.read (n := 64) (r := 4) (by simp)).trans
    (spB.trans (ga.read (n := 64) (r := 4) (by simp)))

end P256.Proofs.EcdhWrapper.Scalar
