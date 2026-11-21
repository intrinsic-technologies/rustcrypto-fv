import P256.Proofs.Sec1.Decompress.Select.Parity.Value
import P256.Proofs.Sec1.Decompress.State
import P256.Proofs.Sec1.Decompress.Select.Parity.Last

set_option autoImplicit false

open P256.Proofs.Sec1Serialize (canonicalLimb)
open P256.Proofs.Sec1Serialize.Conversion (compilerConversionBV compilerConversionBV_of_montgomeryAt)
open P256.Proofs.Sec1Serialize.Conversion.Montgomery (compilerRoundBV)
open P256.Proofs.Common.Instructions (addR64M64Effect addR64M64Effect_components add_r64_m64_effect_step mulHigh64 mulR64Effect mulR64Effect_components mul_r64_effect_step)
open P256.Proofs.Common.Instructions.ByteLogic (andR8Imm8Effect and_sil_one_effect_step)
open P256.Proofs.Common.Instructions.Carry (adcR32Imm8Effect adcR32Imm8Effect_components adcR32R32Effect adcR32R32Effect_components adcR64Imm8Effect adcR64Imm8Effect_components adcR64R64Effect adcR64R64Effect_components adcSpec adcSpec_result adc_r32_imm8_effect_step adc_r32_r32_effect_step adc_r32_r32_rex_effect_step adc_r64_imm8_effect_step adc_r64_r64_effect_step)
open P256.Proofs.Common.Instructions.MovzxByte (movzxR32R8Effect movzx_r32_r8_rex_effect_step)
open P256.Proofs.Common.Instructions.Setb (setccR8Effect setccR8Effect_components setcc_r8_effect_step setcc_r8_rex_effect_step)
open P256.Proofs.Common.Instructions.ShiftLeft (shlR64Effect shlR64Effect_components shl_r64_imm8_effect_step)
open P256.Proofs.Program (CalleePre boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice readyToStep)
open P256.Proofs.Field (MontgomeryAt)

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

namespace P256.Proofs.Sec1.Decompress.Select.Parity

private theorem memory_eq {u t : RamState} (h : AgreesExcept registers u t) :
    t.external = u.external := h.external (by simp [registers, Component.Covers])

private theorem stack_eq {u t : RamState} (h : AgreesExcept registers u t) :
    stackPtr t = stackPtr u := h.read (n := 64) (r := 4) (by simp [registers])

private theorem readable_of_agrees {u t : RamState} (h : AgreesExcept registers u t)
    (readable : ∀ i < 4, MemReadable u (stackPtr u + BitVec.ofNat 64 (152+8*i)) 8) :
    ∀ i < 4, MemReadable t (stackPtr t + BitVec.ofNat 64 (152+8*i)) 8 := by
  intro i hi
  rw [stack_eq h]
  exact (readable i hi).of_external_eq (memory_eq h)

theorem machine [Bindings] {u : RamState} {boundary : ReturnBoundary}
    (hout : ¬ InProgram boundary.rip) (ready : ReadyToStep u) (loaded : ProgramLoaded u)
    (rip : u.RIP = 0x10ff77)
    (constant : (Operand.reg 14 : Operand 64).read u = 0xffffffff00000001)
    (readable : ∀ i < 4, MemReadable u (stackPtr u + BitVec.ofNat 64 (152+8*i)) 8) :
    ∃ fuel t, Advances boundary fuel u t ∧ ReadyToStep t ∧ t.RIP = 0x11002f ∧
      AgreesExcept registers u t ∧
      (Operand.reg 7 : Operand 64).read t =
        (((value (memLoad u.external (stackPtr u+152) 64)
          (memLoad u.external (stackPtr u+160) 64)
          (memLoad u.external (stackPtr u+168) 64)
          (memLoad u.external (stackPtr u+176) 64)).setWidth 8) &&& 1).setWidth 64 := by
  let a0 := memLoad u.external (stackPtr u+152) 64
  let a1 := memLoad u.external (stackPtr u+160) 64
  let a2 := memLoad u.external (stackPtr u+168) 64
  let a3 := memLoad u.external (stackPtr u+176) 64
  obtain ⟨n1,t1,run1,ready1,rip1,agree1,h1⟩ := initial hout ready loaded rip constant readable
  obtain ⟨n2,t2,run2,ready2,rip2,agree2,h2⟩ := first_block a0 hout ready1
    (by intro address byte hf; rw [memory_eq agree1]; exact loaded address byte hf) rip1 h1 (readable_of_agrees agree1 readable)
  simp only [memory_eq agree1, stack_eq agree1] at h2
  have agree02 : AgreesExcept registers u t2 := (agree1.trans agree2).mono (by simp)
  obtain ⟨n3,t3,run3,ready3,rip3,agree3,h3⟩ :=
    second_block (first a0 a1).1 (first a0 a1).2.1 (first a0 a1).2.2 hout ready2
      (by intro address byte hf; rw [memory_eq agree02]; exact loaded address byte hf) rip2 h2 (readable_of_agrees agree02 readable)
  simp only [memory_eq agree02, stack_eq agree02] at h3
  have agree03 : AgreesExcept registers u t3 := (agree02.trans agree3).mono (by simp)
  let q := second (first a0 a1).1 (first a0 a1).2.1 (first a0 a1).2.2 a2
  obtain ⟨n4,t4,run4,ready4,rip4,agree4,h4⟩ := last_block q.1 q.2 hout ready3
    (by intro address byte hf; rw [memory_eq agree03]; exact loaded address byte hf) rip3 h3 (readable_of_agrees agree03 readable)
  simp only [memory_eq agree03, stack_eq agree03] at h4
  refine ⟨n1+n2+n3+n4,t4,((run1.trans run2).trans run3).trans run4,ready4,rip4,
    (agree03.trans agree4).mono (by simp), ?_⟩
  exact h4


theorem correct [bindings : Bindings] {s u : RamState} {boundary : ReturnBoundary} {beta : Nat}
    (pre : CalleePre s boundary 0x10fc00 32 80 2592) (state : Frame s u)
    (rip : u.RIP = 0x10ff77) (input : MontgomeryAt u (stackPtr s-256) beta)
    (constant : u.regValue .r14 = 0xffffffff00000001) :
    ∃ fuel t, Advances boundary fuel u t ∧ ReadyToStep t ∧ Frame s t ∧
      t.RIP = 0x11002f ∧ t.regValue .rdi = BitVec.ofNat 64 (beta%2) ∧
      AgreesExcept registers u t := by
  have readable : ∀ i < 4, MemReadable u (stackPtr u + BitVec.ofNat 64 (152+8*i)) 8 := by
    intro i hi
    have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    all_goals rw [state.rsp]
    · have he : stackPtr s-408+BitVec.ofNat 64 (152+8*0) = stackPtr s-256 := by
        simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
        rfl
      rw [he]
      exact P256.Proofs.Program.readable_of_grow (P256.Proofs.Program.stack_sub_readable pre.stack (by decide) (by decide)) state.allocated
    · have he : stackPtr s-408+BitVec.ofNat 64 (152+8*1) = stackPtr s-248 := by
        simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
        rfl
      rw [he]
      exact P256.Proofs.Program.readable_of_grow (P256.Proofs.Program.stack_sub_readable pre.stack (by decide) (by decide)) state.allocated
    · have he : stackPtr s-408+BitVec.ofNat 64 (152+8*2) = stackPtr s-240 := by
        simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
        rfl
      rw [he]
      exact P256.Proofs.Program.readable_of_grow (P256.Proofs.Program.stack_sub_readable pre.stack (by decide) (by decide)) state.allocated
    · have he : stackPtr s-408+BitVec.ofNat 64 (152+8*3) = stackPtr s-232 := by
        simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
        rfl
      rw [he]
      exact P256.Proofs.Program.readable_of_grow (P256.Proofs.Program.stack_sub_readable pre.stack (by decide) (by decide)) state.allocated
  obtain ⟨fuel,t,run,ready,hrip,agree,value⟩ := machine pre.outerBoundary
    (readyToStep state.machine state.bindingsSupported) state.loaded rip constant readable
  refine ⟨fuel,t,run,ready,state.after_registers ready agree
    (by simp [registers,Component.Covers]) (by simp [registers]),hrip,?_,agree⟩
  change (Operand.reg 7 : Operand 64).read t = _
  rw [value, byte_one_parity]
  have hp := value_parity_of_montgomeryAt input
  have h0 : stackPtr u+152 = stackPtr s-256 := by
    rw [state.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have h1 : stackPtr u+160 = stackPtr s-256+8 := by
    rw [state.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have h2 : stackPtr u+168 = stackPtr s-256+16 := by
    rw [state.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have h3 : stackPtr u+176 = stackPtr s-256+24 := by
    rw [state.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  rw [h0,h1,h2,h3,hp]

end P256.Proofs.Sec1.Decompress.Select.Parity
