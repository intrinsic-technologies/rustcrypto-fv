import Md5.Proofs.MemoryRoutines.Memset.Register.Movzx

namespace Md5.Proofs.Buffered.FinalizeReset.Prepare.Register

open X86 X86.Helpers X86Proofs X86.Machine X86.UserProcess
open Md5.Proofs.MemoryRoutines.Memset.Register

theorem movzx_r15d_al_form {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ)
    (ip : BitVec 64) (ds : Segment) (hmode : In64BitMode s) :
    (X86.Instructions.MOVZX_GPRv_GPR8 ip (rexContext ds 0x44) 7 0).run s =
      (.ok (), writeResult s (.reg 15 : Operand 32)
        (((Operand.reg 0 : Operand 8).read s).setWidth 32) ip) := by
  unfold X86.Instructions.MOVZX_GPRv_GPR8
  simp only [writeResult, Operand.write_reg32]
  repeat spec_bind_rfl
  spec_bind_with readGPR8_run_of_rex _ _ hmode
  repeat spec_bind_rfl
  erw [writeGPR32_run {s with Next_IP := ip} _ _ (hmode.of_cs_lma_eq rfl rfl)]
  simp only [BitVec.ofNat_toNat]
  rfl

theorem movzx_r15d_al_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hcode : BytesAt s s.RIP [0x44, 0x0F, 0xB6, 0xF8])
    (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    X86.Machine.step s = some (.next (afterStep s 4 fun t ↦
      writeResult t (.reg 15 : Operand 32)
        (((Operand.reg 0 : Operand 8).read t).setWidth 32) (BitVec.add s.RIP 4#64))) := by
  have hdecode := decodeLegacy1_run_of_rex_B6_register s h 0x44 0xF8 (by decide) hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 5) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  change _ = some ((X86.Instructions.MOVZX_GPRv_GPR8 _ (rexContext s.DS 0x44) 7 0).run _)
    at hdecode
  rw [movzx_r15d_al_form _ _ _ hmode] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy1 s _ h 0x44 0xB6 [0xF8]
    (by unfold RexPrefix; decide) ⟨by decide, by decide⟩ hcode hlow hdecode
    (hmode.of_cs_lma_eq rfl rfl)

def movzxR15dAlEffect (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p + 4
    writes := [⟨(Operand.reg 15 : Operand 64),
      ((Operand.reg 0 : Operand 8).read s).setWidth 64⟩] }

theorem movzxR15dAlEffect_components (p : BitVec 64) (s : RamState) :
    (movzxR15dAlEffect p s).components = [.reg 15, .rip] := rfl

theorem movzxR15dAlEffect_avoids (p : BitVec 64) (s : RamState) (code : CodeMap) :
    (movzxR15dAlEffect p s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [movzxR15dAlEffect_components, Component.Covers]) code

theorem movzx_r15d_al_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p [0x44, 0x0F, 0xB6, 0xF8])
      (movzxR15dAlEffect p) := by
  rintro s h hcode rfl
  refine ⟨_, movzx_r15d_al_step s h hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeResult h 4 _ _ _,
    ⟨afterStep_writeResult_rip h 4 _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s 4 _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self32, Operand.read_afterFetches,
    Operand.read_beforeFetch]
  exact BitVec.setWidth_setWidth (by decide)

attribute [x86_compose] movzxR15dAlEffect

@[x86_local] theorem movzxR15dAlEffect_local (p : BitVec 64) :
    Effect.Local (movzxR15dAlEffect p) := by
  refine ⟨fun _ _ _ ↦ rfl, fun t t' h ↦ ?_, fun _ _ _ ↦ rfl,
    fun t t' h i hi ↦ ?_, fun _ ↦ ?_⟩
  · simp [movzxR15dAlEffect, h.read_reg]
  · simpa only [movzxR15dAlEffect, Effect.flag] using congrArg some hi
  · simp [movzxR15dAlEffect, Write.Full, Operand.Full]

end Md5.Proofs.Buffered.FinalizeReset.Prepare.Register
