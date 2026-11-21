import P256.Proofs.Common.Instructions.ByteLogic.AndReg
import P256.Proofs.Common.Instructions.ByteLogic.Core
import P256.Proofs.Common.Field.Operations.Neg.Borrow.Or

set_option autoImplicit false

open P256.Proofs.Common.Field.FieldNeg.Instructions (orFlags orSpec or_operation)
open P256.Proofs.Common.Instructions.ByteLogic (decodeLegacy0Opcode20_run_of_register readGPR8_run writeGPR8_run)

namespace P256.Proofs.Keygen.Multiply.Inverse.SafeGcd.LinearCombination.OutputInstructions

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem and_dl_cl_form (s : RamState) (ip : BitVec 64) (hmode : In64BitMode s) :
    (X86.Instructions.AND_GPR8_GPR8_20 ip (legacyContext s.DS) 1 2).run s =
      (.ok (), writeOutputs s (.reg 2 : Operand 8)
        (andSpec (oracleBit s.oracle) ((Operand.reg 2 : Operand 8).read s)
          ((Operand.reg 1 : Operand 8).read s)) 1 ip) := by
  unfold X86.Instructions.AND_GPR8_GPR8_20
  simp only [Operand.read, writeOutputs, Operand.write]
  spec_run [Read_GPR8 => readGPR8_run _ _ _ (.inr (by simp only [legacyContext]; decide)) hmode,
    X86.Instructions.Operations.AND => and_operation _ 8 (by decide) _ _,
    Write_GPR8 => writeGPR8_run _ _ _ _ (.inr (by simp only [legacyContext]; decide)) (hmode.of_cs_lma_eq rfl rfl)]

theorem and_dl_cl_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hcode : BytesAt s s.RIP [0x20,202]) (hlow : s.RIP.toNat + 2 ≤ 2^32) :
    Machine.step s = some (.next (afterStep s 2 fun t =>
      writeOutputs t (.reg 2 : Operand 8)
        (andSpec (oracleBit t.oracle) ((Operand.reg 2 : Operand 8).read t)
          ((Operand.reg 1 : Operand 8).read t)) 1 (BitVec.add s.RIP 2#64))) := by
  obtain ⟨fop,fmod⟩ := memFetch_run_of_bytesAt_opcode_modrm s h hcode hlow 0 (by simp) (by decide)
  rw [show BitVec.add s.RIP 0#64 = s.RIP from BitVec.add_zero _] at fop fmod
  have hm (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf : DecoderFeatures (afterFetches (beforeFetch s) 3) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ h.features
  have hd := decodeLegacy0_run_of_opcode20 _ _ s.RIP (legacyContext s.DS) rfl fop (hm 2)
  rw [decodeLegacy0Opcode20_run_of_register _ _ s.RIP (legacyContext s.DS) _ rfl (hm 3) hf fmod] at hd
  erw [and_dl_cl_form _ (BitVec.add s.RIP 2#64) (hm 3)] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0x20 [202]
    (legacyOpcode_of_check _ ⟨by decide,by decide⟩) hcode hlow hd ((hm 3).of_cs_lma_eq rfl rfl)

def andLowEffect (p : BitVec 64) (s : RamState) : Effect :=
  let r := (Operand.reg 2 : Operand 8).read s &&& (Operand.reg 1 : Operand 8).read s
  { rip := p+2
    writes := [⟨(Operand.reg 2 : Operand 64),mergeGPR 8 r ((Operand.reg 2 : Operand 64).read s)⟩]
    flags := some (andFlags r) }

theorem and_dl_cl_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x20,202]) (andLowEffect p) := by
  rintro s h hcode rfl
  refine ⟨_, and_dl_cl_step s h hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeOutputs h 2 _ _ 1 _,
    ⟨afterStep_writeOutputs_rip h 2 _ _ 1 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ 1 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp [writeOutputs, Operand.read, Operand.write, andSpec, setFlags,
      afterFetches, beforeFetch, resetStepFields]
  · exact ⟨rfl,rfl,trivial,rfl,rfl,rfl⟩

@[x86_local] theorem andLowEffect_local (p : BitVec 64) : Effect.Local (andLowEffect p) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [andLowEffect, h.read_reg]
  · intro s
    simp [andLowEffect, Write.Full, Operand.Full]

attribute [x86_compose] andLowEffect

theorem decodeLegacy0Opcode08_run_of_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm,t)) :
    (Decode_Legacy_0_Opcode_08 ip ctx).run s =
      (X86.Instructions.OR_GPR8_GPR8_08 (BitVec.add ip 2#64) ctx
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  have hsel (a b c d e f : Bool) :
      Select_Legacy_0_Opcode_08 ctx true a b c d e f modrm = .ok 1 := by
    simp [Select_Legacy_0_Opcode_08, x86_runtime, X86.Runtime.CheckedSlice.read,
      bind, pure, Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]
  unfold Decode_Legacy_0_Opcode_08
  decode_modrm_form s t ip hfetch hmode hf hsel

theorem or_al_cl_form (s : RamState) (ip : BitVec 64) (hmode : In64BitMode s) :
    (X86.Instructions.OR_GPR8_GPR8_08 ip (legacyContext s.DS) 1 0).run s =
      (.ok (), writeOutputs s (.reg 0 : Operand 8)
        (orSpec (oracleBit s.oracle) ((Operand.reg 0 : Operand 8).read s)
          ((Operand.reg 1 : Operand 8).read s)) 1 ip) := by
  unfold X86.Instructions.OR_GPR8_GPR8_08
  simp only [Operand.read, writeOutputs, Operand.write]
  spec_run [Read_GPR8 => readGPR8_run _ _ _ (.inr (by simp only [legacyContext]; decide)) hmode,
    X86.Instructions.Operations.OR => or_operation _ 8 (by decide) _ _,
    Write_GPR8 => writeGPR8_run _ _ _ _ (.inr (by simp only [legacyContext]; decide)) (hmode.of_cs_lma_eq rfl rfl)]

theorem or_al_cl_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hcode : BytesAt s s.RIP [0x08,200]) (hlow : s.RIP.toNat + 2 ≤ 2^32) :
    Machine.step s = some (.next (afterStep s 2 fun t =>
      writeOutputs t (.reg 0 : Operand 8)
        (orSpec (oracleBit t.oracle) ((Operand.reg 0 : Operand 8).read t)
          ((Operand.reg 1 : Operand 8).read t)) 1 (BitVec.add s.RIP 2#64))) := by
  obtain ⟨fop,fmod⟩ := memFetch_run_of_bytesAt_opcode_modrm s h hcode hlow 0 (by simp) (by decide)
  rw [show BitVec.add s.RIP 0#64 = s.RIP from BitVec.add_zero _] at fop fmod
  have hm (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf : DecoderFeatures (afterFetches (beforeFetch s) 3) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ h.features
  have hd := decodeLegacy0_run_of_opcode08 _ _ s.RIP (legacyContext s.DS) rfl fop (hm 2)
  rw [decodeLegacy0Opcode08_run_of_register _ _ s.RIP (legacyContext s.DS) _ rfl (hm 3) hf fmod] at hd
  erw [or_al_cl_form _ (BitVec.add s.RIP 2#64) (hm 3)] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0x08 [200]
    (legacyOpcode_of_check _ ⟨by decide,by decide⟩) hcode hlow hd ((hm 3).of_cs_lma_eq rfl rfl)

def orLowEffect (p : BitVec 64) (s : RamState) : Effect :=
  let r := (Operand.reg 0 : Operand 8).read s ||| (Operand.reg 1 : Operand 8).read s
  { rip := p+2
    writes := [⟨(Operand.reg 0 : Operand 64),mergeGPR 8 r ((Operand.reg 0 : Operand 64).read s)⟩]
    flags := some (orFlags r) }

theorem or_al_cl_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x08,200]) (orLowEffect p) := by
  rintro s h hcode rfl
  refine ⟨_, or_al_cl_step s h hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeOutputs h 2 _ _ 1 _,
    ⟨afterStep_writeOutputs_rip h 2 _ _ 1 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ 1 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp [writeOutputs, Operand.read, Operand.write, orSpec, setFlags,
      afterFetches, beforeFetch, resetStepFields]
  · exact ⟨rfl,rfl,trivial,rfl,rfl,rfl⟩

@[x86_local] theorem orLowEffect_local (p : BitVec 64) : Effect.Local (orLowEffect p) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [orLowEffect, h.read_reg]
  · intro s
    simp [orLowEffect, Write.Full, Operand.Full]

attribute [x86_compose] orLowEffect

end P256.Proofs.Keygen.Multiply.Inverse.SafeGcd.LinearCombination.OutputInstructions
