import X86Proofs.Step.Decode.Legacy1OpcodeB6
import X86Proofs.Instructions.Movzx.Generated.RM8.Decode
import P256.Proofs.Common.EffectCompose
import X86Proofs.Program.ReadWrite.WriteResult
import X86Proofs.Program.Effect

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi.Negative.Instructions

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem decodeLegacy1_run_of_opcodeBE [Bindings] (s u : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (hmode : In64BitMode u) (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xbe, u)) :
    (Decode_Legacy_1 ip ctx).run s = some ((Decode_Legacy_1_Opcode_BE ip ctx).run u) := by
  unfold Decode_Legacy_1
  rw [ite_eq_right (fun h => Bool.false_ne_true (hrex2.symm.trans h))]
  rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
  repeat erw [decodeLegacy0_modeGuard_run _ _ hmode]
  repeat erw [decodeLegacy1_modeGuard_run _ _ _ _ hmode]
  rfl

theorem selectLegacy1OpcodeBE_run_of_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_BE context true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_1_Opcode_BE, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

theorem decodeLegacy1OpcodeBE_run_of_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_BE ip context).run s =
      (X86.Instructions.MOVSX_GPRv_GPR8 (BitVec.add ip 2#64) context
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_BE
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy1OpcodeBE_run_of_register context a b c d e f modrm hmod)

theorem movsx_r64_r8_form [Bindings] (s : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (reg rm : BitVec 3)
    (hmode : In64BitMode s) (hsize : ctx.operand_size = 64)
    (hlock : ctx.lock_prefix_present = false) (hrex : ctx.rex_prefix_present = true) :
    (X86.Instructions.MOVSX_GPRv_GPR8 ip ctx reg rm).run s =
      let dst : Operand 64 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let src : Operand 64 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeResult s dst (((src.read s).setWidth 8).signExtend 64) ip) := by
  have hcontext :
      {ctx with operand_size := 64, lock_prefix_present := false, rex_prefix_present := true} =
        ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.MOVSX_GPRv_GPR8
  simp only [writeResult, Operand.read_reg64, Operand.write_reg64]
  spec_run [
    Read_GPR8 => readGPR8_run_of_rex _ _ hmode,
    X86.Instructions.Operations.MOVSX => movsx_operation _ _,
    Write_GPR => by
      rw [writeGPR64_run {s with Next_IP := ip} _ _ (hmode.of_cs_lma_eq rfl rfl)]
      simp only [gprNumber, Int.reduceToNat, Int.reduceAdd, BitVec.signExtend]]

theorem movsx_rdi_al_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hcode : BytesAt s s.RIP [0x48, 0x0f, 0xbe, 0xf8])
    (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    X86.Machine.step s = some (.next (afterStep s 4 fun t =>
      writeResult t (.reg 7 : Operand 64)
        ((((Operand.reg 0 : Operand 64).read t).setWidth 8).signExtend 64)
        (BitVec.add s.RIP 4#64))) := by
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [0x48, 0x0f, 0xbe, 0xf8] := hcode
  have f1 := memFetch_run_of_bytesAt (beforeFetch s) 3 h.fetchReady hc hlow 2
    (by simp) (by decide)
  have f2 : (Mem_Fetch (BitVec.add (BitVec.add s.RIP 2#64) 1#64) 8).run
      (afterFetches (beforeFetch s) 4) =
        (.ok 0xf8, afterFetches (beforeFetch s) 5) := by
    rw [show BitVec.add (BitVec.add s.RIP 2#64) 1#64 = BitVec.add s.RIP 3#64
      from BitVec.add_assoc s.RIP 2#64 1#64]
    exact memFetch_run_of_bytesAt (beforeFetch s) 4 h.fetchReady hc hlow 3
      (by simp) (by decide)
  have hmode (j : Nat) : In64BitMode (afterFetches (beforeFetch s) j) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf : DecoderFeatures (afterFetches (beforeFetch s) 5) :=
    h.features.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hd := decodeLegacy1_run_of_opcodeBE _ _ (BitVec.add s.RIP 2#64)
    (rexContext s.DS 0x48) rfl (hmode 4) f1
  rw [decodeLegacy1OpcodeBE_run_of_register _ _ _ _ _ rfl (hmode 5) hf f2,
    movsx_r64_r8_form _ _ _ _ _ (hmode 5) rfl rfl rfl,
    show BitVec.add (BitVec.add s.RIP 2#64) 2#64 = BitVec.add s.RIP 4#64
      from BitVec.add_assoc s.RIP 2#64 2#64] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy1 s _ h 0x48 0xbe [0xf8] (by simp [RexPrefix])
    (by decide) hcode hlow hd ((hmode 5).of_cs_lma_eq rfl rfl)

def movsxRdiAlEffect (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p + 4
    writes := [⟨(Operand.reg 7 : Operand 64),
      ((Operand.reg 0 : Operand 64).read s).setWidth 8 |>.signExtend 64⟩] }

theorem movsx_rdi_al_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x48, 0x0f, 0xbe, 0xf8])
      (movsxRdiAlEffect p) := by
  rintro s h hcode rfl
  refine ⟨_, movsx_rdi_al_step s h hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeResult h 4 _ _ _,
    ⟨afterStep_writeResult_rip h 4 _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s 4 _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self, Operand.read_afterFetches, Operand.read_beforeFetch]

attribute [x86_compose] movsxRdiAlEffect

end P256.Proofs.Verifying.Combination.Loop.Multi.Negative.Instructions
