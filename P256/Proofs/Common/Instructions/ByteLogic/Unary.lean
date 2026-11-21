import X86Proofs.Step.AfterStep
import P256.Proofs.Common.Instructions.ByteLogic.Core
import X86Proofs.Instructions.Not.Operation
import X86Proofs.Instructions.Inc.Operation

set_option autoImplicit false

namespace P256.Proofs.Common.Instructions.ByteLogic

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs
open scoped X86.Runtime.Syntax

theorem not_r8_form (s : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (rm : BitVec 3) (hmode : In64BitMode s) (hlock : ctx.lock_prefix_present = false)
    (haccess : (ctx.rex_prefix_present ||| ctx.rex2_prefix_present ||| ctx.vex_prefix_present |||
      ctx.evex_prefix_present) = true ∨ (gprNumber ctx.rex_b4 ctx.rex_b3 rm).toNat < 4) :
    (X86.Instructions.NOT_GPR8 ip ctx rm).run s =
      let dst : Operand 8 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeResult s dst (notSpec (dst.read s)) ip) := by
  have hctx : {ctx with lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hctx]
  unfold X86.Instructions.NOT_GPR8
  simp only [Operand.read, writeResult, Operand.write]
  spec_run [Read_GPR8 => readGPR8_run _ _ _ haccess hmode,
    liftM => not_operation _ 8 (by decide) _,
    Write_GPR8 => writeGPR8_run _ _ _ _ haccess (hmode.of_cs_lma_eq rfl rfl)]

theorem inc_r8_form (s : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (rm : BitVec 3) (hmode : In64BitMode s) (hlock : ctx.lock_prefix_present = false)
    (haccess : (ctx.rex_prefix_present ||| ctx.rex2_prefix_present ||| ctx.vex_prefix_present |||
      ctx.evex_prefix_present) = true ∨ (gprNumber ctx.rex_b4 ctx.rex_b3 rm).toNat < 4) :
    (X86.Instructions.INC_GPR8 ip ctx rm).run s =
      let dst : Operand 8 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeOutputs s dst (incSpec (StatusFlags.ofRFLAGS s.RFLAGS) (dst.read s)) 0 ip) := by
  have hctx : {ctx with lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hctx]
  unfold X86.Instructions.INC_GPR8
  simp only [Operand.read, writeOutputs, Operand.write, oracleSkip_zero]
  spec_run [Read_GPR8 => readGPR8_run _ _ _ haccess hmode,
    X86.Instructions.Operations.INC => inc_operation _ 8 (by decide) _,
    Write_GPR8 => writeGPR8_run _ _ _ _ haccess (hmode.of_cs_lma_eq rfl rfl)]

theorem decodeLegacy0_run_of_opcodeFE [Bindings]
    (s u : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xfe, u)) (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip ctx).run s = some ((Decode_Legacy_0_Opcode_FE ip ctx).run u) := by
  unfold Decode_Legacy_0
  rw [ite_eq_right (fun h => Bool.false_ne_true (hrex2.symm.trans h))]
  rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
  repeat erw [decodeLegacy0_modeGuard_run _ _ hmode]
  rfl

theorem decodeLegacy0OpcodeF6_run_of_not [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok 0xd0, t)) :
    (Decode_Legacy_0_Opcode_F6 ip ctx).run s =
      (X86.Instructions.NOT_GPR8 (BitVec.add ip 2#64) ctx 0).run t := by
  have hsel (a b c d e f : Bool) :
      Select_Legacy_0_Opcode_F6 ctx true a b c d e f 0xd0 = .ok 12 := by rfl
  unfold Decode_Legacy_0_Opcode_F6
  decode_modrm_form s t ip hfetch hmode hf hsel

def notAlState (s : RamState) : RamState :=
  afterStep s 2 fun t => writeResult t (.reg 0 : Operand 8) (notSpec ((Operand.reg 0 : Operand 8).read t)) (BitVec.add s.RIP 2#64)

theorem not_al_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hcode : BytesAt s s.RIP [0xF6, 0xd0]) (hlow : s.RIP.toNat + 2 ≤ 2^32) :
    Machine.step s = some (.next (notAlState s)) := by
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [0xF6, 0xd0] := hcode
  have f1 : (Mem_Fetch s.RIP 8).run (afterFetches (beforeFetch s) 1) =
      (.ok 0xF6, afterFetches (beforeFetch s) 2) := by
    have hf := memFetch_run_of_bytesAt (beforeFetch s) 1 h.fetchReady hc hlow 0 (by simp) (by decide)
    rwa [show BitVec.add (beforeFetch s).RIP (BitVec.ofNat 64 0) = (beforeFetch s).RIP
      from BitVec.add_zero _] at hf
  have f2 : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok 0xd0, afterFetches (beforeFetch s) 3) :=
    memFetch_run_of_bytesAt (beforeFetch s) 2 h.fetchReady hc hlow 1 (by simp) (by decide)
  have hm (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf : DecoderFeatures (afterFetches (beforeFetch s) 3) :=
    DecoderFeatures.of_sameControls (s := s)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ h.features
  have hd := decodeLegacy0_run_of_opcodeF6 _ _ _ (legacyContext s.DS) rfl f1 (hm 2)
  rw [decodeLegacy0OpcodeF6_run_of_not _ _ _ _ (hm 3) hf f2,
    not_r8_form _ _ _ _ (hm 3) rfl (.inr (by change (0 : Nat) < 4; decide +kernel))] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0xF6 [0xd0]
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hd ((hm 3).of_cs_lma_eq rfl rfl)

theorem decodeLegacy0OpcodeFE_run_of_inc [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok 0xc1, t)) :
    (Decode_Legacy_0_Opcode_FE ip ctx).run s =
      (X86.Instructions.INC_GPR8 (BitVec.add ip 2#64) ctx 1).run t := by
  have hsel (a b c d e f : Bool) :
      Select_Legacy_0_Opcode_FE ctx true a b c d e f 0xc1 = .ok 4 := by rfl
  unfold Decode_Legacy_0_Opcode_FE
  decode_modrm_form s t ip hfetch hmode hf hsel

def incClState (s : RamState) : RamState :=
  afterStep s 2 fun t => writeOutputs t (.reg 1 : Operand 8)
    (incSpec (StatusFlags.ofRFLAGS t.RFLAGS) ((Operand.reg 1 : Operand 8).read t)) 0 (BitVec.add s.RIP 2#64)

theorem inc_cl_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hcode : BytesAt s s.RIP [0xFE, 0xc1]) (hlow : s.RIP.toNat + 2 ≤ 2^32) :
    Machine.step s = some (.next (incClState s)) := by
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [0xFE, 0xc1] := hcode
  have f1 : (Mem_Fetch s.RIP 8).run (afterFetches (beforeFetch s) 1) =
      (.ok 0xFE, afterFetches (beforeFetch s) 2) := by
    have hf := memFetch_run_of_bytesAt (beforeFetch s) 1 h.fetchReady hc hlow 0 (by simp) (by decide)
    rwa [show BitVec.add (beforeFetch s).RIP (BitVec.ofNat 64 0) = (beforeFetch s).RIP
      from BitVec.add_zero _] at hf
  have f2 : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok 0xc1, afterFetches (beforeFetch s) 3) :=
    memFetch_run_of_bytesAt (beforeFetch s) 2 h.fetchReady hc hlow 1 (by simp) (by decide)
  have hm (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf : DecoderFeatures (afterFetches (beforeFetch s) 3) :=
    DecoderFeatures.of_sameControls (s := s)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ h.features
  have hd := decodeLegacy0_run_of_opcodeFE _ _ _ (legacyContext s.DS) rfl f1 (hm 2)
  rw [decodeLegacy0OpcodeFE_run_of_inc _ _ _ _ (hm 3) hf f2,
    inc_r8_form _ _ _ _ (hm 3) rfl (.inr (by change (1 : Nat) < 4; decide +kernel))] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0xFE [0xc1]
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hd ((hm 3).of_cs_lma_eq rfl rfl)

def notAlEffect (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p + 2
    writes := [⟨(Operand.reg 0 : Operand 64),
      mergeGPR 8 (~~~((Operand.reg 0 : Operand 8).read s))
        ((Operand.reg 0 : Operand 64).read s)⟩] }

def incClEffect (p : BitVec 64) (s : RamState) : Effect :=
  let out := incSpec (StatusFlags.ofRFLAGS s.RFLAGS) ((Operand.reg 1 : Operand 8).read s)
  { rip := p + 2
    writes := [⟨(Operand.reg 1 : Operand 64),
      mergeGPR 8 out.1 ((Operand.reg 1 : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags out.2) }

theorem not_al_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xf6, 0xd0]) (notAlEffect p) := by
  rintro s h hcode rfl
  refine ⟨_, not_al_step s h hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeResult h 2 0 _ _, ?_⟩
  refine ⟨afterStep_writeResult_rip h 2 _ _ _, ?_, trivial,
    AgreesExcept.afterStep_writeResult s 2 0 _ _⟩
  change (Operand.reg 0 : Operand 64).read (notAlState s) = _
  rw [notAlState, Operand.read_afterStep]
  simp [writeResult, Operand.read, Operand.write, notSpec, afterFetches,
    beforeFetch, resetStepFields]

theorem inc_cl_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xfe, 0xc1]) (incClEffect p) := by
  rintro s h hcode rfl
  refine ⟨_, inc_cl_step s h hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeOutputs h 2 1 _ 0 _, ?_⟩
  refine ⟨afterStep_writeOutputs_rip h 2 _ _ 0 _, ?_,
    StatusFlagsOutcome.allows_store ?_ _, AgreesExcept.afterStep_writeOutputs s 2 1 _ 0 _⟩
  · change (Operand.reg 1 : Operand 64).read (incClState s) = _
    rw [incClState, Operand.read_afterStep]
    simp [writeOutputs, Operand.read, Operand.write, setFlags, incSpec, afterFetches,
      beforeFetch, resetStepFields]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

end P256.Proofs.Common.Instructions.ByteLogic
