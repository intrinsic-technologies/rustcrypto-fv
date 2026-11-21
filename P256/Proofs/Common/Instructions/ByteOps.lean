import X86Proofs.Step.AfterStep
import X86Proofs.Step.LegacyStep
import X86Proofs.Step.Decode.Legacy0
import X86Proofs.Instructions.And.Operation
import X86Proofs.Instructions.Cmp.Operation

set_option autoImplicit false

namespace P256.Proofs.Common.Instructions.ByteOps.ByteOps

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem decodeLegacy0_run_of_opcode24 [Bindings]
    (s u : RamState) (ip : BitVec 64) (context : Instruction_Context)
    (hrex2 : context.rex2_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x24, u)) (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s =
      some ((Decode_Legacy_0_Opcode_24 ip context).run u) := by
  unfold Decode_Legacy_0
  rw [ite_eq_right (fun h => Bool.false_ne_true (hrex2.symm.trans h))]
  rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
  repeat erw [decodeLegacy0_modeGuard_run _ _ hmode]
  rfl

theorem decodeLegacy0Opcode24_run_of_acc [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_24 ip context).run s =
      (X86.Instructions.AND_AL_IMMb (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_24
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_24 context mode a b c d e f z) _ 1 hmode hf
    (fun _ _ _ _ _ _ => rfl)).trans ?_
  simp only [Int.reduceBEq, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

theorem decodeLegacy0_run_of_opcode3C [Bindings]
    (s u : RamState) (ip : BitVec 64) (context : Instruction_Context)
    (hrex2 : context.rex2_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x3C, u)) (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s =
      some ((Decode_Legacy_0_Opcode_3C ip context).run u) := by
  unfold Decode_Legacy_0
  rw [ite_eq_right (fun h => Bool.false_ne_true (hrex2.symm.trans h))]
  rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
  repeat erw [decodeLegacy0_modeGuard_run _ _ hmode]
  rfl

theorem decodeLegacy0Opcode3C_run_of_acc [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_3C ip context).run s =
      (X86.Instructions.CMP_AL_IMMb (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_3C
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_3C context mode a b c d e f z) _ 1 hmode hf
    (fun _ _ _ _ _ _ => rfl)).trans ?_
  simp only [Int.reduceBEq, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

theorem al_write_run {σ : Type} (s : X86.State σ) (v : BitVec 8) :
    (AL_write v).run s =
      (.ok (), {s with GPR := Vector.set s.GPR (gprIndex 0) (mergeGPR 8 v s.GPR[gprIndex 0])}) := by
  simp only [AL_write, x86_runtime, ExceptT.run, bind, ExceptT.bind, ExceptT.mk,
    GPR.get, getThe, MonadStateOf.get, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, Functor.map, pure, ExceptT.pure, GPR.set,
    modify, modifyGet, MonadStateOf.modifyGet]
  rfl

theorem and_al_imm8_form [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (imm : BitVec 8)
    (hlock : ctx.lock_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok imm, t)) :
    (X86.Instructions.AND_AL_IMMb ip ctx).run s =
      (.ok (), writeOutputs t (.reg 0 : Operand 8)
        (andSpec (oracleBit t.oracle) ((Operand.reg 0 : Operand 8).read s) (imm.signExtend 8))
        1 (BitVec.add ip 1#64)) := by
  have hcontext : {ctx with lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.AND_AL_IMMb
  simp only [Operand.read, writeOutputs, Operand.write]
  spec_run [AL => al_run _, Mem_Fetch => hfetch,
    X86.Instructions.Operations.AND => and_operation _ 8 (by decide) _ _,
    AL_write => al_write_run _ _]

theorem cmp_al_imm8_form [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (imm : BitVec 8)
    (hlock : ctx.lock_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok imm, t)) :
    (X86.Instructions.CMP_AL_IMMb ip ctx).run s =
      (.ok (), writeFlagsOutputs t
        (cmpSpec ((Operand.reg 0 : Operand 8).read s) (imm.signExtend 8))
        0 (BitVec.add ip 1#64)) := by
  have hcontext : {ctx with lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.CMP_AL_IMMb
  simp only [Operand.read, writeFlagsOutputs, oracleSkip_zero]
  spec_run [AL => al_run _, Mem_Fetch => hfetch,
    X86.Instructions.Operations.CMP => cmp_operation _ 8 (by decide) _ _]

def andAlImm8State (s : RamState) (imm : BitVec 8) : RamState :=
  afterStep s 2 fun t => writeOutputs t (.reg 0 : Operand 8)
    (andSpec (oracleBit t.oracle) ((Operand.reg 0 : Operand 8).read t) imm) 1 (BitVec.add s.RIP 2#64)

def cmpAlImm8State (s : RamState) (imm : BitVec 8) : RamState :=
  afterStep s 2 fun t => writeFlagsOutputs t
    (cmpSpec ((Operand.reg 0 : Operand 8).read t) imm) 0 (BitVec.add s.RIP 2#64)

theorem and_al_imm8_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (imm : UInt8) (hcode : BytesAt s s.RIP [0x24, imm])
    (hlow : s.RIP.toNat + 2 ≤ 2^32) :
    Machine.step s = some (.next (andAlImm8State s imm.toBitVec)) := by
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [0x24, imm] := hcode
  have hlow' : s.RIP.toNat + [0x24, imm].length ≤ 2^32 := hlow
  have fop : (Mem_Fetch s.RIP 8).run (afterFetches (beforeFetch s) 1) =
      (.ok 0x24, afterFetches (beforeFetch s) 2) := by
    have hf := memFetch_run_of_bytesAt (beforeFetch s) 1 h.fetchReady hc hlow' 0
      (by simp) (by decide)
    rwa [show BitVec.add (beforeFetch s).RIP (BitVec.ofNat 64 0) = (beforeFetch s).RIP
      from BitVec.add_zero _] at hf
  have fimm : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run
      (afterFetches (beforeFetch s) 2) =
      (.ok imm.toBitVec, afterFetches (beforeFetch s) 3) :=
    memFetch_run_of_bytesAt (beforeFetch s) 2 h.fetchReady hc hlow' 1
      (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 2) :=
    DecoderFeatures.of_sameControls (s := s)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ h.features
  have hd := decodeLegacy0_run_of_opcode24 _ _ s.RIP (legacyContext s.DS) rfl fop (hmode 2)
  rw [decodeLegacy0Opcode24_run_of_acc _ _ _ (hmode 2) hfeatures,
    and_al_imm8_form _ _ _ _ _ rfl fimm,
    show BitVec.add (BitVec.add s.RIP 1#64) 1#64 = BitVec.add s.RIP 2#64 from
      BitVec.add_assoc _ _ _, BitVec.signExtend_eq] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0x24 [imm]
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow' hd
    ((hmode 3).of_cs_lma_eq rfl rfl)

theorem cmp_al_imm8_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (imm : UInt8) (hcode : BytesAt s s.RIP [0x3c, imm])
    (hlow : s.RIP.toNat + 2 ≤ 2^32) :
    Machine.step s = some (.next (cmpAlImm8State s imm.toBitVec)) := by
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [0x3C, imm] := hcode
  have hlow' : s.RIP.toNat + [0x3C, imm].length ≤ 2^32 := hlow
  have fop : (Mem_Fetch s.RIP 8).run (afterFetches (beforeFetch s) 1) =
      (.ok 0x3C, afterFetches (beforeFetch s) 2) := by
    have hf := memFetch_run_of_bytesAt (beforeFetch s) 1 h.fetchReady hc hlow' 0
      (by simp) (by decide)
    rwa [show BitVec.add (beforeFetch s).RIP (BitVec.ofNat 64 0) = (beforeFetch s).RIP
      from BitVec.add_zero _] at hf
  have fimm : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run
      (afterFetches (beforeFetch s) 2) =
      (.ok imm.toBitVec, afterFetches (beforeFetch s) 3) :=
    memFetch_run_of_bytesAt (beforeFetch s) 2 h.fetchReady hc hlow' 1
      (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 2) :=
    DecoderFeatures.of_sameControls (s := s)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ h.features
  have hd := decodeLegacy0_run_of_opcode3C _ _ s.RIP (legacyContext s.DS) rfl fop (hmode 2)
  rw [decodeLegacy0Opcode3C_run_of_acc _ _ _ (hmode 2) hfeatures,
    cmp_al_imm8_form _ _ _ _ _ rfl fimm,
    show BitVec.add (BitVec.add s.RIP 1#64) 1#64 = BitVec.add s.RIP 2#64 from
      BitVec.add_assoc _ _ _, BitVec.signExtend_eq] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0x3C [imm]
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow' hd
    ((hmode 3).of_cs_lma_eq rfl rfl)

theorem and_al_imm8_ready [Bindings] {s : RamState} (h : ReadyToStep s) (imm : BitVec 8) :
    ReadyToStep (andAlImm8State s imm) :=
  ReadyToStep.afterStep_writeOutputs h 2 0 _ 1 _

theorem cmp_al_imm8_ready [Bindings] {s : RamState} (h : ReadyToStep s) (imm : BitVec 8) :
    ReadyToStep (cmpAlImm8State s imm) :=
  ReadyToStep.afterStep_writeFlagsOutputs h 2 _ 0 _

theorem and_fe_eq_two_iff : ∀ b : BitVec 8, b &&& 0xfe = 2 ↔ b = 2 ∨ b = 3 := by
  decide +kernel

end P256.Proofs.Common.Instructions.ByteOps.ByteOps
