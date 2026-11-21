import P256.Proofs.Common.Instructions.ByteOps.Effects
import X86Proofs.Instructions.Xor.Operation
import X86Proofs.Instructions.Xor.Generated.RR.Triple

set_option autoImplicit false

open P256.Proofs.Common.Instructions.ByteOps.ByteOps (al_write_run)

namespace P256.Proofs.PublicPoint.Normalize.Finish

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem decodeLegacy0_run_of_opcode34 [Bindings]
    (s u : RamState) (ip : BitVec 64) (context : Instruction_Context)
    (hrex2 : context.rex2_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x34, u)) (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s =
      some ((Decode_Legacy_0_Opcode_34 ip context).run u) := by
  unfold Decode_Legacy_0
  rw [ite_eq_right (fun h => Bool.false_ne_true (hrex2.symm.trans h))]
  rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
  repeat erw [decodeLegacy0_modeGuard_run _ _ hmode]
  rfl

theorem decodeLegacy0Opcode34_run_of_acc [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_34 ip context).run s =
      (X86.Instructions.XOR_AL_IMMb (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_34
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_34 context mode a b c d e f z) _ 1 hmode hf
    (fun _ _ _ _ _ _ => rfl)).trans ?_
  simp only [Int.reduceBEq, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

theorem xor_al_imm8_form [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (imm : BitVec 8)
    (hlock : ctx.lock_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok imm, t)) :
    (X86.Instructions.XOR_AL_IMMb ip ctx).run s =
      (.ok (), writeOutputs t (.reg 0 : Operand 8)
        (xorSpec (oracleBit t.oracle) ((Operand.reg 0 : Operand 8).read s) (imm.signExtend 8))
        1 (BitVec.add ip 1#64)) := by
  have hcontext : {ctx with lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.XOR_AL_IMMb
  simp only [Operand.read, writeOutputs, Operand.write]
  spec_run [AL => al_run _, Mem_Fetch => hfetch,
    X86.Instructions.Operations.XOR => xor_operation _ 8 (by decide) _ _,
    AL_write => al_write_run _ _]

def xorAlImm8State (s : RamState) (imm : BitVec 8) : RamState :=
  afterStep s 2 fun t => writeOutputs t (.reg 0 : Operand 8)
    (xorSpec (oracleBit t.oracle) ((Operand.reg 0 : Operand 8).read t) imm) 1 (BitVec.add s.RIP 2#64)

theorem xor_al_imm8_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (imm : UInt8) (hcode : BytesAt s s.RIP [0x34, imm])
    (hlow : s.RIP.toNat + 2 ≤ 2^32) :
    Machine.step s = some (.next (xorAlImm8State s imm.toBitVec)) := by
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [0x34, imm] := hcode
  have hlow' : s.RIP.toNat + [0x34, imm].length ≤ 2^32 := hlow
  have fop : (Mem_Fetch s.RIP 8).run (afterFetches (beforeFetch s) 1) =
      (.ok 0x34, afterFetches (beforeFetch s) 2) := by
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
  have hd := decodeLegacy0_run_of_opcode34 _ _ s.RIP (legacyContext s.DS) rfl fop (hmode 2)
  rw [decodeLegacy0Opcode34_run_of_acc _ _ _ (hmode 2) hfeatures,
    xor_al_imm8_form _ _ _ _ _ rfl fimm,
    show BitVec.add (BitVec.add s.RIP 1#64) 1#64 = BitVec.add s.RIP 2#64 from
      BitVec.add_assoc _ _ _, BitVec.signExtend_eq] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0x34 [imm]
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow' hd
    ((hmode 3).of_cs_lma_eq rfl rfl)

def xorAlImm8Effect (p : BitVec 64) (imm : BitVec 8) (s : RamState) : Effect :=
  let r := (Operand.reg 0 : Operand 8).read s ^^^ imm
  { rip := p + 2
    writes := [⟨(Operand.reg 0 : Operand 64),
      mergeGPR 8 r ((Operand.reg 0 : Operand 64).read s)⟩]
    flags := some (xorFlags r) }

theorem xor_al_imm8_effect_step [Bindings] (p : BitVec 64) (imm : UInt8) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x34, imm])
      (xorAlImm8Effect p imm.toBitVec) := by
  rintro s h hcode rfl
  refine ⟨_, xor_al_imm8_step s h imm hcode.bytesAt
      (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeOutputs h 2 0 _ 1 _, ?_⟩
  refine ⟨afterStep_writeOutputs_rip h 2 _ _ 1 _, ?_,
    StatusFlagsOutcome.allows_store ?_ _, AgreesExcept.afterStep_writeOutputs s 2 0 _ 1 _⟩
  · change (Operand.reg 0 : Operand 64).read (xorAlImm8State s imm.toBitVec) = _
    rw [xorAlImm8State, Operand.read_afterStep]
    simp [writeOutputs, setFlags, Operand.read, Operand.write, xorSpec,
      afterFetches, beforeFetch, resetStepFields]
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

end P256.Proofs.PublicPoint.Normalize.Finish
