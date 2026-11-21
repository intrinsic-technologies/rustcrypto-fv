import P256.Proofs.Common.Instructions.Sar.Core
import P256.Proofs.Common.Instructions.Sar.Spec
import P256.Proofs.Common.Instructions.ByteLogic.Core
import X86Proofs.Step.LegacyStep
import X86Proofs.Instructions.Shr.Operation
import P256.Proofs.Common.EffectCompose
import P256.Proofs.Common.Instructions.ByteLogic.AndReg

open P256.Proofs.Common.Instructions (sarFlags sarFlags_allows sarOracleAF sarOracleBits sarSpec sar_fold shiftRightArithmetic_one)
open P256.Proofs.Common.Instructions.ByteLogic (readGPR8_run writeGPR8_run)

namespace P256.Proofs.Keygen.Multiply.ProjectiveLookup.Instructions

open X86 X86.Helpers X86Proofs X86.Machine X86.UserProcess

open scoped X86.Runtime.Syntax

theorem sar_byte_operation {σ : Type} (s : X86.State σ) (x : BitVec 8) (count : BitVec 8)
    (hcount : shiftCount 8 count ≤ 8) :
    (X86.Instructions.Operations.SAR 8 x count).run s =
      let c := shiftCount 8 count
      let (r, flags) := sarSpec (StatusFlags.ofRFLAGS s.RFLAGS) (oracleBit s.oracle)
        (sarOracleAF s.oracle c) c x
      (.ok r, setFlags { s with oracle := oracleSkip s.oracle (sarOracleBits c) } flags) := by
  have hlt := shiftCount_lt_64 8 count
  obtain ⟨c, hc⟩ : ∃ c, shiftCount 8 count = c := ⟨_, rfl⟩
  have hc32 : count.toNat % 32 = c := by simpa [shiftCount] using hc
  rw [hc] at hlt hcount ⊢
  simp only [sarSpec, sarOracleBits, sarOracleAF]
  unfold X86.Instructions.Operations.SAR
  simp only [isParityEven8_run]
  repeat spec_bind_rfl
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte, Int.reduceToNat,
    unsigned_extractLsb', Nat.reducePow]
  rw [hc32]
  by_cases h0 : c = 0
  · subst h0
    simp
  have e0 : ((c : Int) != 0) = true := by
    simpa only [bne_iff_ne, ne_eq, Int.ofNat_eq_zero] using h0
  simp only [e0, h0, ↓reduceIte]
  spec_bind_rfl

  refine (specM_bind_run _ _ (specM_forIn_run _ _
    (fun _ (acc : BitVec _ × BitVec 1) => (acc.1.sshiftRight 1, acc.1.extractLsb' 0 1)) _ _ ?_)).trans ?_
  · intro _ _ _
    simp only [shiftRightArithmetic_one (by decide : 1 < 8)]
    rfl
  rw [sar_fold _ _ _ (by omega) (by omega)]
  generalize x.sshiftRight c = r
  by_cases h1 : c = 1
  · subst h1
    simp only [↓reduceIte]
    rw [setFlags_eq_of_store]
    · rfl
    · rflags_ext
  · have e1 : ((c : Int) == 1) = false := by
      simp only [beq_eq_false_iff_ne]
      omega
    simp only [e1, h1, Bool.false_eq_true, ↓reduceIte]
    rw [setFlags_eq_of_store]
    · rfl
    · rflags_ext

theorem sar_byte_seven_form [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (rm : BitVec 3)
    (hmode : In64BitMode s) (htmode : In64BitMode t)
    (haccess : (ctx.rex_prefix_present ||| ctx.rex2_prefix_present ||| ctx.vex_prefix_present |||
      ctx.evex_prefix_present) = true ∨ (gprNumber ctx.rex_b4 ctx.rex_b3 rm).toNat < 4)
    (hlock : ctx.lock_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok 7, t)) :
    (X86.Instructions.SAR_GPR8_IMMb ip ctx rm).run s =
      let dst : Operand 8 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeOutputs t dst (sarSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (sarOracleAF t.oracle 7) 7 (dst.read s))
        (sarOracleBits 7) (BitVec.add ip 1#64)) := by
  have hctx : {ctx with lock_prefix_present := false} = ctx := by cases ctx; simp_all
  rw [← hctx]
  unfold X86.Instructions.SAR_GPR8_IMMb
  simp only [Operand.read, writeOutputs, Operand.write]
  spec_run [Read_GPR8 => readGPR8_run _ _ _ haccess hmode,
    Mem_Fetch => hfetch,
    X86.Instructions.Operations.SAR => sar_byte_operation _ _ _ (by decide),
    Write_GPR8 => writeGPR8_run _ _ _ _ haccess (htmode.of_cs_lma_eq rfl rfl)]

theorem decodeLegacy0OpcodeC0_sar [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok 0xf8, t)) :
    (Decode_Legacy_0_Opcode_C0 ip ctx).run s =
      (X86.Instructions.SAR_GPR8_IMMb (BitVec.add ip 2#64) ctx 0).run t := by
  unfold Decode_Legacy_0_Opcode_C0
  decode_modrm_form s t ip hfetch hmode hf
    (show ∀ a b c d e f, Select_Legacy_0_Opcode_C0 ctx true a b c d e f 0xf8 = .ok 7
      from by intros; rfl)

theorem sar_al_seven_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hcode : BytesAt s s.RIP [0xc0, 0xf8, 7]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    Machine.step s = some (.next (afterStep s 3 fun t =>
      writeOutputs t (.reg 0 : Operand 8) (sarSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (sarOracleAF t.oracle 7) 7 ((Operand.reg 0 : Operand 8).read t))
        (sarOracleBits 7) (BitVec.add s.RIP 3#64))) := by
  obtain ⟨fop, fmod⟩ := memFetch_run_of_bytesAt_opcode_modrm s h hcode hlow 0
    (by simp) (by decide)
  have fimm : (Mem_Fetch (BitVec.add s.RIP 2#64) 8).run (afterFetches (beforeFetch s) 3) =
      (.ok 7, afterFetches (beforeFetch s) 4) :=
    memFetch_run_of_bytesAt (beforeFetch s) 3 h.fetchReady hcode hlow 2 (by simp) (by decide)
  have hm (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf : DecoderFeatures (afterFetches (beforeFetch s) 3) :=
    DecoderFeatures.of_sameControls (s := s)
      ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ h.features
  rw [show BitVec.add s.RIP 0#64 = s.RIP from BitVec.add_zero _] at fop fmod
  have hd := decodeLegacy0_run_of_opcodeC0 _ _ _ (legacyContext s.DS) rfl fop (hm 2)
  rw [decodeLegacy0OpcodeC0_sar _ _ _ _ (hm 3) hf fmod,
    sar_byte_seven_form _ _ _ _ _ (hm 3) (hm 4) (.inr (by change (0 : Nat) < 4; decide)) rfl fimm,
    show BitVec.add (BitVec.add s.RIP 2#64) 1#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc _ _ _] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0xc0 [0xf8,7]
    (legacyOpcode_of_check _ ⟨by decide,by decide⟩) hcode hlow hd
    ((hm 4).of_cs_lma_eq rfl rfl)

def sarAlSevenEffect (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p + 3
    writes := [⟨(Operand.reg 0 : Operand 64),
      mergeGPR 8 (((Operand.reg 0 : Operand 8).read s).sshiftRight 7)
        ((Operand.reg 0 : Operand 64).read s)⟩]
    flags := some (sarFlags (StatusFlags.ofRFLAGS s.RFLAGS) 7 ((Operand.reg 0 : Operand 8).read s)) }

theorem sar_al_seven_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xc0,0xf8,7]) (sarAlSevenEffect p) := by
  rintro s h hcode rfl
  refine ⟨_, sar_al_seven_step s h hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeOutputs h 3 _ _ _ _,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_,
      StatusFlagsOutcome.allows_store ?_ _, AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp [writeOutputs, Operand.read, Operand.write, sarSpec, setFlags,
      afterFetches, beforeFetch, resetStepFields]
  · exact sarFlags_allows _ _ _ _ _

@[x86_local] theorem sarAlSevenEffect_local (p : BitVec 64) : Effect.Local (sarAlSevenEffect p) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [sarAlSevenEffect, sarFlags, h.read_reg]
    rfl
  · intro s
    simp [sarAlSevenEffect, Write.Full, Operand.Full]

@[simp] theorem sarAlSevenEffect_components (p : BitVec 64) (s : RamState) :
    (sarAlSevenEffect p s).components = [.reg 0, .flags, .rip] := rfl

attribute [x86_compose] sarAlSevenEffect

theorem shr_byte_seven_form [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (rm : BitVec 3)
    (hmode : In64BitMode s) (htmode : In64BitMode t)
    (haccess : (ctx.rex_prefix_present ||| ctx.rex2_prefix_present ||| ctx.vex_prefix_present |||
      ctx.evex_prefix_present) = true ∨ (gprNumber ctx.rex_b4 ctx.rex_b3 rm).toNat < 4)
    (hlock : ctx.lock_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok 7, t)) :
    (X86.Instructions.SHR_GPR8_IMMb ip ctx rm).run s =
      let dst : Operand 8 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeOutputs t dst (shrSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (shrOracleAF t.oracle 7) 7 (dst.read s))
        (shrOracleBits 7) (BitVec.add ip 1#64)) := by
  have hctx : {ctx with lock_prefix_present := false} = ctx := by cases ctx; simp_all
  rw [← hctx]
  unfold X86.Instructions.SHR_GPR8_IMMb
  simp only [Operand.read, writeOutputs, Operand.write]
  spec_run [Read_GPR8 => readGPR8_run _ _ _ haccess hmode,
    Mem_Fetch => hfetch,
    X86.Instructions.Operations.SHR => shr_operation _ 8 (by decide) _ _,
    Write_GPR8 => writeGPR8_run _ _ _ _ haccess (htmode.of_cs_lma_eq rfl rfl)]

theorem decodeLegacy0OpcodeC0_shr [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok 0xe8, t)) :
    (Decode_Legacy_0_Opcode_C0 ip ctx).run s =
      (X86.Instructions.SHR_GPR8_IMMb (BitVec.add ip 2#64) ctx 0).run t := by
  unfold Decode_Legacy_0_Opcode_C0
  decode_modrm_form s t ip hfetch hmode hf
    (show ∀ a b c d e f, Select_Legacy_0_Opcode_C0 ctx true a b c d e f 0xe8 = .ok 3
      from by intros; rfl)

theorem shr_al_seven_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hcode : BytesAt s s.RIP [0xc0, 0xe8, 7]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    Machine.step s = some (.next (afterStep s 3 fun t =>
      writeOutputs t (.reg 0 : Operand 8) (shrSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (shrOracleAF t.oracle 7) 7 ((Operand.reg 0 : Operand 8).read t))
        (shrOracleBits 7) (BitVec.add s.RIP 3#64))) := by
  obtain ⟨fop, fmod⟩ := memFetch_run_of_bytesAt_opcode_modrm s h hcode hlow 0
    (by simp) (by decide)
  have fimm : (Mem_Fetch (BitVec.add s.RIP 2#64) 8).run (afterFetches (beforeFetch s) 3) =
      (.ok 7, afterFetches (beforeFetch s) 4) :=
    memFetch_run_of_bytesAt (beforeFetch s) 3 h.fetchReady hcode hlow 2 (by simp) (by decide)
  have hm (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf : DecoderFeatures (afterFetches (beforeFetch s) 3) :=
    DecoderFeatures.of_sameControls (s := s)
      ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ h.features
  rw [show BitVec.add s.RIP 0#64 = s.RIP from BitVec.add_zero _] at fop fmod
  have hd := decodeLegacy0_run_of_opcodeC0 _ _ _ (legacyContext s.DS) rfl fop (hm 2)
  rw [decodeLegacy0OpcodeC0_shr _ _ _ _ (hm 3) hf fmod,
    shr_byte_seven_form _ _ _ _ _ (hm 3) (hm 4) (.inr (by change (0 : Nat) < 4; decide)) rfl fimm,
    show BitVec.add (BitVec.add s.RIP 2#64) 1#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc _ _ _] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0xc0 [0xe8,7]
    (legacyOpcode_of_check _ ⟨by decide,by decide⟩) hcode hlow hd
    ((hm 4).of_cs_lma_eq rfl rfl)

def shrAlSevenEffect (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p + 3
    writes := [⟨(Operand.reg 0 : Operand 64),
      mergeGPR 8 ((Operand.reg 0 : Operand 8).read s >>> 7)
        ((Operand.reg 0 : Operand 64).read s)⟩]
    flags := some (shrFlags (StatusFlags.ofRFLAGS s.RFLAGS) 7 ((Operand.reg 0 : Operand 8).read s)) }

theorem shr_al_seven_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xc0,0xe8,7]) (shrAlSevenEffect p) := by
  rintro s h hcode rfl
  refine ⟨_, shr_al_seven_step s h hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeOutputs h 3 _ _ _ _,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_,
      StatusFlagsOutcome.allows_store ?_ _, AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp [writeOutputs, Operand.read, Operand.write, shrSpec, setFlags,
      afterFetches, beforeFetch, resetStepFields]
  · exact shrFlags_allows _ _ _ _ _

@[simp] theorem shrAlSevenEffect_components (p : BitVec 64) (s : RamState) :
    (shrAlSevenEffect p s).components = [.reg 0, .flags, .rip] := rfl

attribute [x86_compose] shrAlSevenEffect

end P256.Proofs.Keygen.Multiply.ProjectiveLookup.Instructions
