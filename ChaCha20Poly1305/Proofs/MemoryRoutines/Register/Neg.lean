import X86Proofs.Instructions.Sub.Operation
import X86Proofs.Core.Operand
import X86Proofs.Step.Decode.Legacy0
import X86Proofs.Step.Decode.Legacy0OpcodeF7
import X86Proofs.Step.AfterStep
import X86Proofs.Step.LegacyStep
import X86Proofs.Program.Effect

namespace ChaCha20Poly1305.Proofs.MemoryRoutines.Register

open X86 X86.Helpers X86Proofs X86.Machine X86.UserProcess

set_option maxHeartbeats 1000000 in
theorem neg32_operation {σ : Type} (s : X86.State σ) (x : BitVec 32) :
    (X86.Instructions.Operations.NEG 32 x).run s =
      (.ok (subSpec 0 x).1, setFlags s (subSpec 0 x).2) := by
  have hv : BitVec.ofInt 32 (-(x.toNat : Int)) = -x := by
    simpa only [BitVec.toNat_zero, Int.natCast_zero, Int.zero_sub, BitVec.zero_sub] using
      (ofInt_sub_toNat (0#32) x)
  have ha : max (-(x.toNat : Int) % 16) 0 = -((x.toNat : Int) % 16) ↔
      x.toNat % 16 = 0 := by omega
  have hc : ¬ x = 0#32 ↔ 0 < x.toNat := by
    rw [BitVec.toNat_eq]
    change (¬ x.toNat = 0) ↔ 0 < x.toNat
    omega
  unfold X86.Instructions.Operations.NEG
  simp only [isParityEven8_run]
  repeat spec_bind_rfl
  simp only [Int.reduceToNat, BitVec.ofNat_eq_ofNat, unsigned_eq, BitVec.toNat_ofNat,
    Nat.reducePow, Nat.zero_mod, Int.cast_ofNat_Int, Int.toNat_one, Nat.pow_one,
    Int.add_zero, Int.zero_sub, Int.toNat_zero, Int.pow_zero, Int.ediv_one, hv, signed_eq,
    BitVec.toInt_zero, beq_iff_eq, Int.reduceSub, Nat.reduceAdd, extractLsb'_msb,
    beq_zero_eq_decide, BitVec.neg_eq_zero_iff, decide_eq_true_eq, Int.reduceAdd, BitVec.toNat_ofInt,
    Int.ofNat_toNat, BitVec.extractLsb'_zero, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
    Int.natCast_emod, ha, specM_pure_run, subSpec, BitVec.zero_sub, ne_eq, decide_not,
    setFlags, StatusFlags.store]
  congr 2
  rw [ite_zero_one, ite_one_zero, ite_zero_one, ite_one_zero, ite_zero_one]
  have haf : ¬ x.toNat % 16 = 0 ↔ 0 < x.toNat % 16 := by omega
  simp only [Bool.decide_eq_true, ← decide_not, haf, hc]

theorem neg_r32_form {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ)
    (ip : BitVec 64) (ctx : Instruction_Context) (rm : BitVec 3) (hmode : In64BitMode s)
    (hsize : ctx.operand_size = 32) (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.NEG_GPRv ip ctx rm).run s =
      let dst : Operand 32 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeOutputs s dst (subSpec 0 (dst.read s)) 0 ip) := by
  have hcontext : {ctx with operand_size := 32, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.NEG_GPRv
  simp only [Operand.read_reg32, writeOutputs, Operand.write_reg32, oracleSkip_zero]
  spec_run [
    Read_GPR => readGPR32_run _ _ hmode,
    X86.Instructions.Operations.NEG => neg32_operation _ _,
    Write_GPR => writeGPR32_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

theorem selectLegacy0OpcodeF7_run_of_neg_register (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 3#3) :
    Select_Legacy_0_Opcode_F7 context true a b c d e f modrm = .ok 7 := by
  simp [Select_Legacy_0_Opcode_F7, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and,
    strictAnd]

theorem decodeLegacy0OpcodeF7_run_of_neg_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 3#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_F7 ip context).run s =
      (X86.Instructions.NEG_GPRv (BitVec.add ip 2#64) context
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_F7
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f ↦ selectLegacy0OpcodeF7_run_of_neg_register context a b c d e f modrm hmod hreg)

theorem decodeLegacy0_run_of_rex_F7_neg [Bindings] (s : RamState) (h : ReadyToStep s) (rex modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 3)
    (hcode : BytesAt s s.RIP [rex, 0xF7, modrm]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP 1#64) (rexContext s.DS rex.toBitVec)).run
        (afterFetches (beforeFetch s) 2) =
      some ((X86.Instructions.NEG_GPRv (BitVec.add s.RIP 3#64)
        (rexContext s.DS rex.toBitVec) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) 4)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [rex, 0xF7, modrm] := hcode
  have f2 : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok 0xF7, afterFetches (beforeFetch s) 3) :=
    memFetch_run_of_bytesAt (beforeFetch s) 2 hf hc hlow 1 (by simp) (by decide)
  have f3 : (Mem_Fetch (BitVec.add (BitVec.add s.RIP 1#64) 1#64) 8).run
      (afterFetches (beforeFetch s) 3) = (.ok modrm.toBitVec, afterFetches (beforeFetch s) 4) := by
    rw [show BitVec.add (BitVec.add s.RIP 1#64) 1#64 = BitVec.add s.RIP 2#64 from
      BitVec.add_assoc s.RIP 1#64 1#64]
    exact memFetch_run_of_bytesAt (beforeFetch s) 3 hf hc hlow 2 (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 4) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [decodeLegacy0_run_of_opcodeF7 _ _ _ _ rfl f2 (hmode 3),
    decodeLegacy0OpcodeF7_run_of_neg_register _ _ _ _ _ hmod hreg (hmode 4) hfeatures f3,
    show BitVec.add (BitVec.add s.RIP 1#64) 2#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc s.RIP 1#64 2#64]
  rfl

theorem decodeLegacy0_run_of_F7_neg [Bindings] (s : RamState) (h : ReadyToStep s) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 3)
    (hcode : BytesAt s s.RIP [0xF7, modrm]) (hlow : s.RIP.toNat + 2 ≤ 2^32) :
    (Decode_Legacy_0 s.RIP (legacyContext s.DS)).run (afterFetches (beforeFetch s) 1) =
      some ((X86.Instructions.NEG_GPRv (BitVec.add s.RIP 2#64)
        (legacyContext s.DS) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) 3)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [0xF7, modrm] := hcode
  have f1 : (Mem_Fetch s.RIP 8).run (afterFetches (beforeFetch s) 1) =
      (.ok 0xF7, afterFetches (beforeFetch s) 2) := by
    have := memFetch_run_of_bytesAt (beforeFetch s) 1 hf hc hlow 0 (by simp) (by decide)
    rwa [show BitVec.add (beforeFetch s).RIP (BitVec.ofNat 64 0) = (beforeFetch s).RIP
      from BitVec.add_zero _] at this
  have f2 : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok modrm.toBitVec, afterFetches (beforeFetch s) 3) :=
    memFetch_run_of_bytesAt (beforeFetch s) 2 hf hc hlow 1 (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 3) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [decodeLegacy0_run_of_opcodeF7 _ _ _ _ rfl f1 (hmode 2),
    decodeLegacy0OpcodeF7_run_of_neg_register _ _ _ _ _ hmod hreg (hmode 3) hfeatures f2]
  rfl

theorem neg_r32_step [Bindings] (s : RamState) (h : ReadyToStep s) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 3)
    (hcode : BytesAt s s.RIP [0xF7, modrm]) (hlow : s.RIP.toNat + 2 ≤ 2^32) :
    let dst : Operand 32 := .reg (gprNumber 0 0 (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s 2 fun t ↦
      writeOutputs t dst (subSpec 0 (dst.read t)) 0 (BitVec.add s.RIP 2#64))) := by
  have hdecode := decodeLegacy0_run_of_F7_neg s h modrm hmod hreg hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 3) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [neg_r32_form _ _ _ _ hmode
    (legacyContext_operand_size s.DS) rfl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0xF7 [modrm]
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem neg_r32_ready [Bindings] {s : RamState} (h : ReadyToStep s) (modrm : UInt8) :
    let dst : Operand 32 := .reg (gprNumber 0 0 (modrmRm modrm))
    ReadyToStep (afterStep s 2 fun t ↦
      writeOutputs t dst (subSpec 0 (dst.read t)) 0 (BitVec.add s.RIP 2#64)) :=
  ReadyToStep.afterStep_writeOutputs h 2 _ _ 0 _

theorem neg_r32_rex_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 3)
    (hcode : BytesAt s s.RIP [rex, 0xF7, modrm]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    let dst : Operand 32 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s 3 fun t ↦
      writeOutputs t dst (subSpec 0 (dst.read t)) 0 (BitVec.add s.RIP 3#64))) := by
  have hdecode := decodeLegacy0_run_of_rex_F7_neg s h rex modrm hmod hreg hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 4) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [neg_r32_form _ _ _ _ hmode
    (hrex.operand_size s.DS) rfl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex 0xF7 [modrm] hrex.rexPrefix
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem neg_r32_rex_ready [Bindings] {s : RamState} (h : ReadyToStep s) (rex modrm : UInt8) :
    let dst : Operand 32 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    ReadyToStep (afterStep s 3 fun t ↦
      writeOutputs t dst (subSpec 0 (dst.read t)) 0 (BitVec.add s.RIP 3#64)) :=
  ReadyToStep.afterStep_writeOutputs h 3 _ _ 0 _

def negR32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 32).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), (-a).setWidth 64⟩]
    flags := some (.ofStatusFlags (subSpec 0 a).2) }

theorem negR32Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState) :
    (negR32Effect p len dst s).components = [.reg dst, .flags, .rip] := rfl

theorem negR32Effect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState)
    (code : CodeMap) : (negR32Effect p len dst s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [negR32Effect_components, Component.Covers]) code

theorem neg_r32_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 3) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p [0xF7, modrm])
      (negR32Effect p 2 (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, neg_r32_step s h modrm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), neg_r32_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 2 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, subSpec, BitVec.ofNat_eq_ofNat, BitVec.zero_sub,
      Operand.read_afterFetches, Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem neg_r32_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 3) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p [rex, 0xF7, modrm])
      (negR32Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, neg_r32_rex_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), neg_r32_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, subSpec, BitVec.ofNat_eq_ofNat, BitVec.zero_sub,
      Operand.read_afterFetches, Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem neg_ecx_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p [0xF7, 0xD9])
      (negR32Effect p 2 1) :=
  neg_r32_effect_step p 0xD9 (by decide) (by decide)

theorem neg_r8d_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p [0x41, 0xF7, 0xD8])
      (negR32Effect p 3 8) :=
  neg_r32_rex_effect_step p 0x41 0xD8 (by unfold RexNoWPrefix; decide) (by decide) (by decide)

end ChaCha20Poly1305.Proofs.MemoryRoutines.Register
