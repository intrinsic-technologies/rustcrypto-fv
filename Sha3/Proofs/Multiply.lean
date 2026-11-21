import X86Proofs.Step.AfterStep
import X86Proofs.Step.LegacyStep
import X86Proofs.Step.Decode.Legacy0
import X86Proofs.Step.Escape
import X86Proofs.Program.Effect

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

def mul64Lo (x y : BitVec 64) : BitVec 64 := BitVec.ofNat 64 (x.toNat * y.toNat)

def mul64Hi (x y : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (x.toNat * y.toNat / 2^64)

def multiplyFlags (o : X86.Runtime.Oracle) (overflow : Bool) : StatusFlags :=
  ⟨overflow, oracleBit (oracleSkip o 3), oracleBit (oracleSkip o 2),
    oracleBit (oracleSkip o 1), oracleBit o, overflow⟩

def mul64State {σ : Type} (s : X86.State σ) (y : BitVec 64) : X86.State σ :=
  let x := s.GPR[0]
  setFlags {s with
    GPR := (Vector.set (Vector.set s.GPR 0 (mul64Lo x y) (by decide)) 2 (mul64Hi x y) (by decide))
    oracle := oracleSkip s.oracle 4} (multiplyFlags s.oracle (!(mul64Hi x y == 0)))

theorem oracle_mk_skip (o : X86.Runtime.Oracle) (k : Nat) :
    ({ bits := o.bits, position := o.position + k, limit := o.limit } : X86.Runtime.Oracle) =
      oracleSkip o k := rfl

theorem oracleTake_match_skip (o : X86.Runtime.Oracle) (k : Nat) :
    X86.Runtime.Oracle.take.match_1 (fun _ => Nat) o.limit
      (fun limit => min 1 (limit - (o.position + k))) (fun _ => 1) =
      oracleTakeCount (oracleSkip o k) 1 := rfl

set_option maxRecDepth 3000 in
theorem mul64_operation {σ : Type} (s : X86.State σ) (y : BitVec 64) :
    (X86.Instructions.Operations.MUL 64 y).run s = (.ok (), mul64State s y) := by
  change ((Except.ok () : Except (X86.Runtime.Error X86.Exception) Unit), _) = _
  have hdiv (n : Nat) : (n : Int) / 18446744073709551616 = (n / 18446744073709551616 : Nat) :=
    (Int.natCast_ediv n 18446744073709551616).symm
  simp only [Int.reduceToNat, Runtime.Unsigned, Int.toNat_zero, BitVec.extractLsb'_eq_self, ←
    Int.natCast_mul, Int.reducePow, hdiv, BitVec.ofInt_natCast, BitVec.ofNat_eq_ofNat, beq_iff_eq,
    Int.toNat_one, oracle_mk_skip, oracleTake_match_skip, oracleTake_match_eq_oracleTakeCount,
    oracleTakeGo_one, Nat.add_assoc, Nat.reduceAdd, Int.zero_mul,
    Int.pow_zero, Int.ediv_one, setSlice_full, ne_eq, reduceCtorEq, not_false_eq_true,
    Vector.getElem_set_ne, Int.one_mul, mul64State, setFlags, StatusFlags.store, multiplyFlags,
    mul64Hi, Nat.reducePow, mul64Lo, Prod.mk.injEq, State.mk.injEq, and_self, and_true,
    true_and]
  rw [ite_zero_one]
  simp only [beq_zero_eq_decide]

theorem selectLegacy0OpcodeF7_run_of_mul_register (context : Instruction_Context)
    (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 4#3) :
    Select_Legacy_0_Opcode_F7 context true a b c d e f modrm = .ok 3 := by
  simp [Select_Legacy_0_Opcode_F7, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and,
    strictAnd]

theorem decodeLegacy0OpcodeF7_run_of_mul_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_F7 ip context).run s =
      (X86.Instructions.MUL_GPRv (BitVec.add ip 2#64) context
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_F7
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f =>
      selectLegacy0OpcodeF7_run_of_mul_register context a b c d e f modrm hmod hreg)

theorem decodeLegacy0_run_of_rex_F7_mul [Bindings] (s : RamState) (h : ReadyToStep s)
    (rex modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4)
    (hcode : BytesAt s s.RIP [rex, 0xF7, modrm]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP 1#64) (rexContext s.DS rex.toBitVec)).run
        (afterFetches (beforeFetch s) 2) =
      some ((X86.Instructions.MUL_GPRv (BitVec.add s.RIP 3#64)
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
    decodeLegacy0OpcodeF7_run_of_mul_register _ _ _ _ _ hmod hreg (hmode 4) hfeatures f3,
    show BitVec.add (BitVec.add s.RIP 1#64) 2#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc s.RIP 1#64 2#64]
  rfl

theorem mul_r64_form {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ)
    (ip : BitVec 64) (ctx : Instruction_Context) (rm : BitVec 3) (hmode : In64BitMode s)
    (hsize : ctx.operand_size = 64) (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.MUL_GPRv ip ctx rm).run s =
      let src : Operand 64 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), mul64State {s with Next_IP := ip} (src.read s)) := by
  have hcontext : {ctx with operand_size := 64, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.MUL_GPRv
  simp only [Operand.read_reg64]
  spec_run [Read_GPR => readGPR64_run _ _ hmode,
    X86.Instructions.Operations.MUL => mul64_operation _ _]

theorem mul_r64_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4)
    (hcode : BytesAt s s.RIP [rex, 0xF7, modrm]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    let src : Operand 64 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s 3 fun t =>
      mul64State {t with Next_IP := BitVec.add s.RIP 3#64} (src.read t))) := by
  have hdecode := decodeLegacy0_run_of_rex_F7_mul s h rex modrm hmod hreg hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 4) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [mul_r64_form _ _ _ _ hmode (hrex.operand_size s.DS) rfl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex 0xF7 [modrm] hrex.rexPrefix
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode
    (hmode.of_cs_lma_eq rfl rfl)

def imul64Overflow (x y : BitVec 64) : Bool :=
  !((x * y).toInt == x.toInt * y.toInt)

set_option maxRecDepth 3000 in
theorem imul64_operation {σ : Type} (s : X86.State σ) (x y : BitVec 64) :
    (X86.Instructions.Operations.IMUL_SINGLE 64 x y).run s =
      (.ok (x * y), setFlags {s with oracle := oracleSkip s.oracle 4}
        (multiplyFlags s.oracle (imul64Overflow x y))) := by
  change ((Except.ok _ : Except (X86.Runtime.Error X86.Exception) (BitVec 64)), _) = _
  simp only [Int.reduceToNat, Runtime.Signed, Int.toNat_zero, Int.pow_zero, Int.ediv_one,
    BitVec.ofInt_mul, BitVec.ofInt_toInt, BitVec.toInt_mul, Nat.reducePow, beq_iff_eq,
    BitVec.ofNat_eq_ofNat, Int.toNat_one, oracle_mk_skip, oracleTake_match_skip, oracleTake_match_eq_oracleTakeCount, oracleTakeGo_one, Nat.add_assoc, Nat.reduceAdd,
    setFlags, StatusFlags.store, multiplyFlags, imul64Overflow, Prod.mk.injEq,
    State.mk.injEq, and_self, and_true, true_and]
  rw [ite_zero_one]
  simp only [Bool.beq_eq_decide_eq]

theorem imul_r64_r64_form {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ)
    (ip : BitVec 64) (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (hsize : ctx.operand_size = 64) (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.IMUL_GPRv_GPRv ip ctx reg rm).run s =
      let dst : Operand 64 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let src : Operand 64 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeOutputs s dst (dst.read s * src.read s,
        multiplyFlags s.oracle (imul64Overflow (dst.read s) (src.read s))) 4 ip) := by
  have hcontext : {ctx with operand_size := 64, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.IMUL_GPRv_GPRv
  simp only [Operand.read_reg64, writeOutputs, Operand.write_reg64]
  spec_run [Read_GPR => readGPR64_run _ _ hmode,
    X86.Instructions.Operations.IMUL_SINGLE => imul64_operation _ _ _,
    Write_GPR => writeGPR64_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

theorem selectLegacy1OpcodeAF_run_of_imul_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_AF context true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_1_Opcode_AF, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

theorem decodeLegacy1OpcodeAF_run_of_imul_register [Bindings] (s t : RamState)
    (ip : BitVec 64) (context : Instruction_Context) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_AF ip context).run s =
      (X86.Instructions.IMUL_GPRv_GPRv (BitVec.add ip 2#64) context
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_AF
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy1OpcodeAF_run_of_imul_register context a b c d e f modrm hmod)

theorem decodeLegacy1_run_of_rex_0F_AF_imul [Bindings] (s : RamState) (h : ReadyToStep s)
    (rex modrm : UInt8) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP [rex, 0x0F, 0xAF, modrm]) (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    (Decode_Legacy_1 (BitVec.add s.RIP 2#64) (rexContext s.DS rex.toBitVec)).run
        (afterFetches (beforeFetch s) 3) =
      some ((X86.Instructions.IMUL_GPRv_GPRv (BitVec.add s.RIP 4#64)
        (rexContext s.DS rex.toBitVec) (modrmReg modrm) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) 5)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [rex, 0x0F, 0xAF, modrm] := hcode
  have f3 : (Mem_Fetch (BitVec.add s.RIP 2#64) 8).run (afterFetches (beforeFetch s) 3) =
      (.ok 0xAF, afterFetches (beforeFetch s) 4) :=
    memFetch_run_of_bytesAt (beforeFetch s) 3 hf hc hlow 2 (by simp) (by decide)
  have f4 : (Mem_Fetch (BitVec.add (BitVec.add s.RIP 2#64) 1#64) 8).run
      (afterFetches (beforeFetch s) 4) = (.ok modrm.toBitVec, afterFetches (beforeFetch s) 5) := by
    rw [show BitVec.add (BitVec.add s.RIP 2#64) 1#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc s.RIP 2#64 1#64]
    exact memFetch_run_of_bytesAt (beforeFetch s) 4 hf hc hlow 3 (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 5) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [decodeLegacy1_run_of_opcodeAF _ _ _ _ rfl (hmode 4) f3,
    decodeLegacy1OpcodeAF_run_of_imul_register _ _ _ _ _ hmod (hmode 5) hfeatures f4,
    show BitVec.add (BitVec.add s.RIP 2#64) 2#64 = BitVec.add s.RIP 4#64 from
      BitVec.add_assoc s.RIP 2#64 2#64]
  rfl

theorem imul_r64_r64_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP [rex, 0x0F, 0xAF, modrm]) (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    let dst : Operand 64 := .reg (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
    let src : Operand 64 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s 4 fun t =>
      writeOutputs t dst (dst.read t * src.read t,
        multiplyFlags t.oracle (imul64Overflow (dst.read t) (src.read t))) 4
        (BitVec.add s.RIP 4#64))) := by
  have hdecode := decodeLegacy1_run_of_rex_0F_AF_imul s h rex modrm hmod hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 5) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [imul_r64_r64_form _ _ _ _ _ hmode (hrex.operand_size s.DS) rfl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy1 s _ h rex 0xAF [modrm] hrex.rexPrefix (by decide)
    hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem mul64State_rax {σ : Type} (s : X86.State σ) (y : BitVec 64) :
    (mul64State s y).GPR[0] = mul64Lo s.GPR[0] y := by
  simp [mul64State, setFlags]

theorem mul64State_rdx {σ : Type} (s : X86.State σ) (y : BitVec 64) :
    (mul64State s y).GPR[2] = mul64Hi s.GPR[0] y := by
  simp [mul64State, setFlags]

theorem mul64State_gpr_of_ne {σ : Type} (s : X86.State σ) (y : BitVec 64)
    (i : Fin 32) (h0 : i.val ≠ 0) (h2 : i.val ≠ 2) :
    (mul64State s y).GPR[i] = s.GPR[i] := by
  simp [mul64State, setFlags, Ne.symm h0, Ne.symm h2]

set_option maxRecDepth 3000 in
theorem afterStep_mul64State_rax (s : RamState) (length : Nat) (src : Operand 64)
    (nextIP : BitVec 64) :
    (afterStep s length fun t => mul64State {t with Next_IP := nextIP} (src.read t)).GPR[0] =
      mul64Lo s.GPR[0] (src.read s) := by
  change (mul64State {afterFetches (beforeFetch s) (length + 1) with Next_IP := nextIP}
    (src.read (afterFetches (beforeFetch s) (length + 1)))).GPR[0] = _
  rw [mul64State_rax]
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
  rfl

set_option maxRecDepth 3000 in
theorem afterStep_mul64State_rdx (s : RamState) (length : Nat) (src : Operand 64)
    (nextIP : BitVec 64) :
    (afterStep s length fun t => mul64State {t with Next_IP := nextIP} (src.read t)).GPR[2] =
      mul64Hi s.GPR[0] (src.read s) := by
  change (mul64State {afterFetches (beforeFetch s) (length + 1) with Next_IP := nextIP}
    (src.read (afterFetches (beforeFetch s) (length + 1)))).GPR[2] = _
  rw [mul64State_rdx]
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
  rfl

theorem afterStep_mul64State_rip [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) (src : Operand 64) (nextIP : BitVec 64) :
    (afterStep s length fun t => mul64State {t with Next_IP := nextIP} (src.read t)).RIP =
      nextIP := by
  simp [afterStep, finishStep, mul64State, setFlags, afterFetches, beforeFetch,
    resetStepFields, h.ready.repeatClear, h.ready.msr]

theorem ReadyToStep.afterStep_mul64State [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) (src : Operand 64) (nextIP : BitVec 64) :
    ReadyToStep (afterStep s length fun t =>
      mul64State {t with Next_IP := nextIP} (src.read t)) := by
  have hst : SameControls s (afterStep s length fun t =>
      mul64State {t with Next_IP := nextIP} (src.read t)) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hc := h.cpu
  have hr := h.ready
  exact ⟨⟨hc.cs, hc.ss, hc.ds, hc.es, hc.cpl, hc.cr0, hc.cr4, hc.efer, hc.maxPhysical, hc.early,
      reportsCPUFeature_of_sameControls hst hc.lam, reportsCPUFeature_of_sameControls hst hc.lass,
      hc.debug, hc.aet⟩,
    ⟨h.memory.cr3, h.memory.tables⟩,
    ⟨hr.event, hr.active, hr.sti, hr.movss, hr.singleStep, hr.taskSwitch, hr.breakpoint,
      hr.busLock, StatusFlags.trapFlagClear_store _ hr.tf,
      StatusFlags.resumeFlagClear_store _ hr.rf, hr.repeatClear, hr.msr⟩,
    smrrUnblocked_of_sameControls hst h.smrr, writeBackMemoryType_of_sameControls hst h.memoryType,
    h.features.of_sameControls hst⟩

theorem imul_r64_r64_ready [Bindings] {s : RamState} (h : ReadyToStep s) (rex modrm : UInt8) :
    let dst : Operand 64 := .reg (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
    let src : Operand 64 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    ReadyToStep (afterStep s 4 fun t =>
      writeOutputs t dst (dst.read t * src.read t,
        multiplyFlags t.oracle (imul64Overflow (dst.read t) (src.read t))) 4
        (BitVec.add s.RIP 4#64)) :=
  ReadyToStep.afterStep_writeOutputs h 4 _ _ 4 _

def multiplyFlagsOutcome (overflow : Bool) : StatusFlagsOutcome :=
  ⟨some overflow, none, none, none, none, some overflow⟩

theorem multiplyFlags_allows (o : X86.Runtime.Oracle) (overflow : Bool) :
    (multiplyFlagsOutcome overflow).Allows (multiplyFlags o overflow) :=
  ⟨rfl, trivial, trivial, trivial, trivial, rfl⟩

def mulR64Effect (p : BitVec 64) (src : BitVec 5) (s : RamState) : Effect :=
  let x := s.GPR[0]
  let y := (Operand.reg src : Operand 64).read s
  {rip := p + 3
   writes := [⟨(Operand.reg 0 : Operand 64), mul64Lo x y⟩,
     ⟨(Operand.reg 2 : Operand 64), mul64Hi x y⟩]
   flags := some (multiplyFlagsOutcome (!(mul64Hi x y == 0)))}

theorem mulR64Effect_components (p : BitVec 64) (src : BitVec 5) (s : RamState) :
    (mulR64Effect p src s).components = [.reg 0, .reg 2, .flags, .rip] := rfl

theorem mulR64Effect_avoids (p : BitVec 64) (src : BitVec 5) (s : RamState) (code : CodeMap) :
    (mulR64Effect p src s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [mulR64Effect_components, Component.Covers]) code

set_option maxRecDepth 3000 in
theorem AgreesExcept.afterStep_mul64State (s : RamState) (length : Nat) (src : Operand 64)
    (nextIP : BitVec 64) :
    AgreesExcept [.reg 0, .reg 2, .flags, .rip] s
      (afterStep s length fun t => mul64State {t with Next_IP := nextIP} (src.read t)) := by
  refine ⟨fun c hc _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
  · cases c with
    | reg r =>
      have h0 : r ≠ 0 := by intro h; subst r; exact hc (by simp)
      have h2 : r ≠ 2 := by intro h; subst r; exact hc (by simp)
      have hi0 : (gprIndex r).val ≠ 0 := by
        intro hi
        exact h0 (BitVec.eq_of_toNat_eq hi)
      have hi2 : (gprIndex r).val ≠ 2 := by
        intro hi
        exact h2 (BitVec.eq_of_toNat_eq hi)
      change (mul64State {afterFetches (beforeFetch s) (length + 1) with Next_IP := nextIP}
        (src.read (afterFetches (beforeFetch s) (length + 1)))).GPR[gprIndex r] = _
      rw [mul64State_gpr_of_ne _ _ _ hi0 hi2]
      rfl
    | flags => exact absurd (by simp) hc
    | rip => exact absurd (by simp) hc
    | mem addr len => exact fun _ _ => rfl
    | xmm x => exact Component.agrees_xmm_of_zmm rfl x
    | mxcsr => rfl
    | fpr x => exact Component.agrees_fpr_of_fp87 rfl x
    | fsw => rfl
    | fcc => rfl
    | ftw => rfl
    | fcw => rfl
    | fpuPtr => rfl
    | df => exact dfBit_store _ _
  · simp only [fixedPart, afterStep, finishStep, mul64State, setFlags, afterFetches,
      beforeFetch, resetStepFields, clearStatusFlags_store]

theorem mul_r64_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xF7, modrm])
      (mulR64Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  let src : Operand 64 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
  refine ⟨_, mul_r64_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), ReadyToStep.afterStep_mul64State h 3 _ _,
    ⟨afterStep_mul64State_rip h 3 _ _, ?_, ?_,
      AgreesExcept.afterStep_mul64State s 3 _ _⟩⟩
  · change (Operand.reg 0 : Operand 64).read _ = _ ∧
      (Operand.reg 2 : Operand 64).read _ = _
    simp only [Operand.read_reg64]
    exact ⟨afterStep_mul64State_rax s 3 src (BitVec.add s.RIP 3#64),
      afterStep_mul64State_rdx s 3 src (BitVec.add s.RIP 3#64)⟩
  · change (multiplyFlagsOutcome (!(mul64Hi s.GPR[0] (src.read s) == 0))).Allows
      (StatusFlags.ofRFLAGS ((multiplyFlags (afterFetches (beforeFetch s) 4).oracle
        (!(mul64Hi s.GPR[0] (src.read (afterFetches (beforeFetch s) 4)) == 0))).store s.RFLAGS))
    apply StatusFlagsOutcome.allows_store
    simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact multiplyFlags_allows _ _

theorem imul_r64_r64_imm8_form [Bindings] (s t : RamState)
    (ip : BitVec 64) (ctx : Instruction_Context) (reg rm : BitVec 3) (imm : BitVec 8)
    (hmode : In64BitMode s) (hmode' : In64BitMode t)
    (hsize : ctx.operand_size = 64) (hlock : ctx.lock_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok imm, t)) :
    (X86.Instructions.IMUL_GPRv_GPRv_IMMb ip ctx reg rm).run s =
      let dst : Operand 64 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let src : Operand 64 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeOutputs t dst (src.read s * imm.signExtend 64,
        multiplyFlags t.oracle (imul64Overflow (src.read s) (imm.signExtend 64))) 4 (ip + 1)) := by
  have hcontext : {ctx with operand_size := 64, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.IMUL_GPRv_GPRv_IMMb
  simp only [Operand.read_reg64, writeOutputs, Operand.write_reg64]
  spec_run [Read_GPR => readGPR64_run _ _ hmode,
    Mem_Fetch => hfetch,
    X86.Instructions.Operations.IMUL_SINGLE => imul64_operation _ _ _,
    Write_GPR => writeGPR64_run _ _ _ (hmode'.of_cs_lma_eq rfl rfl)]

theorem selectLegacy0Opcode6B_run_of_imul_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_0_Opcode_6B context true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_0_Opcode_6B, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

theorem decodeLegacy0Opcode6B_run_of_imul_register [Bindings] (s t : RamState)
    (ip : BitVec 64) (context : Instruction_Context) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_6B ip context).run s =
      (X86.Instructions.IMUL_GPRv_GPRv_IMMb (BitVec.add ip 2#64) context
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_6B
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode6B_run_of_imul_register context a b c d e f modrm hmod)

theorem decodeLegacy0_run_of_rex_6B_imul [Bindings] (s : RamState) (h : ReadyToStep s)
    (rex modrm imm : UInt8) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP [rex, 0x6B, modrm, imm]) (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP 1#64) (rexContext s.DS rex.toBitVec)).run
        (afterFetches (beforeFetch s) 2) =
      some ((X86.Instructions.IMUL_GPRv_GPRv_IMMb (BitVec.add s.RIP 3#64)
        (rexContext s.DS rex.toBitVec) (modrmReg modrm) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) 4)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [rex, 0x6B, modrm, imm] := hcode
  have f2 : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok 0x6B, afterFetches (beforeFetch s) 3) :=
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
  rw [decodeLegacy0_run_of_opcode6B _ _ _ _ rfl f2 (hmode 3),
    decodeLegacy0Opcode6B_run_of_imul_register _ _ _ _ _ hmod (hmode 4) hfeatures f3,
    show BitVec.add (BitVec.add s.RIP 1#64) 2#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc s.RIP 1#64 2#64]
  rfl

theorem imul_r64_r64_imm8_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (rex modrm imm : UInt8) (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP [rex, 0x6B, modrm, imm]) (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    let dst : Operand 64 := .reg (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
    let src : Operand 64 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s 4 fun t =>
      writeOutputs t dst (src.read t * imm.toBitVec.signExtend 64,
        multiplyFlags t.oracle (imul64Overflow (src.read t) (imm.toBitVec.signExtend 64))) 4
        (BitVec.add s.RIP 4#64))) := by
  have hdecode := decodeLegacy0_run_of_rex_6B_imul s h rex modrm imm hmod hcode hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have f4 : (Mem_Fetch (BitVec.add s.RIP 3#64) 8).run (afterFetches (beforeFetch s) 4) =
      (.ok imm.toBitVec, afterFetches (beforeFetch s) 5) :=
    memFetch_run_of_bytesAt (beforeFetch s) 4 h.fetchReady hcode hlow 3 (by simp) (by decide)
  rw [imul_r64_r64_imm8_form _ _ _ _ _ _ _ (hmode 4) (hmode 5)
    (hrex.operand_size s.DS) rfl f4] at hdecode
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch] at hdecode ⊢
  rw [show BitVec.add s.RIP 3#64 + 1 = BitVec.add s.RIP 4#64 from
    BitVec.add_assoc s.RIP 3#64 1#64] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex 0x6B [modrm, imm] hrex.rexPrefix
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode
    ((hmode 5).of_cs_lma_eq rfl rfl)

def imulR64R64Effect (p : BitVec 64) (dst src : BitVec 5) (s : RamState) : Effect :=
  let x := (Operand.reg dst : Operand 64).read s
  let y := (Operand.reg src : Operand 64).read s
  {rip := p + 4
   writes := [⟨(Operand.reg dst : Operand 64), x * y⟩]
   flags := some (multiplyFlagsOutcome (imul64Overflow x y))}

def imulR64Imm8Effect (p : BitVec 64) (dst src : BitVec 5) (imm : UInt8)
    (s : RamState) : Effect :=
  let x := (Operand.reg src : Operand 64).read s
  let y := imm.toBitVec.signExtend 64
  {rip := p + 4
   writes := [⟨(Operand.reg dst : Operand 64), x * y⟩]
   flags := some (multiplyFlagsOutcome (imul64Overflow x y))}

theorem imulR64R64Effect_components (p : BitVec 64) (dst src : BitVec 5) (s : RamState) :
    (imulR64R64Effect p dst src s).components = [.reg dst, .flags, .rip] := rfl

theorem imulR64Imm8Effect_components (p : BitVec 64) (dst src : BitVec 5) (imm : UInt8)
    (s : RamState) :
    (imulR64Imm8Effect p dst src imm s).components = [.reg dst, .flags, .rip] := rfl

theorem imulR64R64Effect_avoids (p : BitVec 64) (dst src : BitVec 5) (s : RamState)
    (code : CodeMap) : (imulR64R64Effect p dst src s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [imulR64R64Effect_components, Component.Covers]) code

theorem imulR64Imm8Effect_avoids (p : BitVec 64) (dst src : BitVec 5) (imm : UInt8)
    (s : RamState) (code : CodeMap) : (imulR64Imm8Effect p dst src imm s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [imulR64Imm8Effect_components, Component.Covers]) code

theorem imul_r64_r64_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0x0F, 0xAF, modrm])
      (imulR64R64Effect p (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, imul_r64_r64_step s h rex modrm hrex hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), imul_r64_r64_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ 4 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ 4 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact multiplyFlags_allows _ _

theorem imul_r64_r64_imm8_effect_step [Bindings] (p : BitVec 64) (rex modrm imm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0x6B, modrm, imm])
      (imulR64Imm8Effect p (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm) := by
  rintro s h hcode rfl
  refine ⟨_, imul_r64_r64_imm8_step s h rex modrm imm hrex hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), ReadyToStep.afterStep_writeOutputs h 4 _ _ 4 _,
    ⟨afterStep_writeOutputs_rip h 4 _ _ 4 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ 4 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact multiplyFlags_allows _ _

end X86Proofs
