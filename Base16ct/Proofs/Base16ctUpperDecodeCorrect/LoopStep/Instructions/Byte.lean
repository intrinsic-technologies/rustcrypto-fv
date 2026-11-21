import X86Proofs

namespace Base16ct.Proofs.Base16ctUpperDecodeCorrect.Instructions

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem writeGPR8_run_of_rex {σ : Type} (s : X86.State σ) (r : BitVec 5)
    (v : BitVec 8) (hmode : In64BitMode s) :
    (Write_GPR8 r true v).run s =
      (.ok (), {s with GPR := Vector.set s.GPR (gprIndex r) (mergeGPR 8 v s.GPR[gprIndex r])}) := by
  unfold Write_GPR8
  rw [specM_bind_run _ _ hmode]
  obtain ⟨i, rfl⟩ : ∃ i : Fin 32, r = BitVec.ofNat 5 i.val := ⟨⟨r.toNat, r.isLt⟩, by simp⟩
  finite_cases i <;> rfl

theorem and_r8_imm8_form [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (rm : BitVec 3) (imm : BitVec 8) (hmode : In64BitMode s)
    (hrex : ctx.rex_prefix_present = true) (hlock : ctx.lock_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok imm, t)) (htmode : In64BitMode t) :
    (X86.Instructions.AND_GPR8_IMMb_80r4 ip ctx rm).run s =
      let dst : Operand 8 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeOutputs t dst (andSpec (oracleBit t.oracle) (dst.read s) (imm.signExtend 8)) 1
        (BitVec.add ip 1#64)) := by
  have hcontext : {ctx with rex_prefix_present := true, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.AND_GPR8_IMMb_80r4
  simp only [Operand.read, writeOutputs, Operand.write]
  spec_run [
    Read_GPR8 => readGPR8_run_of_rex _ _ hmode,
    Mem_Fetch => hfetch,
    X86.Instructions.Operations.AND => and_operation _ 8 (by decide) _ _,
    Write_GPR8 => writeGPR8_run_of_rex _ _ _ (htmode.of_cs_lma_eq rfl rfl)]

theorem add_r8_r8_form {σ : Type} [PhysicalMemory σ] (s : X86.State σ) (ip : BitVec 64)
    (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (hrex : ctx.rex_prefix_present = true) (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.ADD_GPR8_GPR8_00 ip ctx reg rm).run s =
      let dst : Operand 8 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      let src : Operand 8 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (.ok (), writeOutputs s dst (addSpec (dst.read s) (src.read s)) 0 ip) := by
  have hcontext : {ctx with rex_prefix_present := true, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.ADD_GPR8_GPR8_00
  simp only [Operand.read, writeOutputs, Operand.write]
  spec_run [
    Read_GPR8 => readGPR8_run_of_rex _ _ hmode,
    X86.Instructions.Operations.ADD => add_operation _ 8 (by decide) _ _,
    Write_GPR8 => writeGPR8_run_of_rex _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

theorem test_r16_r16_form {σ : Type} [PhysicalMemory σ] (s : X86.State σ) (ip : BitVec 64)
    (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (hsize : ctx.operand_size = 16) (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.TEST_GPRv_GPRv ip ctx reg rm).run s =
      let dst : Operand 16 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      let src : Operand 16 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (.ok (), writeFlagsOutputs s (testSpec (oracleBit s.oracle) (dst.read s) (src.read s)) 1 ip) := by
  have hcontext : {ctx with operand_size := 16, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.TEST_GPRv_GPRv
  simp only [Operand.read, writeFlagsOutputs]
  spec_run [
    Read_GPR => readGPR16_run _ _ hmode,
    X86.Instructions.Operations.TEST => test_operation _ 16 (by decide) _ _]

theorem decodeLegacy0_run_of_opcode00 [Bindings] (s u : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hrex2 : context.rex2_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x00, u)) (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_00 ip context).run u) := by
  unfold Decode_Legacy_0
  rw [ite_eq_right (fun h => Bool.false_ne_true (hrex2.symm.trans h))]
  rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
  repeat erw [decodeLegacy0_modeGuard_run _ _ hmode]
  rfl

theorem selectLegacy0Opcode80_run_of_r4_register (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 4#3) :
    Select_Legacy_0_Opcode_80 context true a b c d e f modrm = .ok 18 := by
  simp [Select_Legacy_0_Opcode_80, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and,
    strictAnd]

theorem decodeLegacy0Opcode80_run_of_r4_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_80 ip context).run s =
      (X86.Instructions.AND_GPR8_IMMb_80r4 (BitVec.add ip 2#64) context (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_80
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode80_run_of_r4_register context a b c d e f modrm hmod hreg)

theorem decodeLegacy0_run_of_rex_80_r4 [Bindings] (s : RamState) (h : ReadyToStep s)
    (rex modrm : UInt8) (imm : BitVec 8) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 4)
    (hcode : BytesAt s s.RIP (rex :: 0x80 :: modrm :: immBytes 8 imm))
    (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP 1#64) (rexContext s.DS rex.toBitVec)).run
        (afterFetches (beforeFetch s) 2) =
      some ((X86.Instructions.AND_GPR8_IMMb_80r4 (BitVec.add s.RIP 3#64)
        (rexContext s.DS rex.toBitVec) (modrmRm modrm)).run (afterFetches (beforeFetch s) 4)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (rex :: 0x80 :: modrm :: immBytes 8 imm) := hcode
  have hlow' : s.RIP.toNat + (rex :: 0x80 :: modrm :: immBytes 8 imm).length ≤ 2^32 := by
    simpa using hlow
  have f2 : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok 0x80, afterFetches (beforeFetch s) 3) :=
    memFetch_run_of_bytesAt (beforeFetch s) 2 hf hc hlow' 1 (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 4) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  have f3 : (Mem_Fetch (BitVec.add (BitVec.add s.RIP 1#64) 1#64) 8).run
      (afterFetches (beforeFetch s) 3) = (.ok modrm.toBitVec, afterFetches (beforeFetch s) 4) := by
    rw [show BitVec.add (BitVec.add s.RIP 1#64) 1#64 = BitVec.add s.RIP 2#64 from
      BitVec.add_assoc s.RIP 1#64 1#64]
    exact memFetch_run_of_bytesAt (beforeFetch s) 3 hf hc hlow' 2 (by simp) (by decide)
  rw [decodeLegacy0_run_of_opcode80 _ _ _ _ rfl f2 (hmode 3),
    decodeLegacy0Opcode80_run_of_r4_register _ _ _ _ _ hmod hreg (hmode 4) hfeatures f3,
    show BitVec.add (BitVec.add s.RIP 1#64) 2#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc s.RIP 1#64 2#64]
  rfl

theorem and_r8_imm8_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (rex modrm : UInt8) (imm : BitVec 8) (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 4)
    (hcode : BytesAt s s.RIP (rex :: 0x80 :: modrm :: immBytes 8 imm))
    (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    let dst : Operand 8 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s 4 fun t =>
      writeOutputs t dst (andSpec (oracleBit t.oracle) (dst.read t) (imm.signExtend 8)) 1
        (BitVec.add s.RIP 4#64))) := by
  have hdecode := decodeLegacy0_run_of_rex_80_r4 s h rex modrm imm hmod hreg
    hcode hlow
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (rex :: 0x80 :: modrm :: immBytes 8 imm) := hcode
  have hlow' : s.RIP.toNat + (rex :: 0x80 :: modrm :: immBytes 8 imm).length ≤ 2^32 := by
    simpa using hlow
  have himm := memFetch_run_of_bytesAt_imm (beforeFetch s) 4 h.fetchReady hc hlow' 8 (by decide) imm 3
    (immBytes_getElem?_append [rex, 0x80, modrm] imm) (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [and_r8_imm8_form _ _ (BitVec.add s.RIP 3#64) _ _ imm (hmode 4) rfl rfl himm (hmode 5),
    show BitVec.add (BitVec.add s.RIP 3#64) 1#64 = BitVec.add s.RIP 4#64 from
      BitVec.add_assoc _ _ _] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · first | exact h.ready.repeatClear | (simp only [writeOutputs, Operand.write_repeat]; exact h.ready.repeatClear)
  exact step_rex_legacy0 s _ h rex 0x80 (modrm :: immBytes 8 imm) hrex
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow' hdecode ((hmode 5).of_cs_lma_eq rfl rfl)

theorem and_r8_imm8_ready [Bindings] {s : RamState} (h : ReadyToStep s) (rex modrm : UInt8) (imm : BitVec 8) :
    let dst : Operand 8 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    ReadyToStep (afterStep s 4 fun t =>
      writeOutputs t dst (andSpec (oracleBit t.oracle) (dst.read t) (imm.signExtend 8)) 1
        (BitVec.add s.RIP 4#64)) :=
  ReadyToStep.afterStep_writeOutputs h 4 _ _ 1 _

theorem selectLegacy0Opcode00_run_of_register (context : Instruction_Context) (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_0_Opcode_00 context true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_0_Opcode_00, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

theorem decodeLegacy0Opcode00_run_of_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_00 ip context).run s =
      (X86.Instructions.ADD_GPR8_GPR8_00 (BitVec.add ip 2#64) context
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_00
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode00_run_of_register context a b c d e f modrm hmod)

theorem decodeLegacy0_run_of_rex_00 [Bindings] (s : RamState) (h : ReadyToStep s) (rex modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hcode : BytesAt s s.RIP [rex, 0x00, modrm])
    (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP 1#64) (rexContext s.DS rex.toBitVec)).run
        (afterFetches (beforeFetch s) 2) =
      some ((X86.Instructions.ADD_GPR8_GPR8_00 (BitVec.add s.RIP 3#64)
        (rexContext s.DS rex.toBitVec) (modrmReg modrm) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) 4)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [rex, 0x00, modrm] := hcode
  have f2 : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok 0x00, afterFetches (beforeFetch s) 3) :=
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
  rw [decodeLegacy0_run_of_opcode00 _ _ _ _ rfl f2 (hmode 3),
    decodeLegacy0Opcode00_run_of_register _ _ _ _ _ hmod (hmode 4) hfeatures f3,
    show BitVec.add (BitVec.add s.RIP 1#64) 2#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc s.RIP 1#64 2#64]
  rfl

theorem add_r8_r8_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex modrm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP [rex, 0x00, modrm]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    let dst : Operand 8 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    let src : Operand 8 := .reg (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
    X86.Machine.step s = some (.next (afterStep s 3 fun t =>
      writeOutputs t dst (addSpec (dst.read t) (src.read t)) 0
        (BitVec.add s.RIP 3#64))) := by
  have hdecode := decodeLegacy0_run_of_rex_00 s h rex modrm hmod hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 4) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [add_r8_r8_form _ _ _ _ _ hmode rfl rfl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · first | exact h.ready.repeatClear | (simp only [writeOutputs, Operand.write_repeat]; exact h.ready.repeatClear)
  exact step_rex_legacy0 s _ h rex 0x00 [modrm] hrex
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem add_r8_r8_ready [Bindings] {s : RamState} (h : ReadyToStep s) (rex modrm : UInt8) :
    let dst : Operand 8 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    let src : Operand 8 := .reg (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
    ReadyToStep (afterStep s 3 fun t =>
      writeOutputs t dst (addSpec (dst.read t) (src.read t)) 0
        (BitVec.add s.RIP 3#64)) :=
  ReadyToStep.afterStep_writeOutputs h 3 _ _ 0 _

theorem read_writeOutputs_self8 {σ : Type} [PhysicalMemory σ] (s : X86.State σ) (r : BitVec 5)
    (out : BitVec 8 × StatusFlags) (used : Nat) (next : BitVec 64) :
    (Operand.reg r : Operand 64).read (writeOutputs s (.reg r : Operand 8) out used next) =
      mergeGPR 8 out.1 ((Operand.reg r : Operand 64).read s) := by
  simp [writeOutputs, setFlags, Operand.read, Operand.write]

def andR8Imm8Effect (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (s : RamState) : Effect :=
  let r := (Operand.reg dst : Operand 8).read s &&& imm
  { rip := p + 4
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 8 r ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (andFlags r) }

theorem and_r8_imm8_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (imm : BitVec 8) (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p (rex :: 0x80 :: modrm :: immBytes 8 imm))
      (andR8Imm8Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm) := by
  rintro s h hc rfl
  refine ⟨_, and_r8_imm8_step s h rex modrm imm hrex hmod hreg hc.bytesAt
    (by simpa using hc.low (by simp) (by simp)), and_r8_imm8_ready h rex modrm imm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ 1 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ 1 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep, read_writeOutputs_self8]
    simp only [andSpec, BitVec.signExtend_eq, Operand.read_afterFetches, Operand.read_beforeFetch]
  · simp only [BitVec.signExtend_eq]
    exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

def addR8R8Effect (p : BitVec 64) (dst src : BitVec 5) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 8).read s
  let b := (Operand.reg src : Operand 8).read s
  { rip := p + 3
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 8 (a + b) ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (addSpec a b).2) }

theorem add_r8_r8_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0x00, modrm])
      (addR8R8Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))) := by
  rintro s h hc rfl
  refine ⟨_, add_r8_r8_step s h rex modrm hrex hmod hc.bytesAt
    (hc.low (by simp) (by simp)), add_r8_r8_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep, read_writeOutputs_self8]
    simp only [addSpec, Operand.read_afterFetches, Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem decodeLegacy0_run_of_osz_85 [Bindings] (s : RamState) (h : ReadyToStep s) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hcode : BytesAt s s.RIP [0x66, 0x85, modrm])
    (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP 1#64) (oszContext s.DS)).run
        (afterFetches (beforeFetch s) 2) =
      some ((X86.Instructions.TEST_GPRv_GPRv (BitVec.add s.RIP 3#64)
        (oszContext s.DS) (modrmReg modrm) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) 4)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [0x66, 0x85, modrm] := hcode
  have f2 : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok 0x85, afterFetches (beforeFetch s) 3) :=
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
  rw [decodeLegacy0_run_of_opcode85 _ _ _ _ rfl f2 (hmode 3),
    decodeLegacy0Opcode85_run_of_register _ _ _ _ _ hmod (hmode 4) hfeatures f3,
    show BitVec.add (BitVec.add s.RIP 1#64) 2#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc s.RIP 1#64 2#64]
  rfl

theorem test_r16_r16_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (modrm : UInt8) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP [0x66, 0x85, modrm]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    let dst : Operand 16 := .reg (gprNumber 0 0 (modrmRm modrm))
    let src : Operand 16 := .reg (gprNumber 0 0 (modrmReg modrm))
    X86.Machine.step s = some (.next (afterStep s 3 fun t =>
      writeFlagsOutputs t (testSpec (oracleBit t.oracle) (dst.read t) (src.read t)) 1
        (BitVec.add s.RIP 3#64))) := by
  have hd := decodeLegacy0_run_of_osz_85 s h modrm hmod hcode hlow
  have hm : In64BitMode (afterFetches (beforeFetch s) 4) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [test_r16_r16_form _ _ _ _ _ hm rfl rfl] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · first | exact h.ready.repeatClear | (simp only [writeOutputs, Operand.write_repeat]; exact h.ready.repeatClear)
  exact step_scan_legacy0 s _ h [0x66] 0x85 [modrm] (scanPrefix_of_66_2e (by decide))
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by decide) hcode hlow
    (by rw [scanContext_66]; exact hd) (hm.of_cs_lma_eq rfl rfl)

def testR16R16Effect (p : BitVec 64) (dst src : BitVec 5) (s : RamState) : Effect :=
  { rip := p + 3
    flags := some (testFlags ((Operand.reg dst : Operand 16).read s &&&
      (Operand.reg src : Operand 16).read s)) }

theorem test_r16_r16_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x66, 0x85, modrm])
      (testR16R16Effect p (gprNumber 0 0 (modrmRm modrm)) (gprNumber 0 0 (modrmReg modrm))) := by
  rintro s h hc rfl
  refine ⟨_, test_r16_r16_step s h modrm hmod hc.bytesAt (hc.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeFlagsOutputs h 3 _ 1 _,
    ⟨afterStep_writeFlagsOutputs_rip h 3 _ 1 _, trivial,
      StatusFlagsOutcome.allows_store ?_ _, AgreesExcept.afterStep_writeFlagsOutputs s 3 _ 1 _⟩⟩
  exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

end Base16ct.Proofs.Base16ctUpperDecodeCorrect.Instructions
