import X86Proofs

namespace Base16ct.Proofs.Base16ctUpperDecodeCorrect.Instructions

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem shl32_fold (x : BitVec 32) (cf : BitVec 1) (k : Nat) (hk : 0 < k) (hlt : k < 32) :
    (Runtime.intRange 0 ((k : Int) - 1)).foldl
        (fun (acc : BitVec 32 × BitVec 1) (_ : Int) => (acc.1 <<< 1, acc.1.extractLsb' 31 1)) (x, cf) =
      (x <<< k, x.extractLsb' (32 - k) 1) := by
  have hr : Runtime.intRange 0 ((k : Int) - 1) =
      (List.range k).map (fun i : Nat => (0 : Int) + i) := by
    simp only [x86_runtime]
    congr 2
    omega
  rw [hr, List.foldl_map]
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  clear hk hr
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, ih (by omega)]
    simp only [List.foldl_cons, List.foldl_nil, Prod.mk.injEq]
    constructor
    · exact (BitVec.shiftLeft_add x (k + 1) 1).symm
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have hi0 : i = 0 := by omega
      subst i
      simp only [BitVec.getLsbD_extractLsb', Nat.add_zero, BitVec.getLsbD_shiftLeft]
      simp only [show 31 < 32 from by decide, show ¬31 < k + 1 from by omega,
        decide_true, decide_false, Bool.not_false, Bool.true_and]
      rw [show 31 - (k + 1) = 32 - (k + 1 + 1) by omega]

theorem sar32_fold (x : BitVec 32) (cf : BitVec 1) (k : Nat) (hk : 0 < k) (hlt : k < 32) :
    (Runtime.intRange 0 ((k : Int) - 1)).foldl
        (fun (acc : BitVec 32 × BitVec 1) (_ : Int) => (acc.1.sshiftRight 1, acc.1.extractLsb' 0 1)) (x, cf) =
      (x.sshiftRight k, x.extractLsb' (k - 1) 1) := by
  have hr : Runtime.intRange 0 ((k : Int) - 1) =
      (List.range k).map (fun i : Nat => (0 : Int) + i) := by
    simp only [x86_runtime]
    congr 2
    omega
  rw [hr, List.foldl_map]
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  clear hk hr
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, ih (by omega)]
    simp only [List.foldl_cons, List.foldl_nil, Nat.add_sub_cancel, Prod.mk.injEq]
    constructor
    · exact BitVec.sshiftRight_add.symm
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have hi0 : i = 0 := by omega
      subst i
      simp only [BitVec.getLsbD_extractLsb', Nat.add_zero, BitVec.getLsbD_sshiftRight,
        show ¬32 ≤ 0 from by decide, decide_false, Bool.not_false, Bool.true_and,
        show k + 1 < 32 from by omega, ↓reduceIte]

def shl32Spec (old : StatusFlags) (of af : Bool) (c : Nat) (x : BitVec 32) : BitVec 32 × StatusFlags :=
  let r := x <<< c
  (r, if c = 0 then old else
    { CF := x.getLsbD (32 - c), PF := evenParity (r.extractLsb' 0 8), AF := af, ZF := r == 0,
      SF := r.msb, OF := if c = 1 then r.msb != x.msb else of })

def sar32Spec (old : StatusFlags) (of af : Bool) (c : Nat) (x : BitVec 32) : BitVec 32 × StatusFlags :=
  let r := x.sshiftRight c
  (r, if c = 0 then old else
    { CF := x.getLsbD (c - 1), PF := evenParity (r.extractLsb' 0 8), AF := af, ZF := r == 0,
      SF := r.msb, OF := if c = 1 then false else of })

theorem shl32_operation {σ : Type} (s : X86.State σ) (x : BitVec 32) (count : BitVec 8) :
    (X86.Instructions.Operations.SHL 32 x count).run s =
      let c := shiftCount 32 count
      let (r, flags) := shl32Spec (StatusFlags.ofRFLAGS s.RFLAGS) (oracleBit s.oracle)
        (shrOracleAF s.oracle c) c x
      (.ok r, setFlags { s with oracle := oracleSkip s.oracle (shrOracleBits c) } flags) := by
  obtain ⟨c, hc⟩ : ∃ c, shiftCount 32 count = c := ⟨_, rfl⟩
  have hlt : c < 32 := by
    rw [← hc]
    exact Nat.mod_lt _ (by decide)
  have hc32 : count.toNat % 32 = c := hc
  rw [hc]
  simp only [shl32Spec, shrOracleBits, shrOracleAF]
  unfold X86.Instructions.Operations.SHL
  simp only [isParityEven8_run]
  repeat spec_bind_rfl
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte, Int.reduceToNat,
    unsigned_extractLsb', Nat.reducePow]
  rw [hc32]
  by_cases h0 : c = 0
  · subst h0
    simp
  have e0 : ((c : Int) != 0) = true := by simp; omega
  simp only [e0, h0, ↓reduceIte]
  spec_bind_rfl
  refine (specM_bind_run _ _ (specM_forIn_run _ _
    (fun _ (acc : BitVec _ × BitVec 1) => (acc.1 <<< 1, acc.1.extractLsb' 31 1)) _ _ ?_)).trans ?_
  · intro _ _ _
    rfl
  erw [shl32_fold x _ c (by omega) hlt]
  generalize x <<< c = r
  by_cases h1 : c = 1
  · subst h1
    simp only [↓reduceIte]
    rw [setFlags_eq_of_store]
    · rfl
    · rflags_ext
  · have e1 : ((c : Int) == 1) = false := by simp; omega
    simp only [e1, h1, Bool.false_eq_true, ↓reduceIte]
    rw [setFlags_eq_of_store]
    · rfl
    · rflags_ext

theorem sar32_operation {σ : Type} (s : X86.State σ) (x : BitVec 32) (count : BitVec 8) :
    (X86.Instructions.Operations.SAR 32 x count).run s =
      let c := shiftCount 32 count
      let (r, flags) := sar32Spec (StatusFlags.ofRFLAGS s.RFLAGS) (oracleBit s.oracle)
        (shrOracleAF s.oracle c) c x
      (.ok r, setFlags { s with oracle := oracleSkip s.oracle (shrOracleBits c) } flags) := by
  obtain ⟨c, hc⟩ : ∃ c, shiftCount 32 count = c := ⟨_, rfl⟩
  have hlt : c < 32 := by
    rw [← hc]
    exact Nat.mod_lt _ (by decide)
  have hc32 : count.toNat % 32 = c := hc
  rw [hc]
  simp only [sar32Spec, shrOracleBits, shrOracleAF]
  unfold X86.Instructions.Operations.SAR
  simp only [isParityEven8_run]
  repeat spec_bind_rfl
  simp only [Int.reduceBEq, Bool.false_eq_true, ↓reduceIte, Int.reduceToNat,
    unsigned_extractLsb', Nat.reducePow]
  rw [hc32]
  by_cases h0 : c = 0
  · subst h0
    simp
  have e0 : ((c : Int) != 0) = true := by simp; omega
  simp only [e0, h0, ↓reduceIte]
  spec_bind_rfl
  refine (specM_bind_run _ _ (specM_forIn_run _ _
    (fun _ (acc : BitVec _ × BitVec 1) => (acc.1.sshiftRight 1, acc.1.extractLsb' 0 1)) _ _ ?_)).trans ?_
  · intro _ _ _
    simp only [Int.reduceToNat, Std.le_refl, Int.zero_le_ofNat, Int.zero_add, Int.cast_ofNat_Int,
      Int.reduceLE, checkedSliceRead_eq_pure, Int.toNat_one, Int.toNat_zero,
      Std.Bits.Shift_Right_Arithmetic, decide_true, assert_of_true, Int.reduceLT, ↓reduceIte,
      Std.Bits.Shift_Right_Arithmetic_Restricted, Runtime.shiftRightArithmetic, Nat.reduceBEq,
      Int.reduceBEq, Bool.or_self, Bool.false_eq_true, Bool.or_true, Bool.and_self,
      bind_pure_comp, map_pure, pure_bind, ExceptT.run_map]
    rfl
  erw [sar32_fold x _ c (by omega) hlt]
  generalize x.sshiftRight c = r
  by_cases h1 : c = 1
  · subst h1
    simp only [↓reduceIte]
    rw [setFlags_eq_of_store]
    · rfl
    · rflags_ext
  · have e1 : ((c : Int) == 1) = false := by simp; omega
    simp only [e1, h1, Bool.false_eq_true, ↓reduceIte]
    rw [setFlags_eq_of_store]
    · rfl
    · rflags_ext

theorem shl_r32_imm8_form [X86.Machine.Bindings] (s t : X86.Machine.RamState)
    (ip : BitVec 64) (ctx : Instruction_Context) (rm : BitVec 3) (count : BitVec 8)
    (hmode : In64BitMode s) (hfetch : (Mem_Fetch ip 8).run s = (.ok count, t))
    (htmode : In64BitMode t) (hsize : ctx.operand_size = 32) (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.SHL_GPRv_IMMb_C1r4 ip ctx rm).run s =
      let dst : Operand 32 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      let c := shiftCount 32 count
      (.ok (), writeOutputs t dst (shl32Spec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (shrOracleAF t.oracle c) c (dst.read s)) (shrOracleBits c)
        (BitVec.add ip 1#64)) := by
  have hcontext : {ctx with operand_size := 32, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.SHL_GPRv_IMMb_C1r4
  simp only [Operand.read_reg32, writeOutputs, Operand.write_reg32]
  spec_run [
    Read_GPR => readGPR32_run _ _ hmode,
    Mem_Fetch => hfetch,
    X86.Instructions.Operations.SHL => shl32_operation _ _ _,
    Write_GPR => writeGPR32_run _ _ _ (htmode.of_cs_lma_eq rfl rfl)]

theorem selectLegacy0OpcodeC1_run_of_shl_register (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 4#3) :
    Select_Legacy_0_Opcode_C1 context true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_0_Opcode_C1, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and,
    strictAnd]

theorem decodeLegacy0OpcodeC1_run_of_shl_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 4#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_C1 ip context).run s =
      (X86.Instructions.SHL_GPRv_IMMb_C1r4 (BitVec.add ip 2#64) context
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_C1
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeC1_run_of_shl_register context a b c d e f modrm hmod hreg)

theorem decodeLegacy0_run_of_rex_C1_shl [Bindings] (s : RamState) (h : ReadyToStep s) (rex modrm imm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4)
    (hcode : BytesAt s s.RIP [rex, 0xC1, modrm, imm]) (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP 1#64) (rexContext s.DS rex.toBitVec)).run
        (afterFetches (beforeFetch s) 2) =
      some ((X86.Instructions.SHL_GPRv_IMMb_C1r4 (BitVec.add s.RIP 3#64)
        (rexContext s.DS rex.toBitVec) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) 4)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [rex, 0xC1, modrm, imm] := hcode
  have f2 : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok 0xC1, afterFetches (beforeFetch s) 3) :=
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
  rw [decodeLegacy0_run_of_opcodeC1 _ _ _ _ rfl f2 (hmode 3),
    decodeLegacy0OpcodeC1_run_of_shl_register _ _ _ _ _ hmod hreg (hmode 4) hfeatures f3,
    show BitVec.add (BitVec.add s.RIP 1#64) 2#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc s.RIP 1#64 2#64]
  rfl

theorem shl_r32_imm8_rex_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex modrm imm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4)
    (hcode : BytesAt s s.RIP [rex, 0xC1, modrm, imm]) (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    let dst : Operand 32 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    let c := shiftCount 32 imm.toBitVec
    X86.Machine.step s = some (.next (afterStep s 4 fun t =>
      writeOutputs t dst (shl32Spec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (shrOracleAF t.oracle c) c (dst.read t))
        (shrOracleBits c) (BitVec.add s.RIP 4#64))) := by
  have hdecode := decodeLegacy0_run_of_rex_C1_shl s h rex modrm imm hmod hreg hcode hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have himm : (Mem_Fetch (BitVec.add s.RIP 3#64) 8).run (afterFetches (beforeFetch s) 4) =
      (.ok imm.toBitVec, afterFetches (beforeFetch s) 5) :=
    memFetch_run_of_bytesAt (beforeFetch s) 4 h.fetchReady hcode hlow 3 (by simp) (by decide)
  rw [shl_r32_imm8_form _ _ _ _ _ _ (hmode 4) himm (hmode 5)
    (hrex.operand_size s.DS) rfl,
    show BitVec.add (BitVec.add s.RIP 3#64) 1#64 = BitVec.add s.RIP 4#64 from
      BitVec.add_assoc s.RIP 3#64 1#64] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · first | exact h.ready.repeatClear | (simp only [writeOutputs, Operand.write_repeat]; exact h.ready.repeatClear)
  exact step_rex_legacy0 s _ h rex 0xC1 [modrm, imm] hrex.rexPrefix
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode ((hmode 5).of_cs_lma_eq rfl rfl)

theorem shl_r32_imm8_rex_ready [Bindings] {s : RamState} (h : ReadyToStep s)
    (rex modrm imm : UInt8) :
    let dst : Operand 32 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    let c := shiftCount 32 imm.toBitVec
    ReadyToStep (afterStep s 4 fun t =>
      writeOutputs t dst (shl32Spec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (shrOracleAF t.oracle c) c (dst.read t))
        (shrOracleBits c) (BitVec.add s.RIP 4#64)) :=
  ReadyToStep.afterStep_writeOutputs h 4 _ _ _ _

def shl32Flags (old : StatusFlags) (c : Nat) (x : BitVec 32) : StatusFlagsOutcome :=
  let r := x <<< c
  if c = 0 then .ofStatusFlags old else
    { CF := some (x.getLsbD (32 - c)), PF := some (evenParity (r.extractLsb' 0 8)), AF := none,
      ZF := some (r == 0), SF := some r.msb, OF := if c = 1 then some (r.msb != x.msb) else none }

theorem shl32Flags_allows (old : StatusFlags) (of af : Bool) (c : Nat) (x : BitVec 32) :
    (shl32Flags old c x).Allows (shl32Spec old of af c x).2 := by
  unfold shl32Flags shl32Spec
  by_cases h0 : c = 0
  · simp only [h0, ↓reduceIte]
    exact StatusFlagsOutcome.allows_ofStatusFlags old
  · by_cases h1 : c = 1 <;>
      simp [h0, h1, StatusFlagsOutcome.Allows, FlagAllows]

def shlR32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 32).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), (a <<< c).setWidth 64⟩]
    flags := some (shl32Flags (StatusFlags.ofRFLAGS s.RFLAGS) c a) }

theorem shl_r32_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm imm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xC1, modrm, imm])
      (shlR32Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (shiftCount 32 imm.toBitVec)) := by
  rintro s h hcode rfl
  refine ⟨_, shl_r32_imm8_rex_step s h rex modrm imm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), shl_r32_imm8_rex_ready h rex modrm imm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, shl32Spec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply shl32Flags_allows

theorem sar_r32_imm8_form [X86.Machine.Bindings] (s t : X86.Machine.RamState)
    (ip : BitVec 64) (ctx : Instruction_Context) (rm : BitVec 3) (count : BitVec 8)
    (hmode : In64BitMode s) (hfetch : (Mem_Fetch ip 8).run s = (.ok count, t))
    (htmode : In64BitMode t) (hsize : ctx.operand_size = 32) (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.SAR_GPRv_IMMb ip ctx rm).run s =
      let dst : Operand 32 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      let c := shiftCount 32 count
      (.ok (), writeOutputs t dst (sar32Spec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (shrOracleAF t.oracle c) c (dst.read s)) (shrOracleBits c)
        (BitVec.add ip 1#64)) := by
  have hcontext : {ctx with operand_size := 32, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.SAR_GPRv_IMMb
  simp only [Operand.read_reg32, writeOutputs, Operand.write_reg32]
  spec_run [
    Read_GPR => readGPR32_run _ _ hmode,
    Mem_Fetch => hfetch,
    X86.Instructions.Operations.SAR => sar32_operation _ _ _,
    Write_GPR => writeGPR32_run _ _ _ (htmode.of_cs_lma_eq rfl rfl)]

theorem selectLegacy0OpcodeC1_run_of_sar_register (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) (hreg : modrm.extractLsb' 3 3 = 7#3) :
    Select_Legacy_0_Opcode_C1 context true a b c d e f modrm = .ok 7 := by
  simp [Select_Legacy_0_Opcode_C1, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, hreg, HAnd.hAnd, AndOp.and,
    strictAnd]

theorem decodeLegacy0OpcodeC1_run_of_sar_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hreg : modrm.extractLsb' 3 3 = 7#3) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_C1 ip context).run s =
      (X86.Instructions.SAR_GPRv_IMMb (BitVec.add ip 2#64) context
        (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_C1
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0OpcodeC1_run_of_sar_register context a b c d e f modrm hmod hreg)

theorem decodeLegacy0_run_of_rex_C1_sar [Bindings] (s : RamState) (h : ReadyToStep s) (rex modrm imm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7)
    (hcode : BytesAt s s.RIP [rex, 0xC1, modrm, imm]) (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP 1#64) (rexContext s.DS rex.toBitVec)).run
        (afterFetches (beforeFetch s) 2) =
      some ((X86.Instructions.SAR_GPRv_IMMb (BitVec.add s.RIP 3#64)
        (rexContext s.DS rex.toBitVec) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) 4)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [rex, 0xC1, modrm, imm] := hcode
  have f2 : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok 0xC1, afterFetches (beforeFetch s) 3) :=
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
  rw [decodeLegacy0_run_of_opcodeC1 _ _ _ _ rfl f2 (hmode 3),
    decodeLegacy0OpcodeC1_run_of_sar_register _ _ _ _ _ hmod hreg (hmode 4) hfeatures f3,
    show BitVec.add (BitVec.add s.RIP 1#64) 2#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc s.RIP 1#64 2#64]
  rfl

theorem sar_r32_imm8_rex_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex modrm imm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7)
    (hcode : BytesAt s s.RIP [rex, 0xC1, modrm, imm]) (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    let dst : Operand 32 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    let c := shiftCount 32 imm.toBitVec
    X86.Machine.step s = some (.next (afterStep s 4 fun t =>
      writeOutputs t dst (sar32Spec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (shrOracleAF t.oracle c) c (dst.read t))
        (shrOracleBits c) (BitVec.add s.RIP 4#64))) := by
  have hdecode := decodeLegacy0_run_of_rex_C1_sar s h rex modrm imm hmod hreg hcode hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have himm : (Mem_Fetch (BitVec.add s.RIP 3#64) 8).run (afterFetches (beforeFetch s) 4) =
      (.ok imm.toBitVec, afterFetches (beforeFetch s) 5) :=
    memFetch_run_of_bytesAt (beforeFetch s) 4 h.fetchReady hcode hlow 3 (by simp) (by decide)
  rw [sar_r32_imm8_form _ _ _ _ _ _ (hmode 4) himm (hmode 5)
    (hrex.operand_size s.DS) rfl,
    show BitVec.add (BitVec.add s.RIP 3#64) 1#64 = BitVec.add s.RIP 4#64 from
      BitVec.add_assoc s.RIP 3#64 1#64] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · first | exact h.ready.repeatClear | (simp only [writeOutputs, Operand.write_repeat]; exact h.ready.repeatClear)
  exact step_rex_legacy0 s _ h rex 0xC1 [modrm, imm] hrex.rexPrefix
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode ((hmode 5).of_cs_lma_eq rfl rfl)

theorem sar_r32_imm8_rex_ready [Bindings] {s : RamState} (h : ReadyToStep s)
    (rex modrm imm : UInt8) :
    let dst : Operand 32 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    let c := shiftCount 32 imm.toBitVec
    ReadyToStep (afterStep s 4 fun t =>
      writeOutputs t dst (sar32Spec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (shrOracleAF t.oracle c) c (dst.read t))
        (shrOracleBits c) (BitVec.add s.RIP 4#64)) :=
  ReadyToStep.afterStep_writeOutputs h 4 _ _ _ _

def sar32Flags (old : StatusFlags) (c : Nat) (x : BitVec 32) : StatusFlagsOutcome :=
  let r := x.sshiftRight c
  if c = 0 then .ofStatusFlags old else
    { CF := some (x.getLsbD (c - 1)), PF := some (evenParity (r.extractLsb' 0 8)), AF := none,
      ZF := some (r == 0), SF := some r.msb, OF := if c = 1 then some false else none }

theorem sar32Flags_allows (old : StatusFlags) (of af : Bool) (c : Nat) (x : BitVec 32) :
    (sar32Flags old c x).Allows (sar32Spec old of af c x).2 := by
  unfold sar32Flags sar32Spec
  by_cases h0 : c = 0
  · simp only [h0, ↓reduceIte]
    exact StatusFlagsOutcome.allows_ofStatusFlags old
  · by_cases h1 : c = 1 <;>
      simp [h0, h1, StatusFlagsOutcome.Allows, FlagAllows]

def sarR32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 32).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), (a.sshiftRight c).setWidth 64⟩]
    flags := some (sar32Flags (StatusFlags.ofRFLAGS s.RFLAGS) c a) }

theorem sar_r32_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm imm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xC1, modrm, imm])
      (sarR32Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (shiftCount 32 imm.toBitVec)) := by
  rintro s h hcode rfl
  refine ⟨_, sar_r32_imm8_rex_step s h rex modrm imm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), sar_r32_imm8_rex_ready h rex modrm imm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, sar32Spec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply sar32Flags_allows

end Base16ct.Proofs.Base16ctUpperDecodeCorrect.Instructions
