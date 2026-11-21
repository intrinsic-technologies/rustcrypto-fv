import X86Proofs

namespace Base16ct.Proofs.Base16ctUpperDecodeCorrect.Instructions

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem movsx32_operation (x : BitVec 16) :
    X86.Instructions.Operations.MOVSX 32 16 x = .ok (x.signExtend 32) := by
  simp [X86.Instructions.Operations.MOVSX, x86_runtime, bind, pure, Except.bind, Except.pure]

theorem movsx_r32_r16_form {σ : Type} [PhysicalMemory σ] (s : X86.State σ)
    (ip : BitVec 64) (ctx : Instruction_Context) (reg rm : BitVec 3)
    (hmode : In64BitMode s) (hsize : ctx.operand_size = 32)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.MOVSX_GPRv_GPR16 ip ctx reg rm).run s =
      let dst : Operand 32 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let src : Operand 16 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeResult s dst ((src.read s).signExtend 32) ip) := by
  have hcontext : {ctx with operand_size := 32, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.MOVSX_GPRv_GPR16
  simp only [movsx32_operation, Operand.read, writeResult, Operand.write_reg32]
  spec_run [
    Read_GPR => readGPR16_run _ _ hmode,
    Write_GPR => writeGPR32_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

theorem decodeLegacy1_run_of_opcodeBF [Bindings] (s u : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hrex2 : context.rex2_prefix_present = false)
    (hmode : In64BitMode u) (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xBF, u)) :
    (Decode_Legacy_1 ip context).run s =
      some ((Decode_Legacy_1_Opcode_BF ip context).run u) := by
  unfold Decode_Legacy_1
  rw [ite_eq_right (fun h => Bool.false_ne_true (hrex2.symm.trans h))]
  rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
  repeat erw [decodeLegacy0_modeGuard_run _ _ hmode]
  repeat erw [decodeLegacy1_modeGuard_run _ _ _ _ hmode]
  rfl

theorem selectLegacy1OpcodeBF_run_of_register (context : Instruction_Context) (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_BF context true a b c d e f modrm = .ok 4 := by
  simp [Select_Legacy_1_Opcode_BF, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

theorem decodeLegacy1OpcodeBF_run_of_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_BF ip context).run s =
      (X86.Instructions.MOVSX_GPRv_GPR16 (BitVec.add ip 2#64) context
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_BF
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  refine (specM_bind_run _ _ hfetch).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 7 6) _ (s := t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 5 3) _ (s := t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 2 0) _ (s := t) rfl).trans ?_
  refine (decoderSelect_run t (fun mode a b c d e f =>
    Select_Legacy_1_Opcode_BF context mode a b c d e f modrm) _ 4 hmode hf
    (fun a b c d e f => selectLegacy1OpcodeBF_run_of_register context a b c d e f modrm hmod)).trans ?_
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 2)) _ (s := t) rfl).trans ?_
  exact specM_bind_pure_unit_run _ t

theorem decodeLegacy1_run_of_BF_register [Bindings] (s : RamState) (h : ReadyToStep s)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (bytes : List UInt8) (k : Nat) (hk : k + 1 < 15)
    (hop : bytes[k]? = some 0xBF) (hm : bytes[k + 1]? = some modrm)
    (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32) :
    (Decode_Legacy_1 (BitVec.add s.RIP (BitVec.ofNat 64 k)) ctx).run
        (afterFetches (beforeFetch s) (k + 1)) =
      some ((X86.Instructions.MOVSX_GPRv_GPR16 (BitVec.add s.RIP (BitVec.ofNat 64 (k + 2))) ctx
        (modrmReg modrm) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) (k + 3))) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP bytes := hcode
  have hlen : k + 1 < bytes.length := by
    rcases Nat.lt_or_ge (k + 1) bytes.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hm; cases hm
  have f1 : (Mem_Fetch (BitVec.add s.RIP (BitVec.ofNat 64 k)) 8).run
      (afterFetches (beforeFetch s) (k + 1)) = (.ok 0xBF, afterFetches (beforeFetch s) (k + 2)) := by
    have := memFetch_run_of_bytesAt (beforeFetch s) (k + 1) hf hc hlow k (by omega) (by omega)
    rw [show bytes[k] = 0xBF from
      Option.some.inj ((List.getElem?_eq_getElem _).symm.trans hop)] at this
    exact this
  have f2 : (Mem_Fetch (BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 k)) 1#64) 8).run
      (afterFetches (beforeFetch s) (k + 2)) =
        (.ok modrm.toBitVec, afterFetches (beforeFetch s) (k + 3)) := by
    have := memFetch_run_of_bytesAt (beforeFetch s) (k + 2) hf hc hlow (k + 1) hlen hk
    rw [show bytes[k + 1] = modrm from
      Option.some.inj ((List.getElem?_eq_getElem _).symm.trans hm)] at this
    rw [show BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 k)) 1#64 =
      BitVec.add s.RIP (BitVec.ofNat 64 (k + 1)) from add_ofNat_add s.RIP k 1]
    exact this
  have hmode (j : Nat) : In64BitMode (afterFetches (beforeFetch s) j) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) (k + 3)) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [decodeLegacy1_run_of_opcodeBF _ _ _ _ hrex2 (hmode _) f1,
    decodeLegacy1OpcodeBF_run_of_register _ _ _ _ _ hmod (hmode _) hfeatures f2,
    show BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 k)) 2#64 =
      BitVec.add s.RIP (BitVec.ofNat 64 (k + 2)) from add_ofNat_add s.RIP k 2]
  rfl

theorem movsx_r32_r16_rex_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (rex modrm : UInt8) (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP [rex, 0x0f, 0xbf, modrm])
    (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    let dst : Operand 32 := .reg (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
    let src : Operand 16 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s 4 fun t =>
      writeResult t dst ((src.read t).signExtend 32) (BitVec.add s.RIP 4#64))) := by
  have hd := decodeLegacy1_run_of_BF_register s h (rexContext s.DS rex.toBitVec) rfl
    modrm hmod [rex, 0x0f, 0xbf, modrm] 2 (by decide) (by simp) (by simp) hcode hlow
  have hm : In64BitMode (afterFetches (beforeFetch s) 5) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [movsx_r32_r16_form _ _ _ _ _ hm (hrex.operand_size s.DS) rfl] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · first | exact h.ready.repeatClear | (simp only [writeOutputs, Operand.write_repeat]; exact h.ready.repeatClear)
  exact step_rex_legacy1 s _ h rex 0xbf [modrm] hrex.rexPrefix
    ⟨by decide, by decide⟩ hcode hlow hd (hm.of_cs_lma_eq rfl rfl)

def movsxR32R16Effect (p : BitVec 64) (dst src : BitVec 5) (s : RamState) : Effect :=
  { rip := p + 4
    writes := [⟨(Operand.reg dst : Operand 64),
      (((Operand.reg src : Operand 16).read s).signExtend 32).setWidth 64⟩] }

theorem movsx_r32_r16_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0x0f, 0xbf, modrm])
      (movsxR32R16Effect p (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hc rfl
  refine ⟨_, movsx_r32_r16_rex_step s h rex modrm hrex hmod hc.bytesAt
    (hc.low (by simp) (by simp)), ReadyToStep.afterStep_writeResult h 4 _ _ _,
    ⟨afterStep_writeResult_rip h 4 _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s 4 _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self32, Operand.read_afterFetches, Operand.read_beforeFetch]

theorem readGPR8_bh_run {σ : Type} (s : X86.State σ) (hmode : In64BitMode s) :
    (Read_GPR8 7 false).run s = (.ok (s.GPR[3].extractLsb' 8 8), s) := by
  unfold Read_GPR8
  rw [specM_bind_run _ _ hmode]
  rfl

theorem movzx32_operation (v : BitVec 8) :
    X86.Instructions.Operations.MOVZX 8 32 v = .ok (v.setWidth 32) :=
  movzx_operation_except 32 (.inr rfl) v

theorem movzx_r32_r8_form [Bindings] (s : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (reg rm : BitVec 3) (v : BitVec 8)
    (hmode : In64BitMode s) (hsize : ctx.operand_size = 32)
    (hlock : ctx.lock_prefix_present = false)
    (hread : (Read_GPR8 (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (ctx.rex_prefix_present || ctx.rex2_prefix_present || ctx.vex_prefix_present ||
        ctx.evex_prefix_present)).run s = (.ok v, s)) :
    (X86.Instructions.MOVZX_GPRv_GPR8 ip ctx reg rm).run s =
      (.ok (), writeResult s (.reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg) : Operand 32)
        (v.setWidth 32) ip) := by
  have hcontext : {ctx with operand_size := 32, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.MOVZX_GPRv_GPR8
  simp only [movzx32_operation, writeResult, Operand.write_reg32]
  spec_run [
    Read_GPR8 => hread,
    Write_GPR => writeGPR32_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

theorem selectLegacy1OpcodeB6_run_of_register (context : Instruction_Context) (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_B6 context true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_1_Opcode_B6, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

theorem decodeLegacy1OpcodeB6_run_of_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_B6 ip context).run s =
      (X86.Instructions.MOVZX_GPRv_GPR8 (BitVec.add ip 2#64) context
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_B6
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  refine (specM_bind_run _ _ hfetch).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 7 6) _ (s := t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 5 3) _ (s := t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 2 0) _ (s := t) rfl).trans ?_
  refine (decoderSelect_run t (fun mode a b c d e f =>
    Select_Legacy_1_Opcode_B6 context mode a b c d e f modrm) _ 1 hmode hf
    (fun a b c d e f => selectLegacy1OpcodeB6_run_of_register context a b c d e f modrm hmod)).trans ?_
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 2)) _ (s := t) rfl).trans ?_
  exact specM_bind_pure_unit_run _ t

theorem decodeLegacy1_run_of_B6_register [Bindings] (s : RamState) (h : ReadyToStep s)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (bytes : List UInt8) (k : Nat) (hk : k + 1 < 15)
    (hop : bytes[k]? = some 0xB6) (hm : bytes[k + 1]? = some modrm)
    (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32) :
    (Decode_Legacy_1 (BitVec.add s.RIP (BitVec.ofNat 64 k)) ctx).run
        (afterFetches (beforeFetch s) (k + 1)) =
      some ((X86.Instructions.MOVZX_GPRv_GPR8 (BitVec.add s.RIP (BitVec.ofNat 64 (k + 2))) ctx
        (modrmReg modrm) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) (k + 3))) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP bytes := hcode
  have hlen : k + 1 < bytes.length := by
    rcases Nat.lt_or_ge (k + 1) bytes.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hm; cases hm
  have f1 : (Mem_Fetch (BitVec.add s.RIP (BitVec.ofNat 64 k)) 8).run
      (afterFetches (beforeFetch s) (k + 1)) = (.ok 0xB6, afterFetches (beforeFetch s) (k + 2)) := by
    have := memFetch_run_of_bytesAt (beforeFetch s) (k + 1) hf hc hlow k (by omega) (by omega)
    rw [show bytes[k] = 0xB6 from
      Option.some.inj ((List.getElem?_eq_getElem _).symm.trans hop)] at this
    exact this
  have f2 : (Mem_Fetch (BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 k)) 1#64) 8).run
      (afterFetches (beforeFetch s) (k + 2)) =
        (.ok modrm.toBitVec, afterFetches (beforeFetch s) (k + 3)) := by
    have := memFetch_run_of_bytesAt (beforeFetch s) (k + 2) hf hc hlow (k + 1) hlen hk
    rw [show bytes[k + 1] = modrm from
      Option.some.inj ((List.getElem?_eq_getElem _).symm.trans hm)] at this
    rw [show BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 k)) 1#64 =
      BitVec.add s.RIP (BitVec.ofNat 64 (k + 1)) from add_ofNat_add s.RIP k 1]
    exact this
  have hmode (j : Nat) : In64BitMode (afterFetches (beforeFetch s) j) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) (k + 3)) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [decodeLegacy1_run_of_opcodeB6 _ _ _ _ hrex2 (hmode _) f1,
    decodeLegacy1OpcodeB6_run_of_register _ _ _ _ _ hmod (hmode _) hfeatures f2,
    show BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 k)) 2#64 =
      BitVec.add s.RIP (BitVec.ofNat 64 (k + 2)) from add_ofNat_add s.RIP k 2]
  rfl

theorem movzx_ebx_bh_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hcode : BytesAt s s.RIP [0x0f, 0xb6, 0xdf])
    (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    X86.Machine.step s = some (.next (afterStep s 3 fun t =>
      writeResult t (.reg 3 : Operand 32) ((t.GPR[3].extractLsb' 8 8).setWidth 32)
        (BitVec.add s.RIP 3#64))) := by
  have hd := decodeLegacy1_run_of_B6_register s h (legacyContext s.DS) rfl
    0xdf (by decide) [0x0f, 0xb6, 0xdf] 1 (by decide) (by simp) (by simp) hcode hlow
  have hm : In64BitMode (afterFetches (beforeFetch s) 4) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  change (Decode_Legacy_1 (BitVec.add s.RIP 1#64) (legacyContext s.DS)).run
    (afterFetches (beforeFetch s) 2) = some ((X86.Instructions.MOVZX_GPRv_GPR8
    (BitVec.add s.RIP 3#64) (legacyContext s.DS) 3 7).run (afterFetches (beforeFetch s) 4)) at hd
  have hf := movzx_r32_r8_form (afterFetches (beforeFetch s) 4) (BitVec.add s.RIP 3#64)
    (legacyContext s.DS) 3 7 ((afterFetches (beforeFetch s) 4).GPR[3].extractLsb' 8 8)
    hm rfl rfl (readGPR8_bh_run _ hm)
  rw [hf] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · first | exact h.ready.repeatClear | (simp only [writeOutputs, Operand.write_repeat]; exact h.ready.repeatClear)
  exact step_none_legacy1 s _ h 0xb6 [0xdf]
    ⟨by decide, by decide⟩ hcode hlow hd (hm.of_cs_lma_eq rfl rfl)

def movzxEbxBhEffect (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p + 3
    writes := [⟨(Operand.reg 3 : Operand 64), (s.GPR[3].extractLsb' 8 8).setWidth 64⟩] }

theorem movzx_ebx_bh_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x0f, 0xb6, 0xdf])
      (movzxEbxBhEffect p) := by
  rintro s h hc rfl
  refine ⟨_, movzx_ebx_bh_step s h hc.bytesAt (hc.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeResult h 3 _ _ _,
    ⟨afterStep_writeResult_rip h 3 _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s 3 _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep, Operand.read_writeResult_self32]
  exact BitVec.setWidth_setWidth (by decide)

end Base16ct.Proofs.Base16ctUpperDecodeCorrect.Instructions
