import X86Proofs

namespace Base16ct.Proofs.Base16ctUpperDecodeCorrect.Instructions

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem cmovne_operation {σ : Type} (s : X86.State σ) (x y : BitVec 64) :
    (X86.Instructions.Operations.CMOVcc 64 x y 5).run s =
      (.ok (if (StatusFlags.ofRFLAGS s.RFLAGS).ZF then x else y), s) := by
  unfold X86.Instructions.Operations.CMOVcc
  spec_bind_rfl
  rw [specM_bind_run _ _ (conditionHolds_run s 5)]
  cases hz : (StatusFlags.ofRFLAGS s.RFLAGS).ZF <;> simp [condHolds, hz]

theorem cmovne_r64_r64_form {σ : Type} [PhysicalMemory σ] (s : X86.State σ)
    (ip : BitVec 64) (ctx : Instruction_Context) (reg rm : BitVec 3)
    (hmode : In64BitMode s) (hsize : ctx.operand_size = 64)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.CMOVNZ_GPRv_GPRv ip ctx reg rm 0x45).run s =
      let dst : Operand 64 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let src : Operand 64 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeResult s dst
        (if (StatusFlags.ofRFLAGS s.RFLAGS).ZF then dst.read s else src.read s) ip) := by
  have hcontext : {ctx with operand_size := 64, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.CMOVNZ_GPRv_GPRv
  simp only [Operand.read_reg64, writeResult, Operand.write_reg64]
  spec_run [
    Read_GPR => readGPR64_run _ _ hmode,
    X86.Instructions.Operations.CMOVcc => cmovne_operation _ _ _,
    Write_GPR => writeGPR64_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

theorem decodeLegacy1_run_of_opcode45 [Bindings] (s u : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hrex2 : context.rex2_prefix_present = false)
    (hmode : In64BitMode u) (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x45, u)) :
    (Decode_Legacy_1 ip context).run s =
      some ((Decode_Legacy_1_Opcode_45 ip context 0x45).run u) := by
  unfold Decode_Legacy_1
  rw [ite_eq_right (fun h => Bool.false_ne_true (hrex2.symm.trans h))]
  rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
  repeat erw [decodeLegacy0_modeGuard_run _ _ hmode]
  repeat erw [decodeLegacy1_modeGuard_run _ _ _ _ hmode]
  rfl

theorem selectLegacy1Opcode45_run_of_register (context : Instruction_Context) (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_45 context true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_1_Opcode_45, x86_runtime, X86.Runtime.CheckedSlice.read, bind, pure,
    Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

theorem decodeLegacy1Opcode45_run_of_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_45 ip context 0x45).run s =
      (X86.Instructions.CMOVNZ_GPRv_GPRv (BitVec.add ip 2#64) context
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) 0x45).run t := by
  unfold Decode_Legacy_1_Opcode_45
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  refine (specM_bind_run _ _ hfetch).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 7 6) _ (s := t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 5 3) _ (s := t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 2 0) _ (s := t) rfl).trans ?_
  refine (decoderSelect_run t (fun mode a b c d e f =>
    Select_Legacy_1_Opcode_45 context mode a b c d e f modrm) _ 1 hmode hf
    (fun a b c d e f => selectLegacy1Opcode45_run_of_register context a b c d e f modrm hmod)).trans ?_
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 2)) _ (s := t) rfl).trans ?_
  exact specM_bind_pure_unit_run _ t

theorem decodeLegacy1_run_of_45_register [Bindings] (s : RamState) (h : ReadyToStep s)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (bytes : List UInt8) (k : Nat) (hk : k + 1 < 15)
    (hop : bytes[k]? = some 0x45) (hm : bytes[k + 1]? = some modrm)
    (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32) :
    (Decode_Legacy_1 (BitVec.add s.RIP (BitVec.ofNat 64 k)) ctx).run
        (afterFetches (beforeFetch s) (k + 1)) =
      some ((X86.Instructions.CMOVNZ_GPRv_GPRv (BitVec.add s.RIP (BitVec.ofNat 64 (k + 2))) ctx
        (modrmReg modrm) (modrmRm modrm) 0x45).run
          (afterFetches (beforeFetch s) (k + 3))) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP bytes := hcode
  have hlen : k + 1 < bytes.length := by
    rcases Nat.lt_or_ge (k + 1) bytes.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hm; cases hm
  have f1 : (Mem_Fetch (BitVec.add s.RIP (BitVec.ofNat 64 k)) 8).run
      (afterFetches (beforeFetch s) (k + 1)) = (.ok 0x45, afterFetches (beforeFetch s) (k + 2)) := by
    have := memFetch_run_of_bytesAt (beforeFetch s) (k + 1) hf hc hlow k (by omega) (by omega)
    rw [show bytes[k] = 0x45 from
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
  rw [decodeLegacy1_run_of_opcode45 _ _ _ _ hrex2 (hmode _) f1,
    decodeLegacy1Opcode45_run_of_register _ _ _ _ _ hmod (hmode _) hfeatures f2,
    show BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 k)) 2#64 =
      BitVec.add s.RIP (BitVec.ofNat 64 (k + 2)) from add_ofNat_add s.RIP k 2]
  rfl

theorem cmovne_r64_r64_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (rex modrm : UInt8) (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP [rex, 0x0f, 0x45, modrm])
    (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    let dst : Operand 64 := .reg (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
    let src : Operand 64 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s 4 fun t =>
      writeResult t dst
        (if (StatusFlags.ofRFLAGS t.RFLAGS).ZF then dst.read t else src.read t)
        (BitVec.add s.RIP 4#64))) := by
  have hd := decodeLegacy1_run_of_45_register s h (rexContext s.DS rex.toBitVec) rfl
    modrm hmod [rex, 0x0f, 0x45, modrm] 2 (by decide) (by simp) (by simp) hcode hlow
  have hm : In64BitMode (afterFetches (beforeFetch s) 5) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [cmovne_r64_r64_form _ _ _ _ _ hm (hrex.operand_size s.DS) rfl] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · first | exact h.ready.repeatClear | (simp only [writeOutputs, Operand.write_repeat]; exact h.ready.repeatClear)
  exact step_rex_legacy1 s _ h rex 0x45 [modrm] hrex.rexPrefix
    ⟨by decide, by decide⟩ hcode hlow hd (hm.of_cs_lma_eq rfl rfl)

def cmovneR64R64Effect (p : BitVec 64) (dst src : BitVec 5) (s : RamState) : Effect :=
  { rip := p + 4
    writes := [⟨(Operand.reg dst : Operand 64),
      if (StatusFlags.ofRFLAGS s.RFLAGS).ZF then
        (Operand.reg dst : Operand 64).read s else (Operand.reg src : Operand 64).read s⟩] }

theorem cmovne_r64_r64_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0x0f, 0x45, modrm])
      (cmovneR64R64Effect p (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hc rfl
  refine ⟨_, cmovne_r64_r64_step s h rex modrm hrex hmod hc.bytesAt
    (hc.low (by simp) (by simp)), ReadyToStep.afterStep_writeResult h 4 _ _ _,
    ⟨afterStep_writeResult_rip h 4 _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s 4 _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self, Operand.read_afterFetches, Operand.read_beforeFetch]
  rfl

end Base16ct.Proofs.Base16ctUpperDecodeCorrect.Instructions
