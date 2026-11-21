import X86Proofs.Step.Escape
import X86Proofs.Step.FetchImm
import P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.Instructions.ShiftCount.Form
import X86Proofs.Program.Effect

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.Instructions.Shrd

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem decodeLegacy1_run_of_shrdOpcode [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrex2 : context.rex2_prefix_present = false) (hmode : In64BitMode t)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xAD, t)) :
    (Decode_Legacy_1 ip context).run s =
      some ((Decode_Legacy_1_Opcode_AD ip context).run t) := by
  unfold Decode_Legacy_1
  rw [ite_eq_right (fun h => Bool.false_ne_true (hrex2.symm.trans h))]
  rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
  repeat erw [decodeLegacy0_modeGuard_run _ _ hmode]
  repeat erw [decodeLegacy1_modeGuard_run _ _ _ _ hmode]
  rfl

theorem selectLegacy1OpcodeAD_run_of_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_AD context true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_1_Opcode_AD, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

theorem decodeLegacy1OpcodeAD_run_of_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_AD ip context).run s =
      (X86.Instructions.SHRD_GPRv_GPRv_CL (BitVec.add ip 2#64) context
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_AD
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy1OpcodeAD_run_of_register context a b c d e f modrm hmod)

theorem decodeLegacy1_run_of_shrd [Bindings] (s : RamState) (h : ReadyToStep s)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (bytes : List UInt8) (k : Nat) (hk : k + 1 < 15)
    (hopbyte : bytes[k]? = some 0xAD) (hm : bytes[k + 1]? = some modrm)
    (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32) :
    (Decode_Legacy_1 (BitVec.add s.RIP (BitVec.ofNat 64 k)) ctx).run
        (afterFetches (beforeFetch s) (k + 1)) =
      some ((X86.Instructions.SHRD_GPRv_GPRv_CL (BitVec.add s.RIP (BitVec.ofNat 64 (k + 2))) ctx
        (modrmReg modrm) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) (k + 3))) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP bytes := hcode
  have hlen : k + 1 < bytes.length := by
    rcases Nat.lt_or_ge (k + 1) bytes.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hm; cases hm
  have f1 : (Mem_Fetch (BitVec.add s.RIP (BitVec.ofNat 64 k)) 8).run
      (afterFetches (beforeFetch s) (k + 1)) =
        (.ok 0xAD, afterFetches (beforeFetch s) (k + 2)) := by
    have := memFetch_run_of_bytesAt (beforeFetch s) (k + 1) hf hc hlow k (by omega) (by omega)
    rw [show bytes[k] = 0xAD from
      Option.some.inj ((List.getElem?_eq_getElem _).symm.trans hopbyte)] at this
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
  rw [decodeLegacy1_run_of_shrdOpcode _ _ _ _ hrex2 (hmode _) f1,
    decodeLegacy1OpcodeAD_run_of_register _ _ _ _ _ hmod (hmode _) hfeatures f2,
    show BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 k)) 2#64 =
      BitVec.add s.RIP (BitVec.ofNat 64 (k + 2)) from add_ofNat_add s.RIP k 2]
  rfl

def shrdOneResult (x y : BitVec 64) : BitVec 64 :=
  (BitVec.ofNat 128 ((y.toNat <<< 64) + x.toNat)).extractLsb' 1 64

def shrdOneSpec (af : Bool) (x y : BitVec 64) : BitVec 64 × StatusFlags :=
  let r := shrdOneResult x y
  (r, { CF := x.getLsbD 0, PF := evenParity (r.extractLsb' 0 8), AF := af, ZF := r == 0, SF := r.msb, OF := x.msb != r.msb })

set_option maxRecDepth 2048 in
theorem shrd_one_operation (s : RamState) (x y : BitVec 64) :
    (X86.Instructions.Operations.SHRD 64 x y 1).run s =
      let (r, flags) := shrdOneSpec (oracleBit s.oracle) x y
      (.ok r, setFlags {s with oracle := oracleSkip s.oracle 1} flags) := by
  unfold X86.Instructions.Operations.SHRD
  simp only [isParityEven8_run]
  repeat spec_bind_rfl
  simp only [shrdOneSpec, shrdOneResult]
  rw [setFlags_eq_of_store]
  · rfl
  · rflags_ext

theorem shrd_r64_r64_cl_one_form [Bindings] (s : RamState)
    (ip : BitVec 64) (ctx : Instruction_Context) (reg rm : BitVec 3)
    (hmode : In64BitMode s) (hcount : (Operand.reg 1 : Operand 8).read s = 1)
    (hsize : ctx.operand_size = 64) (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.SHRD_GPRv_GPRv_CL ip ctx reg rm).run s =
      let dst : Operand 64 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      let src : Operand 64 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (.ok (), writeOutputs s dst (shrdOneSpec (oracleBit s.oracle) (dst.read s) (src.read s))
        1 ip) := by
  have hcontext : {ctx with operand_size := 64, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  have hc : CL.run s = (.ok 1, s) := by
    rw [X86Proofs.cl_run]
    rw [show s.GPR[gprIndex 1].setWidth 8 = 1 from hcount]
  rw [← hcontext]
  unfold X86.Instructions.SHRD_GPRv_GPRv_CL
  simp only [Operand.read_reg64, writeOutputs, Operand.write_reg64]
  spec_run [Read_GPR => readGPR64_run _ _ hmode,
    CL => hc,
    X86.Instructions.Operations.SHRD => shrd_one_operation _ _ _,
    Write_GPR => writeGPR64_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

theorem shrd_r64_r64_cl_one_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (rex modrm : UInt8) (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hcount : (Operand.reg 1 : Operand 8).read s = 1)
    (hcode : BytesAt s s.RIP [rex, 0x0F, 0xAD, modrm])
    (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    let dst : Operand 64 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    let src : Operand 64 := .reg (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
    X86.Machine.step s = some (.next (afterStep s 4 fun t =>
      writeOutputs t dst (shrdOneSpec (oracleBit t.oracle) (dst.read t) (src.read t))
        1 (BitVec.add s.RIP 4#64))) := by
  have hd := decodeLegacy1_run_of_shrd s h (rexContext s.DS rex.toBitVec) rfl
    modrm hmod _ 2 (by decide) rfl rfl hcode hlow
  have hm (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [shrd_r64_r64_cl_one_form _ _ _ _ _ (hm 5) hcount (hrex.operand_size _) rfl] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy1 s _ h rex 0xAD [modrm] hrex.rexPrefix (by decide)
    hcode hlow hd ((hm 5).of_cs_lma_eq rfl rfl)

def shrdOneEffect (p : BitVec 64) (dst src : BitVec 5) (s : RamState) : Effect :=
  { rip := p + 4
    writes := [⟨(Operand.reg dst : Operand 64),
      shrdOneResult ((Operand.reg dst : Operand 64).read s) ((Operand.reg src : Operand 64).read s)⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem shrd_r64_r64_cl_one_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p ∧ (Operand.reg 1 : Operand 8).read s = 1)
      (codeRange p [rex, 0x0f, 0xad, modrm])
      (shrdOneEffect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))) := by
  rintro s h hcode ⟨rfl, hc⟩
  refine ⟨_, shrd_r64_r64_cl_one_step s h rex modrm hrex hmod hc hcode.bytesAt
    (hcode.low (by simp) (by simp)), ReadyToStep.afterStep_writeOutputs h 4 _ _ _ _,
    ⟨afterStep_writeOutputs_rip h 4 _ _ _ _, ?_, ?_,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, shrdOneSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · change True ∧ True ∧ True ∧ True ∧ True ∧ True
    trivial

end P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.Instructions.Shrd
