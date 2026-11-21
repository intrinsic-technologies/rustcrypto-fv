import X86Proofs.Core.Shift
import X86Proofs.Program.Effect
import X86Proofs.Step.Escape
import X86Proofs.Program.ReadWrite.WriteResult

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Hash.Finalize.Length.Shld

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

def result (x y : BitVec 64) : BitVec 64 := (x ++ y).extractLsb' 54 64

def flags (x y : BitVec 64) (of af : Bool) : StatusFlags :=
  { CF := x.getLsbD 54, PF := evenParity ((result x y).extractLsb' 0 8), AF := af,
    ZF := result x y == 0, SF := (result x y).msb, OF := of }

theorem operation {σ : Type} (s : X86.State σ) (x y : BitVec 64) :
    (X86.Instructions.Operations.SHLD 64 x y 10).run s =
      (.ok (result x y), setFlags { s with oracle := oracleSkip s.oracle 2 }
        (flags x y (oracleBit s.oracle) (oracleBit (oracleSkip s.oracle 1)))) := by
  have concat : BitVec.ofNat 128 (x.toNat <<< 64 + y.toNat) = x ++ y := by
    rw [Nat.shiftLeft_add_eq_or_of_lt y.isLt]
    simpa only [BitVec.setWidth_eq, BitVec.toNat_append] using BitVec.ofNat_toNat 128 (x ++ y)
  unfold X86.Instructions.Operations.SHLD
  simp only [isParityEven8_run]
  repeat spec_bind_rfl
  simp only [Int.reduceAdd, Int.reduceToNat, concat]
  rw [setFlags_eq_of_store]
  · rfl
  · simp only [flags, result]
    rflags_ext


theorem decode [Bindings] (s u : RamState) (ip : BitVec 64) (context : Instruction_Context)
    (hrex2 : context.rex2_prefix_present = false) (hmode : In64BitMode u)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xa4, u)) :
    (Decode_Legacy_1 ip context).run s = some ((Decode_Legacy_1_Opcode_A4 ip context).run u) := by
  unfold Decode_Legacy_1
  rw [ite_eq_right (fun h => Bool.false_ne_true (hrex2.symm.trans h))]
  rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
  repeat erw [decodeLegacy0_modeGuard_run _ _ hmode]
  repeat erw [decodeLegacy1_modeGuard_run _ _ _ _ hmode]
  rfl

theorem select_register (context : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_A4 context true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_1_Opcode_A4, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

theorem decode_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_A4 ip context).run s =
      (X86.Instructions.SHLD_GPRv_GPRv_IMMb (BitVec.add ip 2#64) context
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_A4
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => select_register context a b c d e f modrm hmod)

theorem form [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (reg rm : BitVec 3)
    (hmode : In64BitMode s) (hsize : ctx.operand_size = 64)
    (hlock : ctx.lock_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok 10, t)) (htmode : In64BitMode t) :
    (X86.Instructions.SHLD_GPRv_GPRv_IMMb ip ctx reg rm).run s =
      let dst : Operand 64 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      let src : Operand 64 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (.ok (), writeOutputs t dst
        (result (dst.read s) (src.read s),
          flags (dst.read s) (src.read s) (oracleBit t.oracle) (oracleBit (oracleSkip t.oracle 1)))
        2 (BitVec.add ip 1#64)) := by
  have hcontext : {ctx with operand_size := 64, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.SHLD_GPRv_GPRv_IMMb
  simp only [Operand.read_reg64, writeOutputs, Operand.write_reg64]
  spec_run [Read_GPR => readGPR64_run _ _ hmode, Mem_Fetch => hfetch,
    X86.Instructions.Operations.SHLD => operation _ _ _,
    Write_GPR => writeGPR64_run _ _ _ (htmode.of_cs_lma_eq rfl rfl)]

theorem step [Bindings] (s : RamState) (h : ReadyToStep s) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP [rex, 0x0f, 0xa4, modrm, 10])
    (hlow : s.RIP.toNat + 5 ≤ 2^32) :
    let dst : Operand 64 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    let src : Operand 64 := .reg (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
    X86.Machine.step s = some (.next (afterStep s 5 fun t =>
      writeOutputs t dst
        (result (dst.read t) (src.read t),
          flags (dst.read t) (src.read t) (oracleBit t.oracle) (oracleBit (oracleSkip t.oracle 1)))
        2 (BitVec.add s.RIP 5#64))) := by
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [rex, 0x0f, 0xa4, modrm, 10] := hcode
  have f1 := memFetch_run_of_bytesAt (beforeFetch s) 3 h.fetchReady hc hlow 2
    (by simp) (by decide)
  have f2 : (Mem_Fetch (BitVec.add (BitVec.add s.RIP 2#64) 1#64) 8).run
      (afterFetches (beforeFetch s) 4) =
        (.ok modrm.toBitVec, afterFetches (beforeFetch s) 5) := by
    rw [show BitVec.add (BitVec.add s.RIP 2#64) 1#64 = BitVec.add s.RIP 3#64
      from BitVec.add_assoc s.RIP 2#64 1#64]
    exact memFetch_run_of_bytesAt (beforeFetch s) 4 h.fetchReady hc hlow 3
      (by simp) (by decide)
  have f3 : (Mem_Fetch (BitVec.add s.RIP 4#64) 8).run
      (afterFetches (beforeFetch s) 5) =
        (.ok 10, afterFetches (beforeFetch s) 6) :=
    memFetch_run_of_bytesAt (beforeFetch s) 5 h.fetchReady hc hlow 4 (by simp) (by decide)
  have hmode (j : Nat) : In64BitMode (afterFetches (beforeFetch s) j) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf : DecoderFeatures (afterFetches (beforeFetch s) 5) :=
    h.features.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hd := decode _ _ (BitVec.add s.RIP 2#64)
    (rexContext s.DS rex.toBitVec) rfl (hmode 4) f1
  rw [decode_register _ _ _ _ _ hmod (hmode 5) hf f2,
    show BitVec.add (BitVec.add s.RIP 2#64) 2#64 = BitVec.add s.RIP 4#64
      from BitVec.add_assoc s.RIP 2#64 2#64,
    form _ _ _ _ _ _ (hmode 5) (hrex.operand_size s.DS) rfl f3 (hmode 6),
    show BitVec.add (BitVec.add s.RIP 4#64) 1#64 = BitVec.add s.RIP 5#64
      from BitVec.add_assoc s.RIP 4#64 1#64] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy1 s _ h rex 0xa4 [modrm, 10] hrex.rexPrefix
    (by decide) hcode hlow hd ((hmode 6).of_cs_lma_eq rfl rfl)

def effect (p : BitVec 64) (dst src : BitVec 5) (s : RamState) : Effect :=
  { rip := p + 5
    writes := [⟨(Operand.reg dst : Operand 64),
      result ((Operand.reg dst : Operand 64).read s) ((Operand.reg src : Operand 64).read s)⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

theorem effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0x0f, 0xa4, modrm, 10])
      (effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, step s h rex modrm hrex hmod hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeOutputs h 5 _ _ _ _,
    ⟨afterStep_writeOutputs_rip h 5 _ _ _ _, ?_, ?_,
      AgreesExcept.afterStep_writeOutputs s 5 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, Operand.read_afterFetches, Operand.read_beforeFetch]
  · simp [effect, Effect.FlagsHold, StatusFlagsOutcome.Allows, FlagAllows]

end Sha2.Proofs.Wrapper512.Hash.Finalize.Length.Shld
