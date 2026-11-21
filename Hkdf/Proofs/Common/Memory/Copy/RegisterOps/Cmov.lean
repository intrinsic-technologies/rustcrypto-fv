import X86Proofs.Step.Escape
import X86Proofs.Program.Effect
import X86Proofs.Program.ReadWrite.WriteResult
import X86Proofs.Instructions.Branch.Cond

open X86Proofs

namespace Hkdf.Proofs.Common.Instructions

open X86 X86.Machine X86.UserProcess X86.Helpers

def cmovbR8RdxValue (s : RamState) : BitVec 64 :=
  if (StatusFlags.ofRFLAGS s.RFLAGS).CF then
    (Operand.reg 2 : Operand 64).read s
  else
    (Operand.reg 8 : Operand 64).read s

def cmovbR8RdxEffect (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p + 4
    writes := [⟨(Operand.reg 8 : Operand 64), cmovbR8RdxValue s⟩] }

theorem decodeLegacy1_run_of_cmovOpcode [Bindings] (s u : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hrex2 : context.rex2_prefix_present = false)
    (hmode : In64BitMode u) (op : UInt8) (hop : op = 0x42 ∨ op = 0x45)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok op.toBitVec, u)) :
    (Decode_Legacy_1 ip context).run s =
      some ((Decode_Legacy_1_Opcode_42 ip context op.toBitVec).run u) := by
  rcases hop with rfl | rfl <;>
    (unfold Decode_Legacy_1
     rw [ite_eq_right (fun h => Bool.false_ne_true (hrex2.symm.trans h))]
     rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
     repeat erw [decodeLegacy0_modeGuard_run _ _ hmode]
     repeat erw [decodeLegacy1_modeGuard_run _ _ _ _ hmode]
     rfl)

theorem selectLegacy1Opcode42_run_of_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_42 context true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_1_Opcode_42, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

theorem decodeLegacy1Opcode42_run_of_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (op modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_42 ip context op).run s =
      (X86.Instructions.CMOVB_GPRv_GPRv (BitVec.add ip 2#64) context
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3) op).run t := by
  unfold Decode_Legacy_1_Opcode_42
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy1Opcode42_run_of_register context a b c d e f modrm hmod)

theorem cmov64_operation (s : RamState) (x y : BitVec 64) (cc : BitVec 4) :
    (X86.Instructions.Operations.CMOVcc 64 x y cc).run s =
      (.ok (if condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) then y else x), s) := by
  unfold X86.Instructions.Operations.CMOVcc
  spec_run [Condition_Holds => conditionHolds_run s cc]
  change ((if condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) then pure y else pure x) :
    X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run s = _
  split <;> rfl

theorem cmov_r64_r64_form [Bindings] (s : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (reg rm : BitVec 3) (opcode : BitVec 8)
    (hmode : In64BitMode s) (hsize : ctx.operand_size = 64)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.CMOVB_GPRv_GPRv ip ctx reg rm opcode).run s =
      let dst : Operand 64 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let src : Operand 64 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeResult s dst
        (if condHolds (opcode.extractLsb' 0 4) (StatusFlags.ofRFLAGS s.RFLAGS)
          then src.read s else dst.read s) ip) := by
  have hcontext : {ctx with operand_size := 64, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.CMOVB_GPRv_GPRv
  simp only [writeResult, Operand.read_reg64, Operand.write_reg64]
  spec_run [
    Read_GPR => readGPR64_run _ _ hmode,
    X86.Instructions.Operations.CMOVcc => cmov64_operation _ _ _ _,
    Write_GPR => writeGPR64_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

def cmovR64R64Value (cc : BitVec 4) (dst src : BitVec 5) (s : RamState) : BitVec 64 :=
  if condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) then
    (Operand.reg src : Operand 64).read s
  else
    (Operand.reg dst : Operand 64).read s

def cmovR64R64Effect (p : BitVec 64) (cc : BitVec 4) (dst src : BitVec 5)
    (s : RamState) : Effect :=
  { rip := p + 4
    writes := [⟨(Operand.reg dst : Operand 64), cmovR64R64Value cc dst src s⟩] }

theorem cmov_r64_r64_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (rex op modrm : UInt8) (hrex : RexWPrefix rex.toBitVec)
    (hop : op = 0x42 ∨ op = 0x45) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP [rex, 0x0f, op, modrm])
    (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    let dst := gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)
    let src := gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)
    X86.Machine.step s = some (.next (afterStep s 4 fun t =>
      writeResult t (.reg dst)
        (cmovR64R64Value (op.toBitVec.extractLsb' 0 4) dst src t) (BitVec.add s.RIP 4#64))) := by
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [rex, 0x0f, op, modrm] := hcode
  have f1 := memFetch_run_of_bytesAt (beforeFetch s) 3 h.fetchReady hc hlow 2
    (by simp) (by decide)
  have f2 : (Mem_Fetch (BitVec.add (BitVec.add s.RIP 2#64) 1#64) 8).run
      (afterFetches (beforeFetch s) 4) =
        (.ok modrm.toBitVec, afterFetches (beforeFetch s) 5) := by
    rw [show BitVec.add (BitVec.add s.RIP 2#64) 1#64 = BitVec.add s.RIP 3#64
      from BitVec.add_assoc s.RIP 2#64 1#64]
    exact memFetch_run_of_bytesAt (beforeFetch s) 4 h.fetchReady hc hlow 3
      (by simp) (by decide)
  have hmode (j : Nat) : In64BitMode (afterFetches (beforeFetch s) j) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf : DecoderFeatures (afterFetches (beforeFetch s) 5) :=
    h.features.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hd := decodeLegacy1_run_of_cmovOpcode _ _ (BitVec.add s.RIP 2#64)
    (rexContext s.DS rex.toBitVec) rfl (hmode 4) op hop f1
  rw [decodeLegacy1Opcode42_run_of_register _ _ _ _ _ _ hmod (hmode 5) hf f2,
    cmov_r64_r64_form _ _ _ _ _ _ (hmode 5) (hrex.operand_size s.DS) rfl,
    show BitVec.add (BitVec.add s.RIP 2#64) 2#64 = BitVec.add s.RIP 4#64
      from BitVec.add_assoc s.RIP 2#64 2#64] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy1 s _ h rex op [modrm] hrex.rexPrefix
    (by rcases hop with rfl | rfl <;> decide) hcode hlow hd
    ((hmode 5).of_cs_lma_eq rfl rfl)

theorem cmov_r64_r64_effect_step [Bindings] (p : BitVec 64) (rex op modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hop : op = 0x42 ∨ op = 0x45)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0x0f, op, modrm])
      (cmovR64R64Effect p (op.toBitVec.extractLsb' 0 4)
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, cmov_r64_r64_step s h rex op modrm hrex hop hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), ReadyToStep.afterStep_writeResult h 4 _ _ _,
    ⟨afterStep_writeResult_rip h 4 _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s 4 _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep, Operand.read_writeResult_self]
  simp only [cmovR64R64Value, Operand.read_afterFetches, Operand.read_beforeFetch]
  rfl

theorem cmovb_r8_rdx_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x4c, 0x0f, 0x42, 0xc2])
      (cmovbR8RdxEffect p) :=
  cmov_r64_r64_effect_step p 0x4c 0x42 0xc2 (by simp [RexWPrefix])
    (Or.inl rfl) rfl

def cmovneR9R8Effect (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p + 4
    writes := [⟨(Operand.reg 9 : Operand 64),
      if !(StatusFlags.ofRFLAGS s.RFLAGS).ZF then
        (Operand.reg 8 : Operand 64).read s else (Operand.reg 9 : Operand 64).read s⟩] }

theorem cmovne_r9_r8_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x4d, 0x0f, 0x45, 0xc8])
      (cmovneR9R8Effect p) :=
  cmov_r64_r64_effect_step p 0x4d 0x45 0xc8 (by simp [RexWPrefix])
    (Or.inr rfl) rfl

end Hkdf.Proofs.Common.Instructions
