import P256.Proofs.Common.Memory.Copy.RegisterOps.Cmov

set_option autoImplicit false

open X86Proofs

namespace P256.Proofs.Common.Instructions

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem cmov32_operation (s : RamState) (x y : BitVec 32) (cc : BitVec 4) :
    (X86.Instructions.Operations.CMOVcc 32 x y cc).run s =
      (.ok (if condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) then y else x), s) := by
  unfold X86.Instructions.Operations.CMOVcc
  spec_run [Condition_Holds => conditionHolds_run s cc]
  change ((if condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) then pure y else pure x) :
    X86.Runtime.SpecM X86.Exception RamState (BitVec 32)).run s = _
  split <;> rfl

theorem cmov_r32_r32_form [Bindings] (s : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (reg rm : BitVec 3) (opcode : BitVec 8)
    (hmode : In64BitMode s) (hsize : ctx.operand_size = 32)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.CMOVB_GPRv_GPRv ip ctx reg rm opcode).run s =
      let dst : Operand 32 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let src : Operand 32 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeResult s dst
        (if condHolds (opcode.extractLsb' 0 4) (StatusFlags.ofRFLAGS s.RFLAGS)
          then src.read s else dst.read s) ip) := by
  have hcontext : {ctx with operand_size := 32, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.CMOVB_GPRv_GPRv
  simp only [writeResult, Operand.read_reg32, Operand.write_reg32]
  spec_run [
    Read_GPR => readGPR32_run _ _ hmode,
    X86.Instructions.Operations.CMOVcc => cmov32_operation _ _ _ _,
    Write_GPR => writeGPR32_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

def cmovR32R32Value (cc : BitVec 4) (dst src : BitVec 5) (s : RamState) : BitVec 32 :=
  if condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) then
    (Operand.reg src : Operand 32).read s
  else
    (Operand.reg dst : Operand 32).read s

def cmovR32R32Effect (p : BitVec 64) (cc : BitVec 4) (dst src : BitVec 5)
    (s : RamState) : Effect :=
  { rip := p + 3
    writes := [⟨(Operand.reg dst : Operand 64), (cmovR32R32Value cc dst src s).setWidth 64⟩] }

theorem cmov_r32_r32_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (op modrm : UInt8) (hop : op = 0x42 ∨ op = 0x45) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP [0x0f, op, modrm])
    (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    let dst := gprNumber 0 0 (modrmReg modrm)
    let src := gprNumber 0 0 (modrmRm modrm)
    X86.Machine.step s = some (.next (afterStep s 3 fun t =>
      writeResult t (.reg dst)
        (cmovR32R32Value (op.toBitVec.extractLsb' 0 4) dst src t) (BitVec.add s.RIP 3#64))) := by
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [0x0f, op, modrm] := hcode
  have f1 := memFetch_run_of_bytesAt (beforeFetch s) 2 h.fetchReady hc hlow 1
    (by simp) (by decide)
  have f2 : (Mem_Fetch (BitVec.add (BitVec.add s.RIP 1#64) 1#64) 8).run
      (afterFetches (beforeFetch s) 3) =
        (.ok modrm.toBitVec, afterFetches (beforeFetch s) 4) := by
    rw [show BitVec.add (BitVec.add s.RIP 1#64) 1#64 = BitVec.add s.RIP 2#64
      from BitVec.add_assoc s.RIP 1#64 1#64]
    exact memFetch_run_of_bytesAt (beforeFetch s) 3 h.fetchReady hc hlow 2
      (by simp) (by decide)
  have hmode (j : Nat) : In64BitMode (afterFetches (beforeFetch s) j) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf : DecoderFeatures (afterFetches (beforeFetch s) 4) :=
    h.features.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hd := decodeLegacy1_run_of_cmovOpcode _ _ (BitVec.add s.RIP 1#64)
    (legacyContext s.DS) rfl (hmode 3) op hop f1
  rw [decodeLegacy1Opcode42_run_of_register _ _ _ _ _ _ hmod (hmode 4) hf f2,
    cmov_r32_r32_form _ _ _ _ _ _ (hmode 4) rfl rfl,
    show BitVec.add (BitVec.add s.RIP 1#64) 2#64 = BitVec.add s.RIP 3#64
      from BitVec.add_assoc s.RIP 1#64 2#64] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy1 s _ h op [modrm]
    (by rcases hop with rfl | rfl <;> decide) hcode hlow hd
    ((hmode 4).of_cs_lma_eq rfl rfl)

theorem cmov_r32_r32_effect_step [Bindings] (p : BitVec 64) (op modrm : UInt8)
    (hop : op = 0x42 ∨ op = 0x45) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x0f, op, modrm])
      (cmovR32R32Effect p (op.toBitVec.extractLsb' 0 4)
        (gprNumber 0 0 (modrmReg modrm)) (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, cmov_r32_r32_step s h op modrm hop hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), ReadyToStep.afterStep_writeResult h 3 _ _ _,
    ⟨afterStep_writeResult_rip h 3 _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s 3 _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep, Operand.read_writeResult_self32]
  simp only [cmovR32R32Value, Operand.read_afterFetches, Operand.read_beforeFetch]
  rfl

end P256.Proofs.Common.Instructions
