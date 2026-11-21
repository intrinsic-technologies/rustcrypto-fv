import X86Proofs.Core.Operand
import X86Proofs.Core.Shift
import X86Proofs.Program.Effect
import X86Proofs.Step.Escape
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Movs.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

namespace Md5.Proofs.MemoryRoutines.Memset.Register

open X86 X86.Helpers X86Proofs X86.Machine X86.UserProcess

def imulOverflow (a b : BitVec 64) : Bool :=
  decide ((a * b).toInt ≠ a.toInt * b.toInt)

def imulSpec (o : X86.Runtime.Oracle) (a b : BitVec 64) : BitVec 64 × StatusFlags :=
  (a * b, ⟨imulOverflow a b, oracleBit (oracleSkip o 3), oracleBit (oracleSkip o 2),
    oracleBit (oracleSkip o 1), oracleBit o, imulOverflow a b⟩)

def imulFlags (a b : BitVec 64) : StatusFlagsOutcome :=
  ⟨some (imulOverflow a b), none, none, none, none, some (imulOverflow a b)⟩

theorem imulFlags_allows (o : X86.Runtime.Oracle) (a b : BitVec 64) :
    (imulFlags a b).Allows (imulSpec o a b).2 :=
  ⟨rfl, trivial, trivial, trivial, trivial, rfl⟩

theorem imul64_operation {σ : Type} (s : X86.State σ) (a b : BitVec 64) :
    (X86.Instructions.Operations.IMUL_SINGLE 64 a b).run s =
      (.ok (a * b), setFlags {s with oracle := oracleSkip s.oracle 4} (imulSpec s.oracle a b).2) := by
  unfold X86.Instructions.Operations.IMUL_SINGLE
  repeat spec_bind_rfl
  simp only [signed_eq, Int.reduceToNat, Int.toNat_zero, Int.pow_zero, Int.ediv_one,
    BitVec.ofInt_mul, BitVec.ofInt_toInt]
  rw [setFlags_eq_of_store]
  · rfl
  · unfold imulSpec imulOverflow
    rflags_ext

theorem imul_r64_r64_form {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ)
    (ip : BitVec 64) (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (hsize : ctx.operand_size = 64) (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.IMUL_GPRv_GPRv ip ctx reg rm).run s =
      let dst : Operand 64 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let src : Operand 64 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeOutputs s dst (imulSpec s.oracle (dst.read s) (src.read s)) 4 ip) := by
  have hcontext : {ctx with operand_size := 64, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.IMUL_GPRv_GPRv
  simp only [Operand.read_reg64, writeOutputs, Operand.write_reg64]
  spec_run [
    Read_GPR => readGPR64_run _ _ hmode,
    X86.Instructions.Operations.IMUL_SINGLE => imul64_operation _ _ _,
    Write_GPR => writeGPR64_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

theorem selectLegacy1OpcodeAF_run_of_register (ctx : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_AF ctx true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_1_Opcode_AF, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

theorem decodeLegacy1OpcodeAF_run_of_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_AF ip ctx).run s =
      (X86.Instructions.IMUL_GPRv_GPRv (BitVec.add ip 2#64) ctx
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_AF
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  refine (specM_bind_run _ _ hfetch).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 7 6) _ (s := t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 5 3) _ (s := t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 2 0) _ (s := t) rfl).trans ?_
  refine (decoderSelect_run t (fun mode a b c d e f ↦
    Select_Legacy_1_Opcode_AF ctx mode a b c d e f modrm) _ 1 hmode hf
    (fun a b c d e f ↦ selectLegacy1OpcodeAF_run_of_register ctx a b c d e f modrm hmod)).trans ?_
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 2)) _ (s := t) rfl).trans ?_
  exact specM_bind_pure_unit_run _ t

theorem decodeLegacy1_run_of_opcodeAF [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (hmode : In64BitMode t)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xAF, t)) :
    (Decode_Legacy_1 ip ctx).run s =
      some ((Decode_Legacy_1_Opcode_AF ip ctx).run t) := by
  unfold Decode_Legacy_1
  rw [ite_eq_right (fun h ↦ Bool.false_ne_true (hrex2.symm.trans h))]
  rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
  repeat erw [decodeLegacy0_modeGuard_run _ _ hmode]
  repeat erw [decodeLegacy1_modeGuard_run _ _ _ _ hmode]
  rfl

theorem decodeLegacy1_run_of_rex_AF_register [Bindings] (s : RamState) (h : ReadyToStep s)
    (rex modrm : UInt8) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP [rex, 0x0F, 0xAF, modrm]) (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    (Decode_Legacy_1 (BitVec.add s.RIP 2#64) (rexContext s.DS rex.toBitVec)).run
        (afterFetches (beforeFetch s) 3) =
      some ((X86.Instructions.IMUL_GPRv_GPRv (BitVec.add s.RIP 4#64)
        (rexContext s.DS rex.toBitVec) (modrmReg modrm) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) 5)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [rex, 0x0F, 0xAF, modrm] := hcode
  have f2 : (Mem_Fetch (BitVec.add s.RIP 2#64) 8).run (afterFetches (beforeFetch s) 3) =
      (.ok 0xAF, afterFetches (beforeFetch s) 4) :=
    memFetch_run_of_bytesAt (beforeFetch s) 3 hf hc hlow 2 (by simp) (by decide)
  have f3 : (Mem_Fetch (BitVec.add (BitVec.add s.RIP 2#64) 1#64) 8).run
      (afterFetches (beforeFetch s) 4) = (.ok modrm.toBitVec, afterFetches (beforeFetch s) 5) := by
    rw [show BitVec.add (BitVec.add s.RIP 2#64) 1#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc s.RIP 2#64 1#64]
    exact memFetch_run_of_bytesAt (beforeFetch s) 4 hf hc hlow 3 (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 5) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [decodeLegacy1_run_of_opcodeAF _ _ _ _ rfl (hmode 4) f2,
    decodeLegacy1OpcodeAF_run_of_register _ _ _ _ _ hmod (hmode 5) hfeatures f3,
    show BitVec.add (BitVec.add s.RIP 2#64) 2#64 = BitVec.add s.RIP 4#64 from
      BitVec.add_assoc s.RIP 2#64 2#64]
  rfl

theorem imul_rax_rcx_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hcode : BytesAt s s.RIP [0x48, 0x0F, 0xAF, 0xC1])
    (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    X86.Machine.step s = some (.next (afterStep s 4 fun t ↦
      writeOutputs t (.reg 0 : Operand 64)
        (imulSpec t.oracle ((Operand.reg 0 : Operand 64).read t)
          ((Operand.reg 1 : Operand 64).read t)) 4 (BitVec.add s.RIP 4#64))) := by
  have hdecode := decodeLegacy1_run_of_rex_AF_register s h 0x48 0xC1 (by decide) hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 5) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [imul_r64_r64_form _ _ _ _ _ hmode rfl rfl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy1 s _ h 0x48 0xAF [0xC1]
    (by unfold RexPrefix; decide) ⟨by decide, by decide⟩ hcode hlow hdecode
    (hmode.of_cs_lma_eq rfl rfl)

def imulRaxRcxEffect (p : BitVec 64) (s : RamState) : Effect :=
  let a := (Operand.reg 0 : Operand 64).read s
  let b := (Operand.reg 1 : Operand 64).read s
  { rip := p + 4
    writes := [⟨(Operand.reg 0 : Operand 64), a * b⟩]
    flags := some (imulFlags a b) }

theorem imulRaxRcxEffect_components (p : BitVec 64) (s : RamState) :
    (imulRaxRcxEffect p s).components = [.reg 0, .flags, .rip] := rfl

theorem imulRaxRcxEffect_avoids (p : BitVec 64) (s : RamState) (code : CodeMap) :
    (imulRaxRcxEffect p s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [imulRaxRcxEffect_components, Component.Covers]) code

theorem imul_rax_rcx_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p [0x48, 0x0F, 0xAF, 0xC1])
      (imulRaxRcxEffect p) := by
  rintro s h hcode rfl
  refine ⟨_, imul_rax_rcx_step s h hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeOutputs h 4 _ _ 4 _,
    ⟨afterStep_writeOutputs_rip h 4 _ _ 4 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ 4 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, imulSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact imulFlags_allows _ _ _

attribute [x86_compose] imulRaxRcxEffect imulFlags imulOverflow

@[x86_local] theorem imulRaxRcxEffect_local (p : BitVec 64) :
    Effect.Local (imulRaxRcxEffect p) := by
  refine ⟨fun _ _ _ ↦ rfl, fun t t' h ↦ ?_, fun _ _ _ ↦ (show true = true from rfl),
    fun t t' h i _ ↦ ?_, fun _ ↦ ?_⟩
  · simp only [imulRaxRcxEffect, h.read_reg]
  · change (imulFlags ((Operand.reg 0 : Operand 64).read t)
      ((Operand.reg 1 : Operand 64).read t)).get i =
        (imulFlags ((Operand.reg 0 : Operand 64).read t')
          ((Operand.reg 1 : Operand 64).read t')).get i
    rw [h.read (.reg 0 : Operand 64) trivial, h.read (.reg 1 : Operand 64) trivial]
  · simp [imulRaxRcxEffect, Write.Full, Operand.Full]

end Md5.Proofs.MemoryRoutines.Memset.Register
