import P256.Proofs.Common.Memory.Fill.Prologue.ZeroProduct.Movzx
import X86Proofs.Step.AfterStep
import X86Proofs.Step.PrefixScan

set_option autoImplicit false

namespace P256.Proofs.Common.Encoding.Parser.CompressedRoute

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem movzx_r32_r8_low_form [Bindings] (s : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (reg rm : BitVec 3)
    (hmode : In64BitMode s) (hsize : ctx.operand_size = 32)
    (hlock : ctx.lock_prefix_present = false)
    (hsmall : (gprNumber ctx.rex_b4 ctx.rex_b3 rm).toNat < 4) :
    (X86.Instructions.MOVZX_GPRv_GPR8 ip ctx reg rm).run s =
      let dst : Operand 32 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let src : Operand 64 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeResult s dst (movzxSpec 32 ((src.read s).setWidth 8)) ip) := by
  have hcontext :
      {ctx with operand_size := 32, lock_prefix_present := false} =
        ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.MOVZX_GPRv_GPR8
  simp only [writeResult, Operand.read_reg64, Operand.write_reg32]
  spec_run [
    Read_GPR8 => readGPR8_run_of_low _ _ hsmall _ hmode,
    X86.Instructions.Operations.MOVZX => movzx_operation _ 32 (.inr rfl) _,
    Write_GPR => by
      rw [writeGPR32_run {s with Next_IP := ip} _ _ (hmode.of_cs_lma_eq rfl rfl)]
      simp only [movzxSpec, BitVec.ofNat_toNat, gprNumber, Int.reduceToNat, Int.reduceAdd]]

theorem movzx_r32_al_step [Bindings] (s : RamState) (h : ReadyToStep s) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hrm : modrmRm modrm = 0)
    (hcode : BytesAt s s.RIP [0x0f, 0xb6, modrm]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    Machine.step s = some (.next (afterStep s 3 fun t =>
      writeResult t (.reg (gprNumber 0 0 (modrmReg modrm)) : Operand 32)
        (movzxSpec 32 ((Operand.reg 0 : Operand 8).read t)) (BitVec.add s.RIP 3#64))) := by
  have f1 := memFetch_run_of_bytesAt (beforeFetch s) 2 h.fetchReady hcode hlow 1
    (by simp) (by decide)
  have f2 : (Mem_Fetch (BitVec.add (BitVec.add s.RIP 1#64) 1#64) 8).run
      (afterFetches (beforeFetch s) 3) =
        (.ok modrm.toBitVec, afterFetches (beforeFetch s) 4) := by
    rw [show BitVec.add (BitVec.add s.RIP 1#64) 1#64 = BitVec.add s.RIP 2#64
      from BitVec.add_assoc s.RIP 1#64 1#64]
    exact memFetch_run_of_bytesAt (beforeFetch s) 3 h.fetchReady hcode hlow 2
      (by simp) (by decide)
  have hmode (j : Nat) : In64BitMode (afterFetches (beforeFetch s) j) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf : DecoderFeatures (afterFetches (beforeFetch s) 4) :=
    h.features.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hd := decodeLegacy1_run_of_opcodeB6 _ _ (BitVec.add s.RIP 1#64)
    (legacyContext s.DS) rfl (hmode 3) f1
  rw [P256.Proofs.Common.Memory.Fill.decodeLegacy1OpcodeB6_run_of_register _ _ _ _ _ hmod (hmode 4) hf f2] at hd
  change (Decode_Legacy_1 _ _).run _ = some ((X86.Instructions.MOVZX_GPRv_GPR8 _ _
    (modrmReg modrm) (modrmRm modrm)).run _) at hd
  rw [hrm, movzx_r32_r8_low_form _ _ _ _ _ (hmode 4) rfl rfl (by change 0 < 4; decide),
    show BitVec.add (BitVec.add s.RIP 1#64) 2#64 = BitVec.add s.RIP 3#64
      from BitVec.add_assoc s.RIP 1#64 2#64] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy1 s _ h 0xb6 [modrm] ⟨by decide, by decide⟩ hcode hlow hd
    ((hmode 4).of_cs_lma_eq rfl rfl)

def movzxAlEffect (p : BitVec 64) (dst : BitVec 5) (s : RamState) : Effect :=
  { rip := p + 3
    writes := [⟨(Operand.reg dst : Operand 64),
      ((Operand.reg 0 : Operand 8).read s).setWidth 64⟩] }

theorem movzx_r32_al_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hrm : modrmRm modrm = 0) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x0f, 0xb6, modrm])
      (movzxAlEffect p (gprNumber 0 0 (modrmReg modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, movzx_r32_al_step s h modrm hmod hrm hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeResult h 3 _ _ _,
    ⟨afterStep_writeResult_rip h 3 _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s 3 _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self32, movzxSpec, Operand.read_afterFetches,
    Operand.read_beforeFetch]
  exact BitVec.setWidth_setWidth (by decide)

end P256.Proofs.Common.Encoding.Parser.CompressedRoute
