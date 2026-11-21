import P256.Proofs.Common.Curve.LinearCombination.NafReverse.Load

set_option autoImplicit false

namespace P256.Proofs.Common.Instructions.MovzxWord

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs
open P256.Proofs.Common.Curve.LinearCombination.NafReverse

theorem decodeLegacy1OpcodeB7_run_of_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm,t)) :
    (Decode_Legacy_1_Opcode_B7 ip ctx).run s =
      (X86.Instructions.MOVZX_GPRv_GPR16 (BitVec.add ip 2#64) ctx
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  have hsel (a b c d e f : Bool) :
      Select_Legacy_1_Opcode_B7 ctx true a b c d e f modrm = .ok 4 := by
    simp [Select_Legacy_1_Opcode_B7, x86_runtime, X86.Runtime.CheckedSlice.read,
      bind, pure, Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]
  unfold Decode_Legacy_1_Opcode_B7
  decode_modrm_form s t ip hfetch hmode hf hsel

theorem movzx_r32_r16_form {σ : Type} [PhysicalMemory σ] (s : State σ) (ip : BitVec 64)
    (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (hsize : ctx.operand_size = 32) (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.MOVZX_GPRv_GPR16 ip ctx reg rm).run s =
      (.ok (), writeResult s (.reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg) : Operand 32)
        (movzxSpec 32 ((Operand.reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm) : Operand 16).read s)) ip) := by
  have hcontext : {ctx with operand_size := 32, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.MOVZX_GPRv_GPR16
  simp only [writeResult, Operand.read, Operand.write_reg32]
  spec_run [Read_GPR => readGPR16_run _ _ hmode,
    X86.Instructions.Operations.MOVZX => movzx16_operation _ 32 (.inr rfl) _,
    Write_GPR => by
      rw [writeGPR32_run {s with Next_IP := ip} _ _ (hmode.of_cs_lma_eq rfl rfl)]
      simp only [movzxSpec, BitVec.ofNat_toNat, gprNumber, Int.reduceToNat, Int.reduceAdd]]

theorem movzx_r32_r16_step [Bindings] (s : RamState) (h : ReadyToStep s) (modrm : UInt8)
    (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP [0x0f, 0xb7, modrm]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    Machine.step s = some (.next (afterStep s 3 fun t =>
      writeResult t (.reg (gprNumber 0 0 (modrmReg modrm)) : Operand 32)
        (movzxSpec 32 ((Operand.reg (gprNumber 0 0 (modrmRm modrm)) : Operand 16).read t))
        (BitVec.add s.RIP 3#64))) := by
  have fop : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok 0xb7, afterFetches (beforeFetch s) 3) :=
    memFetch_run_of_bytesAt (beforeFetch s) 2 h.fetchReady hcode hlow 1 (by simp) (by decide)
  have fmod : (Mem_Fetch (BitVec.add (BitVec.add s.RIP 1#64) 1#64) 8).run
      (afterFetches (beforeFetch s) 3) = (.ok modrm.toBitVec, afterFetches (beforeFetch s) 4) := by
    rw [show BitVec.add (BitVec.add s.RIP 1#64) 1#64 = BitVec.add s.RIP 2#64 from
      BitVec.add_assoc s.RIP 1#64 1#64]
    exact memFetch_run_of_bytesAt (beforeFetch s) 3 h.fetchReady hcode hlow 2 (by simp) (by decide)
  have hm (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf : DecoderFeatures (afterFetches (beforeFetch s) 4) :=
    h.features.of_sameControls (s := s) ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  have hd := decodeLegacy1_run_of_opcodeB7 _ _ _ (legacyContext s.DS) rfl (hm 3) fop
  rw [decodeLegacy1OpcodeB7_run_of_register _ _ _ _ _ hmod (hm 4) hf fmod,
    movzx_r32_r16_form _ _ _ _ _ (hm 4) rfl rfl,
    show BitVec.add (BitVec.add s.RIP 1#64) 2#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc s.RIP 1#64 2#64] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy1 s _ h 0xb7 [modrm]
    ⟨by decide,by decide⟩ hcode hlow hd ((hm 4).of_cs_lma_eq rfl rfl)

def movzxR32R16Effect (p : BitVec 64) (dst src : BitVec 5) (s : RamState) : Effect :=
  { rip := p + 3
    writes := [⟨(Operand.reg dst : Operand 64),
      ((Operand.reg src : Operand 16).read s).setWidth 64⟩] }

theorem movzx_r32_r16_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x0f,0xb7,modrm])
      (movzxR32R16Effect p (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, movzx_r32_r16_step s h modrm hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), ReadyToStep.afterStep_writeResult h 3 _ _ _,
    ⟨afterStep_writeResult_rip h 3 _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s 3 _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self32, movzxSpec, Operand.read_afterFetches,
    Operand.read_beforeFetch]
  exact BitVec.setWidth_setWidth (by decide)

end P256.Proofs.Common.Instructions.MovzxWord
