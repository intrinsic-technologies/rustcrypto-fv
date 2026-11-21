import X86Proofs.Instructions.Cmp.Generated.RR.Triple

set_option autoImplicit false

namespace P256.Proofs.Common.Instructions.CompareWord

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem cmp_r16_r16_form {σ : Type} [PhysicalMemory σ] (s : State σ) (ip : BitVec 64)
    (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (hsize : ctx.operand_size = 16) (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.CMP_GPRv_GPRv_39 ip ctx reg rm).run s =
      (.ok (), writeFlagsOutputs s
        (cmpSpec ((Operand.reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm) : Operand 16).read s)
          ((Operand.reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg) : Operand 16).read s)) 0 ip) := by
  have hcontext : {ctx with operand_size := 16, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.CMP_GPRv_GPRv_39
  simp only [Operand.read, writeFlagsOutputs, oracleSkip_zero]
  spec_run [Read_GPR => readGPR16_run _ _ hmode,
    X86.Instructions.Operations.CMP => cmp_operation _ 16 (by decide) _ _]

theorem cmp_r16_r16_step [Bindings] (s : RamState) (h : ReadyToStep s) (modrm : UInt8)
    (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP [0x66, 0x39, modrm]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    Machine.step s = some (.next (afterStep s 3 fun t =>
      writeFlagsOutputs t
        (cmpSpec ((Operand.reg (gprNumber 0 0 (modrmRm modrm)) : Operand 16).read t)
          ((Operand.reg (gprNumber 0 0 (modrmReg modrm)) : Operand 16).read t)) 0
        (BitVec.add s.RIP 3#64))) := by
  have fop : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok 0x39, afterFetches (beforeFetch s) 3) :=
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
  have hd := decodeLegacy0_run_of_opcode39 _ _ _ (oszContext s.DS) rfl fop (hm 3)
  rw [decodeLegacy0Opcode39_run_of_register _ _ _ _ _ hmod (hm 4) hf fmod,
    cmp_r16_r16_form _ _ _ _ _ (hm 4) rfl rfl,
    show BitVec.add (BitVec.add s.RIP 1#64) 2#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc s.RIP 1#64 2#64] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_66_legacy0 s _ h 0x39 [modrm]
    (legacyOpcode_of_check _ ⟨by decide,by decide⟩) hcode hlow hd
    ((hm 4).of_cs_lma_eq rfl rfl)

def cmpR16R16Effect (p : BitVec 64) (dst src : BitVec 5) (s : RamState) : Effect :=
  { rip := p + 3
    flags := some (.ofStatusFlags (cmpSpec ((Operand.reg dst : Operand 16).read s)
      ((Operand.reg src : Operand 16).read s))) }

theorem cmp_r16_r16_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x66,0x39,modrm])
      (cmpR16R16Effect p (gprNumber 0 0 (modrmRm modrm))
        (gprNumber 0 0 (modrmReg modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, cmp_r16_r16_step s h modrm hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), ReadyToStep.afterStep_writeFlagsOutputs h 3 _ 0 _,
    ⟨afterStep_writeFlagsOutputs_rip h 3 _ 0 _, trivial,
      StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _,
      AgreesExcept.afterStep_writeFlagsOutputs s 3 _ 0 _⟩⟩

end P256.Proofs.Common.Instructions.CompareWord
