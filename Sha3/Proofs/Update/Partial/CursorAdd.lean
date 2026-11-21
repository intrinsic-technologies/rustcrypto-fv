import Sha3.Proofs.X86.Instructions.Add.Step
import X86Proofs.Program.Effect

namespace Sha3.Proofs.Update.Partial

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem decodeLegacy0_run_of_opcode00 [Bindings] (s u : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hrex2 : context.rex2_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x00, u)) (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s =
      some ((Decode_Legacy_0_Opcode_00 ip context).run u) := by
  unfold Decode_Legacy_0
  rw [ite_eq_right (fun h ↦ Bool.false_ne_true (hrex2.symm.trans h))]
  rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
  repeat erw [decodeLegacy0_modeGuard_run _ _ hmode]
  rfl

theorem selectLegacy0Opcode00_run_of_register (context : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_0_Opcode_00 context true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_0_Opcode_00, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

theorem decodeLegacy0Opcode00_run_of_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_00 ip context).run s =
      (X86.Instructions.ADD_GPR8_GPR8_00 (BitVec.add ip 2#64) context
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_00
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f ↦ selectLegacy0Opcode00_run_of_register context a b c d e f modrm hmod)

theorem decodeLegacy0_run_of_00 [Bindings] (s : RamState) (h : ReadyToStep s) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hcode : BytesAt s s.RIP [0x00, modrm])
    (hlow : s.RIP.toNat + 2 ≤ 2^32) :
    (Decode_Legacy_0 s.RIP (legacyContext s.DS)).run (afterFetches (beforeFetch s) 1) =
      some ((X86.Instructions.ADD_GPR8_GPR8_00 (BitVec.add s.RIP 2#64)
        (legacyContext s.DS) (modrmReg modrm) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) 3)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [0x00, modrm] := hcode
  have f1 : (Mem_Fetch s.RIP 8).run (afterFetches (beforeFetch s) 1) =
      (.ok 0x00, afterFetches (beforeFetch s) 2) := by
    have := memFetch_run_of_bytesAt (beforeFetch s) 1 hf hc hlow 0 (by simp) (by decide)
    rwa [show BitVec.add (beforeFetch s).RIP (BitVec.ofNat 64 0) = (beforeFetch s).RIP
      from BitVec.add_zero _] at this
  have f2 : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok modrm.toBitVec, afterFetches (beforeFetch s) 3) :=
    memFetch_run_of_bytesAt (beforeFetch s) 2 hf hc hlow 1 (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 3) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [decodeLegacy0_run_of_opcode00 _ _ _ _ rfl f1 (hmode 2),
    decodeLegacy0Opcode00_run_of_register _ _ _ _ _ hmod (hmode 3) hfeatures f2]
  rfl

theorem writeGPR8_run_of_low {σ : Type} (s : X86.State σ) (r : BitVec 5)
    (hr : r.toNat < 4) (rex : Bool) (value : BitVec 8) (mode : In64BitMode s) :
    (Write_GPR8 r rex value).run s =
      (.ok (), { s with
        GPR := Vector.set s.GPR (gprIndex r) (mergeGPR 8 value s.GPR[gprIndex r]) }) := by
  unfold Write_GPR8
  rw [specM_bind_run _ _ mode]
  obtain ⟨i, rfl⟩ : ∃ i : Fin 4, r = BitVec.ofNat 5 i.val :=
    ⟨⟨r.toNat, hr⟩, by simp⟩
  clear hr
  finite_cases i <;> cases rex <;> rfl

theorem add_cl_al_form (s : RamState) (ip : BitVec 64) (ds : Segment)
    (hmode : In64BitMode s) :
    (X86.Instructions.ADD_GPR8_GPR8_00 ip (legacyContext ds) 0 1).run s =
      (.ok (), writeOutputs s (Operand.reg 1 : Operand 8)
        (addSpec ((Operand.reg 1 : Operand 8).read s) ((Operand.reg 0 : Operand 8).read s))
        0 ip) := by
  unfold X86.Instructions.ADD_GPR8_GPR8_00
  simp only [Operand.read, writeOutputs, Operand.write, oracleSkip_zero]
  spec_run [
    Read_GPR8 => readGPR8_run_of_low _ _ (by exact of_decide_eq_true rfl) _ hmode,
    X86.Instructions.Operations.ADD => add_operation _ 8 (by decide) _ _,
    Write_GPR8 => writeGPR8_run_of_low _ 1 (by decide) _ _
      (hmode.of_cs_lma_eq rfl rfl)]

theorem add_cl_al_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hcode : BytesAt s s.RIP [0x00, 0xc1]) (hlow : s.RIP.toNat + 2 ≤ 2^32) :
    X86.Machine.step s = some (.next (afterStep s 2 fun t ↦
      writeOutputs t (Operand.reg 1 : Operand 8)
        (addSpec ((Operand.reg 1 : Operand 8).read t) ((Operand.reg 0 : Operand 8).read t))
        0 (BitVec.add s.RIP 2#64))) := by
  have hdecode := decodeLegacy0_run_of_00 s h 0xc1 (by decide) hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 3) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [show modrmReg 0xc1 = 0 from rfl, show modrmRm 0xc1 = 1 from rfl,
    add_cl_al_form _ _ _ hmode] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0x00 [0xc1]
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode
    (hmode.of_cs_lma_eq rfl rfl)

theorem read_writeOutputs_self8 (s : RamState) (r : BitVec 5)
    (out : BitVec 8 × StatusFlags) (oracleUsed : Nat) (nextIP : BitVec 64) :
    (Operand.reg r : Operand 8).read (writeOutputs s (.reg r) out oracleUsed nextIP) =
      out.1 := by
  change ((Vector.set s.GPR (gprIndex r).val
    (Runtime.setSlice s.GPR[gprIndex r] 0 8 out.1))[(gprIndex r).val]).setWidth 8 = out.1
  rw [Vector.getElem_set_self]
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [BitVec.getLsbD_setWidth]
  simp only [hk, decide_true, Bool.true_and]
  rw [getLsbD_setSlice _ 0 8 _ k (by omega)]
  simp [hk]

def addClAlEffect (p : BitVec 64) (s : RamState) : Effect :=
  let a := (Operand.reg 1 : Operand 8).read s
  let b := (Operand.reg 0 : Operand 8).read s
  { rip := p + 2
    writes := [⟨(Operand.reg 1 : Operand 8), a + b⟩]
    flags := some (.ofStatusFlags (addSpec a b).2) }

theorem addClAlEffect_components (p : BitVec 64) (s : RamState) :
    (addClAlEffect p s).components = [.reg 1, .flags, .rip] := rfl

theorem add_cl_al_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p [0x00, 0xc1]) (addClAlEffect p) := by
  rintro s h hcode rfl
  refine ⟨_, add_cl_al_step s h hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeOutputs h 2 _ _ 0 _,
    ⟨afterStep_writeOutputs_rip h 2 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep, read_writeOutputs_self8]
    simp only [addSpec, Operand.read_afterFetches, Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

end Sha3.Proofs.Update.Partial
