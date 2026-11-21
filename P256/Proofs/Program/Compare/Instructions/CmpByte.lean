import P256.Proofs.Program.Compare.Instructions.ByteRegister

namespace P256.Proofs.Program.Compare

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem decodeLegacy0_run_of_opcode38 [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok 0x38, t)) (hmode : In64BitMode t) :
    (Decode_Legacy_0 ip ctx).run s = some ((Decode_Legacy_0_Opcode_38 ip ctx).run t) := by
  unfold Decode_Legacy_0
  rw [ite_eq_right (fun h => Bool.false_ne_true (hrex2.symm.trans h))]
  rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
  repeat erw [decodeLegacy0_modeGuard_run _ _ hmode]
  rfl

theorem selectLegacy0Opcode38_run_of_register (context : Instruction_Context) (a b c d e f : Bool) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_0_Opcode_38 context true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_0_Opcode_38, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

theorem decodeLegacy0Opcode38_run_of_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_0_Opcode_38 ip context).run s =
      (X86.Instructions.CMP_GPR8_GPR8_38 (BitVec.add ip 2#64) context
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_0_Opcode_38
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy0Opcode38_run_of_register context a b c d e f modrm hmod)

theorem decodeLegacy0_run_of_38_register [Bindings] (s : RamState) (h : ReadyToStep s)
    (bytes : List UInt8) (j : Nat) (modrm : UInt8) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32)
    (hop : bytes[j]? = some 0x38) (hm : bytes[j + 1]? = some modrm)
    (hj : j + 1 < 15) (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false) :
    (Decode_Legacy_0 (BitVec.add s.RIP (BitVec.ofNat 64 j)) ctx).run
        (afterFetches (beforeFetch s) (j + 1)) =
      some ((X86.Instructions.CMP_GPR8_GPR8_38 (BitVec.add s.RIP (BitVec.ofNat 64 (j + 2))) ctx
        (modrmReg modrm) (modrmRm modrm)).run (afterFetches (beforeFetch s) (j + 3))) := by
  rw [← add_ofNat_add]
  exact decodeLegacy0_run_of_modrm_at s h bytes j 0x38 modrm hcode hlow hop hm hj ctx _ _
    (fun a u hf hmode => decodeLegacy0_run_of_opcode38 a u _ ctx hrex2 hf hmode)
    (fun a u hf hmode hfe =>
      decodeLegacy0Opcode38_run_of_register a u _ ctx _ hmod hmode hfe hf)

theorem cmp_r8_r8_form [Bindings] (s : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (hdst : (ctx.rex_prefix_present || ctx.rex2_prefix_present ||
      ctx.vex_prefix_present || ctx.evex_prefix_present) = true ∨
      (gprNumber ctx.rex_b4 ctx.rex_b3 rm).toNat < 4)
    (hsrc : (ctx.rex_prefix_present || ctx.rex2_prefix_present ||
      ctx.vex_prefix_present || ctx.evex_prefix_present) = true ∨
      (gprNumber ctx.rex_r4 ctx.rex_r3 reg).toNat < 4)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.CMP_GPR8_GPR8_38 ip ctx reg rm).run s =
      let dst : Operand 8 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      let src : Operand 8 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (.ok (), writeFlagsOutputs s (cmpSpec (dst.read s) (src.read s)) 0 ip) := by
  have hcontext : {ctx with lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext] at hdst hsrc ⊢
  unfold X86.Instructions.CMP_GPR8_GPR8_38
  simp only [Operand.read, writeFlagsOutputs]
  spec_run [
    Read_GPR8 => (by first
      | exact readGPR8_run_of_rex_or_low _ _ _ hmode hdst
      | exact readGPR8_run_of_rex_or_low _ _ _ hmode hsrc),
    X86.Instructions.Operations.CMP => cmp_operation _ 8 (by decide +kernel) _ _]

theorem cmp_r8_r8_rex_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (rex modrm : UInt8) (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP [rex, 0x38, modrm]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    let dst : Operand 8 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    let src : Operand 8 := .reg (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
    Machine.step s = some (.next (afterStep s 3 fun t =>
      writeFlagsOutputs t (cmpSpec (dst.read t) (src.read t)) 0
        (BitVec.add s.RIP 3#64))) := by
  have hd := decodeLegacy0_run_of_38_register s h _ 1 modrm hmod hcode hlow
    rfl rfl (by decide +kernel) (rexContext s.DS rex.toBitVec) rfl
  have hmode : In64BitMode (afterFetches (beforeFetch s) 4) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf := cmp_r8_r8_form (afterFetches (beforeFetch s) 4) (BitVec.add s.RIP 3#64)
    (rexContext s.DS rex.toBitVec) (modrmReg modrm) (modrmRm modrm) hmode (.inl rfl) (.inl rfl) rfl
  have hd' := hd.trans (congrArg some hf)
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex 0x38 [modrm] hrex
    (legacyOpcode_of_check _ ⟨by decide +kernel, by decide +kernel⟩) hcode hlow hd'
    (hmode.of_cs_lma_eq rfl rfl)

theorem cmp_r8_r8_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (modrm : UInt8) (hmod : modrmMod modrm = 3)
    (hdst : (gprNumber 0 0 (modrmRm modrm)).toNat < 4)
    (hsrc : (gprNumber 0 0 (modrmReg modrm)).toNat < 4)
    (hcode : BytesAt s s.RIP [0x38, modrm]) (hlow : s.RIP.toNat + 2 ≤ 2^32) :
    let dst : Operand 8 := .reg (gprNumber 0 0 (modrmRm modrm))
    let src : Operand 8 := .reg (gprNumber 0 0 (modrmReg modrm))
    Machine.step s = some (.next (afterStep s 2 fun t =>
      writeFlagsOutputs t (cmpSpec (dst.read t) (src.read t)) 0
        (BitVec.add s.RIP 2#64))) := by
  have hd := decodeLegacy0_run_of_38_register s h _ 0 modrm hmod hcode hlow
    rfl rfl (by decide +kernel) (legacyContext s.DS) rfl
  rw [show BitVec.add s.RIP 0#64 = s.RIP from BitVec.add_zero _] at hd
  have hmode : In64BitMode (afterFetches (beforeFetch s) 3) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf := cmp_r8_r8_form (afterFetches (beforeFetch s) 3) (BitVec.add s.RIP 2#64)
    (legacyContext s.DS) (modrmReg modrm) (modrmRm modrm) hmode (.inr hdst) (.inr hsrc) rfl
  have hd' := hd.trans (congrArg some hf)
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0x38 [modrm]
    (legacyOpcode_of_check _ ⟨by decide +kernel, by decide +kernel⟩) hcode hlow hd'
    (hmode.of_cs_lma_eq rfl rfl)

def cmpR8R8Effect (p : BitVec 64) (len : Nat) (dst src : BitVec 5) (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 len
    writes := []
    flags := some (.ofStatusFlags (cmpSpec ((Operand.reg dst : Operand 8).read s)
      ((Operand.reg src : Operand 8).read s))) }

theorem cmp_r8_r8_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0x38, modrm])
      (cmpR8R8Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))) := by
  rintro s h hc rfl
  refine ⟨_, cmp_r8_r8_rex_step s h rex modrm hrex hmod hc.bytesAt
    (hc.low (by simp) (by simp)), ReadyToStep.afterStep_writeFlagsOutputs h 3 _ 0 _,
    ⟨afterStep_writeFlagsOutputs_rip h 3 _ 0 _, trivial, StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _,
      AgreesExcept.afterStep_writeFlagsOutputs s 3 _ 0 _⟩⟩

theorem cmp_r8_r8_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3)
    (hdst : (gprNumber 0 0 (modrmRm modrm)).toNat < 4)
    (hsrc : (gprNumber 0 0 (modrmReg modrm)).toNat < 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x38, modrm])
      (cmpR8R8Effect p 2 (gprNumber 0 0 (modrmRm modrm))
        (gprNumber 0 0 (modrmReg modrm))) := by
  rintro s h hc rfl
  refine ⟨_, cmp_r8_r8_step s h modrm hmod hdst hsrc hc.bytesAt
    (hc.low (by simp) (by simp)), ReadyToStep.afterStep_writeFlagsOutputs h 2 _ 0 _,
    ⟨afterStep_writeFlagsOutputs_rip h 2 _ 0 _, trivial, StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _,
      AgreesExcept.afterStep_writeFlagsOutputs s 2 _ 0 _⟩⟩

end P256.Proofs.Program.Compare
