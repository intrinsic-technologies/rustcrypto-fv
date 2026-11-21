import P256.Proofs.Program.Compare.Instructions.ByteRegister
import P256.Proofs.Program.Compare.Instructions.Decode

namespace P256.Proofs.Program.Compare

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

attribute [x86_compose] movzxR32M8Effect

@[x86_local] theorem movzxR32M8Effect_local [Bindings] (p : BitVec 64) (len : Nat)
    (dst : BitVec 5) (am : AddrMode) : Effect.Local (movzxR32M8Effect p len dst am) := by
  effect_local [movzxR32M8Effect]

def movzxR32RegEffect (p : BitVec 64) (len width : Nat) (dst src : BitVec 5)
    (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      (((Operand.reg src : Operand width).read s).setWidth 32).setWidth 64⟩] }

theorem selectLegacy1OpcodeB6_run_of_register (ctx : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_B6 ctx true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_1_Opcode_B6, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

theorem decodeLegacy1OpcodeB6_run_of_register [Bindings] (s t : RamState)
    (ip : BitVec 64) (ctx : Instruction_Context) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_B6 ip ctx).run s =
      (X86.Instructions.MOVZX_GPRv_GPR8 (BitVec.add ip 2#64) ctx
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_B6
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy1OpcodeB6_run_of_register ctx a b c d e f modrm hmod)

theorem movzx_r32_r8_form [Bindings] (s : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (hsize : ctx.operand_size = 32) (hlock : ctx.lock_prefix_present = false)
    (hr : (ctx.rex_prefix_present || ctx.rex2_prefix_present ||
      ctx.vex_prefix_present || ctx.evex_prefix_present) = true ∨
      (gprNumber ctx.rex_b4 ctx.rex_b3 rm).toNat < 4) :
    (X86.Instructions.MOVZX_GPRv_GPR8 ip ctx reg rm).run s =
      let dst : Operand 32 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let src : Operand 8 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeResult s dst (movzxSpec 32 (src.read s)) ip) := by
  have hcontext : {ctx with operand_size := 32, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext] at hr ⊢
  unfold X86.Instructions.MOVZX_GPRv_GPR8
  simp only [Operand.read, writeResult, Operand.write_reg32]
  spec_bind_rfl
  spec_bind_rfl
  refine (specM_bind_run _ _ (readGPR8_run_of_rex_or_low _ _ _ hmode hr)).trans ?_
  simp only [Bool.false_eq_true, ↓reduceIte]
  spec_bind_rfl
  refine (specM_bind_run _ _ (movzx_operation _ 32 (.inr rfl) _)).trans ?_
  spec_bind_rfl
  spec_bind_rfl
  refine (writeGPR32_run _ _ _ ?_).trans ?_
  · exact hmode.of_cs_lma_eq rfl rfl
  · rfl

theorem movzx_0FB6_register_run [Bindings] (s : RamState) (h : ReadyToStep s)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (hsize : ctx.operand_size = 32) (hlock : ctx.lock_prefix_present = false)
    (modrm : UInt8) (hmod : modrmMod modrm = 3)
    (hr : (ctx.rex_prefix_present || ctx.rex2_prefix_present ||
      ctx.vex_prefix_present || ctx.evex_prefix_present) = true ∨
      (gprNumber ctx.rex_b4 ctx.rex_b3 (modrmRm modrm)).toNat < 4)
    (bytes : List UInt8) (k : Nat) (hk : k + 1 < 15)
    (hop : bytes[k]? = some 0xB6) (hm : bytes[k + 1]? = some modrm)
    (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32) :
    (Decode_Legacy_1 (BitVec.add s.RIP (BitVec.ofNat 64 k)) ctx).run
        (afterFetches (beforeFetch s) (k + 1)) =
      some (.ok (), writeResult (afterFetches (beforeFetch s) (k + 3))
        (.reg (gprNumber ctx.rex_r4 ctx.rex_r3 (modrmReg modrm)) : Operand 32)
        (movzxSpec 32 ((Operand.reg (gprNumber ctx.rex_b4 ctx.rex_b3 (modrmRm modrm)) : Operand 8).read s))
        (BitVec.add s.RIP (BitVec.ofNat 64 (k + 2)))) := by
  have hd := decodeLegacy1_run_of_modrm_at s h bytes k 0xB6 modrm hcode hlow hop hm hk ctx _ _
    (fun a u hf hmode => decodeLegacy1_run_of_opcodeB6 a u _ ctx hrex2 hmode hf)
    (fun a u hf hmode hfe =>
      decodeLegacy1OpcodeB6_run_of_register a u _ ctx _ hmod hmode hfe hf)
  have hmode : In64BitMode (afterFetches (beforeFetch s) (k + 3)) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf := movzx_r32_r8_form (afterFetches (beforeFetch s) (k + 3))
    (BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 k)) 2#64) ctx
    (modrmReg modrm) (modrmRm modrm) hmode hsize hlock hr
  have result := hd.trans (congrArg some hf)
  rw [add_ofNat_add] at result
  exact result

theorem movzx_r32_r8_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (modrm : UInt8) (hmod : modrmMod modrm = 3)
    (hr : (gprNumber 0 0 (modrmRm modrm)).toNat < 4)
    (hcode : BytesAt s s.RIP [0x0f, 0xB6, modrm]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    Machine.step s = some (.next (afterStep s 3 fun t =>
      writeResult t (.reg (gprNumber 0 0 (modrmReg modrm)) : Operand 32)
        (movzxSpec 32 ((Operand.reg (gprNumber 0 0 (modrmRm modrm)) : Operand 8).read t))
        (BitVec.add s.RIP 3#64))) := by
  have hd := movzx_0FB6_register_run s h (legacyContext s.DS) rfl
    (legacyContext_operand_size s.DS) rfl modrm hmod (.inr hr)
    [0x0f, 0xB6, modrm] 1 (by decide +kernel) rfl rfl hcode hlow
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy1 s _ h 0xB6 [modrm] (by decide +kernel)
    hcode hlow hd (in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma)

theorem movzx_r32_r8_effect_step [Bindings] (p : BitVec 64)
    (modrm : UInt8) (hmod : modrmMod modrm = 3)
    (hr : (gprNumber 0 0 (modrmRm modrm)).toNat < 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x0f, 0xB6, modrm])
      (movzxR32RegEffect p 3 8 (gprNumber 0 0 (modrmReg modrm)) (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hc rfl
  refine ⟨_, movzx_r32_r8_step s h modrm hmod hr hc.bytesAt
    (hc.low (by simp) (by simp)), ReadyToStep.afterStep_writeResult h 3 _ _ _,
    ⟨afterStep_writeResult_rip h 3 _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s 3 _ _ _⟩⟩
  change (Operand.reg _ : Operand 64).read _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self32, movzxSpec, Operand.read_afterFetches,
    Operand.read_beforeFetch]

theorem movzx_r32_r8_rex_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (rex : UInt8) (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP [rex, 0x0f, 0xB6, modrm]) (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    Machine.step s = some (.next (afterStep s 4 fun t =>
      writeResult t (.reg (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) : Operand 32)
        (movzxSpec 32 ((Operand.reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) : Operand 8).read t))
        (BitVec.add s.RIP 4#64))) := by
  have hd := movzx_0FB6_register_run s h (rexContext s.DS rex.toBitVec) rfl
    (hrex.operand_size s.DS) rfl modrm hmod (.inl rfl)
    [rex, 0x0f, 0xB6, modrm] 2 (by decide +kernel) rfl rfl hcode hlow
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy1 s _ h rex 0xB6 [modrm] hrex.rexPrefix (by decide +kernel)
    hcode hlow hd (in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma)

theorem movzx_r32_r8_rex_effect_step [Bindings] (p : BitVec 64)
    (rex : UInt8) (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0x0f, 0xB6, modrm])
      (movzxR32RegEffect p 4 8 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hc rfl
  refine ⟨_, movzx_r32_r8_rex_step s h rex hrex modrm hmod hc.bytesAt
    (hc.low (by simp) (by simp)), ReadyToStep.afterStep_writeResult h 4 _ _ _,
    ⟨afterStep_writeResult_rip h 4 _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s 4 _ _ _⟩⟩
  change (Operand.reg _ : Operand 64).read _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self32, movzxSpec, Operand.read_afterFetches,
    Operand.read_beforeFetch]

theorem movzx16_operation {σ : Type} (s : X86.State σ) (x : BitVec 16) :
    (liftM (X86.Instructions.Operations.MOVZX 16 32 x) :
      X86.Runtime.SpecM X86.Exception (X86.State σ) (BitVec 32)).run s =
      (.ok (movzxSpec 32 x), s) := by
  have hx : X86.Instructions.Operations.MOVZX 16 32 x = .ok (movzxSpec 32 x) := by
    simp [X86.Instructions.Operations.MOVZX, x86_runtime, movzxSpec, bind, pure,
      Except.bind, Except.pure]
  rw [hx]
  rfl

theorem decodeLegacy1_run_of_opcodeB7 [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (hmode : In64BitMode t) (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xB7, t)) :
    (Decode_Legacy_1 ip ctx).run s = some ((Decode_Legacy_1_Opcode_B7 ip ctx).run t) := by
  unfold Decode_Legacy_1
  rw [ite_eq_right (fun h => Bool.false_ne_true (hrex2.symm.trans h))]
  rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
  repeat erw [decodeLegacy0_modeGuard_run _ _ hmode]
  repeat erw [decodeLegacy1_modeGuard_run _ _ _ _ hmode]
  rfl

theorem selectLegacy1OpcodeB7_run_of_register (ctx : Instruction_Context)
    (a b c d e f : Bool) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_B7 ctx true a b c d e f modrm = .ok 4 := by
  simp [Select_Legacy_1_Opcode_B7, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

theorem decodeLegacy1OpcodeB7_run_of_register [Bindings] (s t : RamState)
    (ip : BitVec 64) (ctx : Instruction_Context) (modrm : BitVec 8)
    (hmod : modrm.extractLsb' 6 2 = 3#2) (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_B7 ip ctx).run s =
      (X86.Instructions.MOVZX_GPRv_GPR16 (BitVec.add ip 2#64) ctx
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_B7
  decode_modrm_form s t ip hfetch hmode hf
    (fun a b c d e f => selectLegacy1OpcodeB7_run_of_register ctx a b c d e f modrm hmod)

theorem movzx_r32_r16_form [Bindings] (s : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (hsize : ctx.operand_size = 32) (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.MOVZX_GPRv_GPR16 ip ctx reg rm).run s =
      let dst : Operand 32 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let src : Operand 16 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeResult s dst (movzxSpec 32 (src.read s)) ip) := by
  have hcontext : {ctx with operand_size := 32, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.MOVZX_GPRv_GPR16
  simp only [Operand.read, writeResult, Operand.write_reg32]
  spec_bind_rfl
  spec_bind_rfl
  refine (specM_bind_run _ _ (readGPR16_run _ _ hmode)).trans ?_
  simp only [Bool.false_eq_true, ↓reduceIte]
  spec_bind_rfl
  refine (specM_bind_run _ _ (movzx16_operation _ _)).trans ?_
  spec_bind_rfl
  spec_bind_rfl
  refine (writeGPR32_run _ _ _ ?_).trans ?_
  · exact hmode.of_cs_lma_eq rfl rfl
  · rfl

theorem movzx_0FB7_register_run [Bindings] (s : RamState) (h : ReadyToStep s)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (hsize : ctx.operand_size = 32) (hlock : ctx.lock_prefix_present = false)
    (modrm : UInt8) (hmod : modrmMod modrm = 3)
    (bytes : List UInt8) (k : Nat) (hk : k + 1 < 15)
    (hop : bytes[k]? = some 0xB7) (hm : bytes[k + 1]? = some modrm)
    (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32) :
    (Decode_Legacy_1 (BitVec.add s.RIP (BitVec.ofNat 64 k)) ctx).run
        (afterFetches (beforeFetch s) (k + 1)) =
      some (.ok (), writeResult (afterFetches (beforeFetch s) (k + 3))
        (.reg (gprNumber ctx.rex_r4 ctx.rex_r3 (modrmReg modrm)) : Operand 32)
        (movzxSpec 32 ((Operand.reg (gprNumber ctx.rex_b4 ctx.rex_b3 (modrmRm modrm)) : Operand 16).read s))
        (BitVec.add s.RIP (BitVec.ofNat 64 (k + 2)))) := by
  have hd := decodeLegacy1_run_of_modrm_at s h bytes k 0xB7 modrm hcode hlow hop hm hk ctx _ _
    (fun a u hf hmode => decodeLegacy1_run_of_opcodeB7 a u _ ctx hrex2 hmode hf)
    (fun a u hf hmode hfe =>
      decodeLegacy1OpcodeB7_run_of_register a u _ ctx _ hmod hmode hfe hf)
  have hmode : In64BitMode (afterFetches (beforeFetch s) (k + 3)) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf := movzx_r32_r16_form (afterFetches (beforeFetch s) (k + 3))
    (BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 k)) 2#64) ctx
    (modrmReg modrm) (modrmRm modrm) hmode hsize hlock
  have result := hd.trans (congrArg some hf)
  rw [add_ofNat_add] at result
  exact result

theorem movzx_r32_r16_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (modrm : UInt8) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP [0x0f, 0xB7, modrm]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    Machine.step s = some (.next (afterStep s 3 fun t =>
      writeResult t (.reg (gprNumber 0 0 (modrmReg modrm)) : Operand 32)
        (movzxSpec 32 ((Operand.reg (gprNumber 0 0 (modrmRm modrm)) : Operand 16).read t))
        (BitVec.add s.RIP 3#64))) := by
  have hd := movzx_0FB7_register_run s h (legacyContext s.DS) rfl
    (legacyContext_operand_size s.DS) rfl modrm hmod
    [0x0f, 0xB7, modrm] 1 (by decide +kernel) rfl rfl hcode hlow
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy1 s _ h 0xB7 [modrm] (by decide +kernel)
    hcode hlow hd (in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma)

theorem movzx_r32_r16_effect_step [Bindings] (p : BitVec 64)
    (modrm : UInt8) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x0f, 0xB7, modrm])
      (movzxR32RegEffect p 3 16 (gprNumber 0 0 (modrmReg modrm)) (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hc rfl
  refine ⟨_, movzx_r32_r16_step s h modrm hmod hc.bytesAt
    (hc.low (by simp) (by simp)), ReadyToStep.afterStep_writeResult h 3 _ _ _,
    ⟨afterStep_writeResult_rip h 3 _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s 3 _ _ _⟩⟩
  change (Operand.reg _ : Operand 64).read _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self32, movzxSpec, Operand.read_afterFetches,
    Operand.read_beforeFetch]

theorem movzx_r32_r16_rex_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (rex : UInt8) (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP [rex, 0x0f, 0xB7, modrm]) (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    Machine.step s = some (.next (afterStep s 4 fun t =>
      writeResult t (.reg (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) : Operand 32)
        (movzxSpec 32 ((Operand.reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) : Operand 16).read t))
        (BitVec.add s.RIP 4#64))) := by
  have hd := movzx_0FB7_register_run s h (rexContext s.DS rex.toBitVec) rfl
    (hrex.operand_size s.DS) rfl modrm hmod
    [rex, 0x0f, 0xB7, modrm] 2 (by decide +kernel) rfl rfl hcode hlow
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy1 s _ h rex 0xB7 [modrm] hrex.rexPrefix (by decide +kernel)
    hcode hlow hd (in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma)

theorem movzx_r32_r16_rex_effect_step [Bindings] (p : BitVec 64)
    (rex : UInt8) (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0x0f, 0xB7, modrm])
      (movzxR32RegEffect p 4 16 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hc rfl
  refine ⟨_, movzx_r32_r16_rex_step s h rex hrex modrm hmod hc.bytesAt
    (hc.low (by simp) (by simp)), ReadyToStep.afterStep_writeResult h 4 _ _ _,
    ⟨afterStep_writeResult_rip h 4 _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s 4 _ _ _⟩⟩
  change (Operand.reg _ : Operand 64).read _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self32, movzxSpec, Operand.read_afterFetches,
    Operand.read_beforeFetch]

end P256.Proofs.Program.Compare
