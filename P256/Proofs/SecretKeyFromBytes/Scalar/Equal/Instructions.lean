import X86Proofs.Instructions.Mov.Step
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.NopMem.Triple
import P256.Proofs.Common.EffectCompose

set_option autoImplicit false

namespace P256.Proofs.SecretKeyFromBytes.Scalar.Equal

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs
open scoped X86.Runtime.Syntax

theorem mov_r16_imm16_form [Bindings] (s t : RamState)
    (ip : BitVec 64) (ctx : Instruction_Context) (opcode : BitVec 8)
    (hsize : ctx.operand_size = 16) (hlock : ctx.lock_prefix_present = false)
    (imm : BitVec 16) (hfetch : (Mem_Fetch ip 16).run s = (.ok imm, t))
    (hmode : In64BitMode t) :
    (X86.Instructions.MOV_GPRv_IMMv ip ctx opcode).run s =
      (.ok (), writeResult t
        (.reg (gprNumber ctx.rex_b4 ctx.rex_b3 (opcode.extractLsb' 0 3)) : Operand 16)
        imm (BitVec.add ip 2#64)) := by
  have hcontext : {ctx with operand_size := 16, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.MOV_GPRv_IMMv
  simp only [writeResult, Operand.write]
  spec_run [Mem_Fetch => hfetch]
  dsimp only
  have hv : BitVec.ofInt (Int.toNat 16) imm.toInt = imm := BitVec.ofInt_toInt
  rw [hv]
  exact writeGPR16_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)

theorem mov_r16_imm16_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (op : UInt8) (hop : MovImmOpcode op) (imm : BitVec 16)
    (hcode : BytesAt s s.RIP (0x66 :: op :: immBytes 16 imm))
    (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    X86.Machine.step s = some (.next (afterStep s 4 fun t =>
      writeResult t (.reg (gprNumber 0 0 (opcodeReg op)) : Operand 16)
        imm (BitVec.add s.RIP 4#64))) := by
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (0x66 :: op :: immBytes 16 imm) := hcode
  have hl : s.RIP.toNat + (0x66 :: op :: immBytes 16 imm).length ≤ 2^32 := by
    simpa using hlow
  have fop : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok op.toBitVec, afterFetches (beforeFetch s) 3) :=
    memFetch_run_of_bytesAt (beforeFetch s) 2 h.fetchReady hc hl 1 (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf : DecoderFeatures (afterFetches (beforeFetch s) 3) :=
    DecoderFeatures.of_sameControls (s := s)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ h.features
  have hd := decodeLegacy0_run_of_movImmOpcode _ _ _ (oszContext s.DS) rfl
    op hop fop (hmode 3) hf
  have fimm := memFetch_run_of_bytesAt_imm (beforeFetch s) 3 h.fetchReady hc hl 16
    (by decide) imm 2 (immBytes_getElem?_append [0x66, op] imm) (by simp) (by decide)
  rw [show BitVec.add (BitVec.add s.RIP 1#64) 1#64 = BitVec.add s.RIP 2#64 from
      BitVec.add_assoc _ _ _,
    mov_r16_imm16_form _ _ (BitVec.add s.RIP 2#64) _ _ rfl rfl imm fimm (hmode 5),
    show BitVec.add (BitVec.add s.RIP 2#64) 2#64 = BitVec.add s.RIP 4#64 from
      BitVec.add_assoc _ _ _] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_66_legacy0 s _ h op _ hop.legacyOpcode hcode hl hd
    ((hmode 5).of_cs_lma_eq rfl rfl)

def movR16Imm16Effect (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 16)
    (s : RamState) : Effect :=
  { rip := p + 4
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 16 imm ((Operand.reg dst : Operand 64).read s)⟩] }

theorem mov_r16_imm16_effect_step [Bindings] (p : BitVec 64) (op : UInt8)
    (hop : MovImmOpcode op) (imm : BitVec 16) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0x66 :: op :: immBytes 16 imm))
      (movR16Imm16Effect p (gprNumber 0 0 (opcodeReg op)) imm) := by
  rintro s h hcode rfl
  refine ⟨_, mov_r16_imm16_step s h op hop imm hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeResult h 4 _ _ _,
    ⟨afterStep_writeResult_rip h 4 _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult _ _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp [writeResult, Operand.read, Operand.write, afterFetches, beforeFetch, resetStepFields]

theorem xor_r16_r16_form {σ : Type} [PhysicalMemory σ] (s : X86.State σ)
    (ip : BitVec 64) (ctx : Instruction_Context) (reg rm : BitVec 3)
    (hmode : In64BitMode s) (hsize : ctx.operand_size = 16)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.XOR_GPRv_GPRv_31 ip ctx reg rm).run s =
      let dst : Operand 16 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      let src : Operand 16 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (.ok (), writeOutputs s dst (xorSpec (oracleBit s.oracle) (dst.read s) (src.read s)) 1 ip) := by
  have hcontext : {ctx with operand_size := 16, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.XOR_GPRv_GPRv_31
  simp only [Operand.read, writeOutputs, Operand.write]
  spec_run [Read_GPR => readGPR16_run _ _ hmode,
    X86.Instructions.Operations.XOR => xor_operation _ 16 (by decide) _ _,
    Write_GPR => writeGPR16_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

theorem xor_r16_r16_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (modrm : UInt8) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP [0x66, 0x31, modrm])
    (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    let dst : Operand 16 := .reg (gprNumber 0 0 (modrmRm modrm))
    let src : Operand 16 := .reg (gprNumber 0 0 (modrmReg modrm))
    X86.Machine.step s = some (.next (afterStep s 3 fun t =>
      writeOutputs t dst (xorSpec (oracleBit t.oracle) (dst.read t) (src.read t)) 1
        (BitVec.add s.RIP 3#64))) := by
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [0x66, 0x31, modrm] := hcode
  have fop : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok 0x31, afterFetches (beforeFetch s) 3) :=
    memFetch_run_of_bytesAt (beforeFetch s) 2 h.fetchReady hc hlow 1 (by simp) (by decide)
  have fm : (Mem_Fetch (BitVec.add (BitVec.add s.RIP 1#64) 1#64) 8).run
      (afterFetches (beforeFetch s) 3) = (.ok modrm.toBitVec, afterFetches (beforeFetch s) 4) := by
    rw [show BitVec.add (BitVec.add s.RIP 1#64) 1#64 = BitVec.add s.RIP 2#64 from
      BitVec.add_assoc _ _ _]
    exact memFetch_run_of_bytesAt (beforeFetch s) 3 h.fetchReady hc hlow 2 (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf : DecoderFeatures (afterFetches (beforeFetch s) 4) :=
    DecoderFeatures.of_sameControls (s := s)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ h.features
  have hd := decodeLegacy0_run_of_opcode31 _ _ _ (oszContext s.DS) rfl fop (hmode 3)
  rw [decodeLegacy0Opcode31_run_of_register _ _ _ _ _ hmod (hmode 4) hf fm,
    show BitVec.add (BitVec.add s.RIP 1#64) 2#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc _ _ _,
    xor_r16_r16_form _ _ _ _ _ (hmode 4) rfl rfl] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_66_legacy0 s _ h 0x31 [modrm]
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hd
    ((hmode 4).of_cs_lma_eq rfl rfl)

def xorR16R16Effect (p : BitVec 64) (dst src : BitVec 5) (s : RamState) : Effect :=
  let r := (Operand.reg dst : Operand 16).read s ^^^ (Operand.reg src : Operand 16).read s
  { rip := p + 3
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 16 r ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (xorFlags r) }

theorem xor_r16_r16_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x66, 0x31, modrm])
      (xorR16R16Effect p (gprNumber 0 0 (modrmRm modrm)) (gprNumber 0 0 (modrmReg modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, xor_r16_r16_step s h modrm hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), ReadyToStep.afterStep_writeOutputs h 3 _ _ 1 _,
    ⟨afterStep_writeOutputs_rip h 3 _ _ 1 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ 1 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp [writeOutputs, Operand.read, Operand.write, xorSpec, setFlags,
      afterFetches, beforeFetch, resetStepFields]
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem equality_nop_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p [0x66, 0x66, 0x66, 0x66, 0x2e, 0x0f, 0x1f, 0x84, 0, 0, 0, 0, 0])
      (fun _ => nopEffect p 13) :=
  nop_m_effect_step p [0x66, 0x66, 0x66, 0x66, 0x2e] (by decide) (by decide)
    (.sib 0 (some 0) 0 (.d32 0)) ⟨by decide, fun h => by cases h⟩ rfl rfl

theorem movR16Imm16Effect_components (p : BitVec 64) (dst : BitVec 5)
    (imm : BitVec 16) (s : RamState) :
    (movR16Imm16Effect p dst imm s).components = [.reg dst, .rip] := rfl

theorem xorR16R16Effect_components (p : BitVec 64) (dst src : BitVec 5) (s : RamState) :
    (xorR16R16Effect p dst src s).components = [.reg dst, .flags, .rip] := rfl

attribute [x86_compose] movR16Imm16Effect xorR16R16Effect

theorem mergeGPR16_low {n : Nat} (hn : n ≤ 16) (v : BitVec 16) (old : BitVec 64) :
    (mergeGPR 16 v old).setWidth n = v.setWidth n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, mergeGPR, show ¬16 = 32 by decide, ite_false]
  rw [getLsbD_setSlice _ _ _ _ _ (by omega)]
  simp only [Nat.zero_le, show i < 0 + 16 by omega, and_self, ite_true, Nat.sub_zero]

end P256.Proofs.SecretKeyFromBytes.Scalar.Equal
