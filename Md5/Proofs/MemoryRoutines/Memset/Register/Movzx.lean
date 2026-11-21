import X86Proofs.Core.Operand
import X86Proofs.Program.ReadWrite.WriteResult
import X86Proofs.Program.Effect
import X86Proofs.Instructions.Movzx.Operation
import X86Proofs.Step.Decode.Legacy1OpcodeB6
import X86Proofs.Instructions.Movzx.Generated.RM8.Decode
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

theorem movzx_ecx_sil_form {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ)
    (ip : BitVec 64) (ds : Segment) (hmode : In64BitMode s) :
    (X86.Instructions.MOVZX_GPRv_GPR8 ip (rexContext ds 0x40) 1 6).run s =
      (.ok (), writeResult s (.reg 1 : Operand 32)
        (((Operand.reg 6 : Operand 8).read s).setWidth 32) ip) := by
  unfold X86.Instructions.MOVZX_GPRv_GPR8
  simp only [writeResult, Operand.write_reg32]
  repeat spec_bind_rfl
  spec_bind_with readGPR8_run_of_rex _ _ hmode
  repeat spec_bind_rfl
  erw [writeGPR32_run {s with Next_IP := ip} _ _ (hmode.of_cs_lma_eq rfl rfl)]
  simp only [BitVec.ofNat_toNat]
  rfl

theorem selectLegacy1OpcodeB6_run_of_register (ctx : Instruction_Context) (a b c d e f : Bool)
    (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2) :
    Select_Legacy_1_Opcode_B6 ctx true a b c d e f modrm = .ok 1 := by
  simp [Select_Legacy_1_Opcode_B6, x86_runtime, X86.Runtime.CheckedSlice.read,
    bind, pure, Except.bind, Except.pure, hmod, HAnd.hAnd, AndOp.and, strictAnd]

theorem decodeLegacy1OpcodeB6_run_of_register [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (modrm : BitVec 8) (hmod : modrm.extractLsb' 6 2 = 3#2)
    (hmode : In64BitMode t) (hf : DecoderFeatures t)
    (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok modrm, t)) :
    (Decode_Legacy_1_Opcode_B6 ip ctx).run s =
      (X86.Instructions.MOVZX_GPRv_GPR8 (BitVec.add ip 2#64) ctx
        (modrm.extractLsb' 3 3) (modrm.extractLsb' 0 3)).run t := by
  unfold Decode_Legacy_1_Opcode_B6
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  refine (specM_bind_run _ _ hfetch).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 7 6) _ (s := t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 5 3) _ (s := t) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.sliceInclusive modrm 2 0) _ (s := t) rfl).trans ?_
  refine (decoderSelect_run t (fun mode a b c d e f ↦
    Select_Legacy_1_Opcode_B6 ctx mode a b c d e f modrm) _ 1 hmode hf
    (fun a b c d e f ↦ selectLegacy1OpcodeB6_run_of_register ctx a b c d e f modrm hmod)).trans ?_
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 2)) _ (s := t) rfl).trans ?_
  exact specM_bind_pure_unit_run _ t

theorem decodeLegacy1_run_of_rex_B6_register [Bindings] (s : RamState) (h : ReadyToStep s)
    (rex modrm : UInt8) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP [rex, 0x0F, 0xB6, modrm]) (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    (Decode_Legacy_1 (BitVec.add s.RIP 2#64) (rexContext s.DS rex.toBitVec)).run
        (afterFetches (beforeFetch s) 3) =
      some ((X86.Instructions.MOVZX_GPRv_GPR8 (BitVec.add s.RIP 4#64)
        (rexContext s.DS rex.toBitVec) (modrmReg modrm) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) 5)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [rex, 0x0F, 0xB6, modrm] := hcode
  have f2 : (Mem_Fetch (BitVec.add s.RIP 2#64) 8).run (afterFetches (beforeFetch s) 3) =
      (.ok 0xB6, afterFetches (beforeFetch s) 4) :=
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
  rw [decodeLegacy1_run_of_opcodeB6 _ _ _ _ rfl (hmode 4) f2,
    decodeLegacy1OpcodeB6_run_of_register _ _ _ _ _ hmod (hmode 5) hfeatures f3,
    show BitVec.add (BitVec.add s.RIP 2#64) 2#64 = BitVec.add s.RIP 4#64 from
      BitVec.add_assoc s.RIP 2#64 2#64]
  rfl

theorem movzx_ecx_sil_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hcode : BytesAt s s.RIP [0x40, 0x0F, 0xB6, 0xCE])
    (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    X86.Machine.step s = some (.next (afterStep s 4 fun t ↦
      writeResult t (.reg 1 : Operand 32)
        (((Operand.reg 6 : Operand 8).read t).setWidth 32) (BitVec.add s.RIP 4#64))) := by
  have hdecode := decodeLegacy1_run_of_rex_B6_register s h 0x40 0xCE (by decide) hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 5) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  change _ = some ((X86.Instructions.MOVZX_GPRv_GPR8 _ (rexContext s.DS 0x40) 1 6).run _)
    at hdecode
  rw [movzx_ecx_sil_form _ _ _ hmode] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy1 s _ h 0x40 0xB6 [0xCE]
    (by unfold RexPrefix; decide) ⟨by decide, by decide⟩ hcode hlow hdecode
    (hmode.of_cs_lma_eq rfl rfl)

def movzxEcxSilEffect (p : BitVec 64) (s : RamState) : Effect :=
  { rip := p + 4
    writes := [⟨(Operand.reg 1 : Operand 64),
      ((Operand.reg 6 : Operand 8).read s).setWidth 64⟩] }

theorem movzxEcxSilEffect_components (p : BitVec 64) (s : RamState) :
    (movzxEcxSilEffect p s).components = [.reg 1, .rip] := rfl

theorem movzxEcxSilEffect_avoids (p : BitVec 64) (s : RamState) (code : CodeMap) :
    (movzxEcxSilEffect p s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [movzxEcxSilEffect_components, Component.Covers]) code

theorem movzx_ecx_sil_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p [0x40, 0x0F, 0xB6, 0xCE])
      (movzxEcxSilEffect p) := by
  rintro s h hcode rfl
  refine ⟨_, movzx_ecx_sil_step s h hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeResult h 4 _ _ _,
    ⟨afterStep_writeResult_rip h 4 _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s 4 _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self32, Operand.read_afterFetches,
    Operand.read_beforeFetch]
  exact BitVec.setWidth_setWidth (by decide)

attribute [x86_compose] movzxEcxSilEffect

@[x86_local] theorem movzxEcxSilEffect_local (p : BitVec 64) :
    Effect.Local (movzxEcxSilEffect p) := by
  refine ⟨fun _ _ _ ↦ rfl, fun t t' h ↦ ?_, fun _ _ _ ↦ rfl,
    fun t t' h i hi ↦ ?_, fun _ ↦ ?_⟩
  · simp [movzxEcxSilEffect, h.read_reg]
  · simpa only [movzxEcxSilEffect, Effect.flag] using congrArg some hi
  · simp [movzxEcxSilEffect, Write.Full, Operand.Full]

end Md5.Proofs.MemoryRoutines.Memset.Register
