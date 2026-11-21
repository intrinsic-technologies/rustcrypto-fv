import P256.Proofs.Common.Memory.Fill.Prologue.ZeroProduct.Movzx
import P256.Proofs.Common.Encoding.Parser.CompressedRoute.Movzx
import P256.Proofs.Common.EffectCompose

set_option autoImplicit false

namespace P256.Proofs.Common.Instructions.MovzxByte
open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem movzx_r32_r8_rex_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (rex modrm : UInt8) (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP [rex, 0x0f, 0xb6, modrm])
    (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    X86.Machine.step s = some (.next (afterStep s 4 fun t =>
      writeResult t (.reg (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) : Operand 32)
        (movzxSpec 32 (((Operand.reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) : Operand 64).read t).setWidth 8))
        (BitVec.add s.RIP 4#64))) := by
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [rex, 0x0f, 0xb6, modrm] := hcode
  have f1 := memFetch_run_of_bytesAt (beforeFetch s) 3 h.fetchReady hc hlow 2
    (by simp) (by decide)
  have f2 : (Mem_Fetch (BitVec.add (BitVec.add s.RIP 2#64) 1#64) 8).run
      (afterFetches (beforeFetch s) 4) =
        (.ok modrm.toBitVec, afterFetches (beforeFetch s) 5) := by
    rw [show BitVec.add (BitVec.add s.RIP 2#64) 1#64 = BitVec.add s.RIP 3#64
      from BitVec.add_assoc s.RIP 2#64 1#64]
    exact memFetch_run_of_bytesAt (beforeFetch s) 4 h.fetchReady hc hlow 3
      (by simp) (by decide)
  have hmode (j : Nat) : In64BitMode (afterFetches (beforeFetch s) j) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf : DecoderFeatures (afterFetches (beforeFetch s) 5) :=
    h.features.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hd := decodeLegacy1_run_of_opcodeB6 _ _ (BitVec.add s.RIP 2#64)
    (rexContext s.DS rex.toBitVec) rfl (hmode 4) f1
  rw [P256.Proofs.Common.Memory.Fill.decodeLegacy1OpcodeB6_run_of_register _ _ _ _ _ hmod (hmode 5) hf f2,
    P256.Proofs.Common.Memory.Fill.movzx_r32_r8_form _ _ _ _ _ (hmode 5) (hrex.operand_size _) rfl rfl,
    show BitVec.add (BitVec.add s.RIP 2#64) 2#64 = BitVec.add s.RIP 4#64
      from BitVec.add_assoc s.RIP 2#64 2#64] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy1 s _ h rex 0xb6 [modrm] hrex.rexPrefix
    (by decide) hcode hlow hd ((hmode 5).of_cs_lma_eq rfl rfl)

theorem movzx_r32_r8_step [Bindings] (s : RamState) (h : ReadyToStep s) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hsmall : (gprNumber 0 0 (modrmRm modrm)).toNat < 4)
    (hcode : BytesAt s s.RIP [0x0f, 0xb6, modrm]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    Machine.step s = some (.next (afterStep s 3 fun t =>
      writeResult t (.reg (gprNumber 0 0 (modrmReg modrm)) : Operand 32)
        (movzxSpec 32 (((Operand.reg (gprNumber 0 0 (modrmRm modrm)) : Operand 64).read t).setWidth 8)) (BitVec.add s.RIP 3#64))) := by
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
  rw [P256.Proofs.Common.Encoding.Parser.CompressedRoute.movzx_r32_r8_low_form _ _ (legacyContext s.DS) (modrmReg modrm) (modrmRm modrm) (hmode 4) rfl rfl hsmall,
    show BitVec.add (BitVec.add s.RIP 1#64) 2#64 = BitVec.add s.RIP 3#64
      from BitVec.add_assoc s.RIP 1#64 2#64] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy1 s _ h 0xb6 [modrm] ⟨by decide, by decide⟩ hcode hlow hd
    ((hmode 4).of_cs_lma_eq rfl rfl)

def movzxR32R8Effect (p : BitVec 64) (len : Nat) (dst src : BitVec 5) (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      ((Operand.reg src : Operand 64).read s).setWidth 8 |>.setWidth 64⟩] }

theorem movzx_r32_r8_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0x0f, 0xb6, modrm])
      (movzxR32R8Effect p 4 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, movzx_r32_r8_rex_step s h rex modrm hrex hmod hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeResult h 4 _ _ _,
    ⟨afterStep_writeResult_rip h 4 _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s 4 _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self32, movzxSpec, Operand.read_afterFetches,
    Operand.read_beforeFetch]
  exact BitVec.setWidth_setWidth (by decide)

theorem movzx_r32_r8_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hsmall : (gprNumber 0 0 (modrmRm modrm)).toNat < 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x0f, 0xb6, modrm])
      (movzxR32R8Effect p 3 (gprNumber 0 0 (modrmReg modrm)) (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, movzx_r32_r8_step s h modrm hmod hsmall hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeResult h 3 _ _ _,
    ⟨afterStep_writeResult_rip h 3 _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s 3 _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self32, movzxSpec, Operand.read_afterFetches,
    Operand.read_beforeFetch]
  exact BitVec.setWidth_setWidth (by decide)

@[x86_local] theorem movzxR32R8Effect_local (p : BitVec 64) (len : Nat) (dst src : BitVec 5) :
    Effect.Local (movzxR32R8Effect p len dst src) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [movzxR32R8Effect, h.read_reg]
  · intro s
    simp [movzxR32R8Effect, Write.Full, Operand.Full]

attribute [x86_compose] movzxR32R8Effect

end P256.Proofs.Common.Instructions.MovzxByte
