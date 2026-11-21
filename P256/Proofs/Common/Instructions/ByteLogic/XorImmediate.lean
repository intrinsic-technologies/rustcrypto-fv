import P256.Proofs.Common.Encoding.Parser.ResultTag.Xor
import P256.Proofs.Common.EffectCompose

set_option autoImplicit false

open P256.Proofs.Common.Encoding.Parser.ResultTag (decodeLegacy0Opcode80_run_of_r6_register xorR8Imm8Effect xor_r8_imm8_form)

namespace P256.Proofs.Common.Instructions.ByteLogic

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem decodeLegacy0_run_of_80_r6 [Bindings] (s : RamState) (h : ReadyToStep s)
    (modrm : UInt8) (imm : BitVec 8) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6)
    (hcode : BytesAt s s.RIP (0x80 :: modrm :: immBytes 8 imm))
    (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    (Decode_Legacy_0 s.RIP (legacyContext s.DS)).run (afterFetches (beforeFetch s) 1) =
      some ((X86.Instructions.XOR_GPR8_IMMb_80r6 (BitVec.add s.RIP 2#64)
        (legacyContext s.DS) (modrmRm modrm)).run (afterFetches (beforeFetch s) 3)) := by
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (0x80 :: modrm :: immBytes 8 imm) := hcode
  have hl : s.RIP.toNat + (0x80 :: modrm :: immBytes 8 imm).length ≤ 2^32 := by simpa using hlow
  have f1 : (Mem_Fetch s.RIP 8).run (afterFetches (beforeFetch s) 1) =
      (.ok 0x80, afterFetches (beforeFetch s) 2) := by
    have hf := memFetch_run_of_bytesAt (beforeFetch s) 1 h.fetchReady hc hl 0 (by simp) (by decide)
    rwa [show BitVec.add (beforeFetch s).RIP (BitVec.ofNat 64 0) = (beforeFetch s).RIP
      from BitVec.add_zero _] at hf
  have f2 : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok modrm.toBitVec, afterFetches (beforeFetch s) 3) :=
    memFetch_run_of_bytesAt (beforeFetch s) 2 h.fetchReady hc hl 1 (by simp) (by decide)
  have hm (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hf : DecoderFeatures (afterFetches (beforeFetch s) 3) :=
    DecoderFeatures.of_sameControls (s := s)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ h.features
  rw [decodeLegacy0_run_of_opcode80 _ _ _ _ rfl f1 (hm 2),
    decodeLegacy0Opcode80_run_of_r6_register _ _ _ _ _ hmod hreg (hm 3) hf f2]
  rfl

theorem xor_r8_imm8_legacy_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (modrm : UInt8) (imm : BitVec 8) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6)
    (hsmall : (gprNumber 0 0 (modrmRm modrm)).toNat < 4)
    (hcode : BytesAt s s.RIP (0x80 :: modrm :: immBytes 8 imm))
    (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    let dst : Operand 8 := .reg (gprNumber 0 0 (modrmRm modrm))
    Machine.step s = some (.next (afterStep s 3 fun t =>
      writeOutputs t dst (xorSpec (oracleBit t.oracle) (dst.read t) (imm.signExtend 8)) 1
        (BitVec.add s.RIP 3#64))) := by
  have hd := decodeLegacy0_run_of_80_r6 s h modrm imm hmod hreg hcode hlow
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (0x80 :: modrm :: immBytes 8 imm) := hcode
  have hl : s.RIP.toNat + (0x80 :: modrm :: immBytes 8 imm).length ≤ 2^32 := by simpa using hlow
  have hi := memFetch_run_of_bytesAt_imm (beforeFetch s) 3 h.fetchReady hc hl 8 (by decide) imm 2
    (immBytes_getElem?_append [0x80, modrm] imm) (by simp) (by decide)
  have hm (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [xor_r8_imm8_form _ _ (BitVec.add s.RIP 2#64) (legacyContext s.DS) (modrmRm modrm) imm (hm 3) (.inr hsmall) rfl hi (hm 4),
    show BitVec.add (BitVec.add s.RIP 2#64) 1#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc _ _ _] at hd
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0x80 (modrm :: immBytes 8 imm)
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hl hd ((hm 4).of_cs_lma_eq rfl rfl)

theorem xor_r8_imm8_legacy_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (imm : BitVec 8) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6)
    (hsmall : (gprNumber 0 0 (modrmRm modrm)).toNat < 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0x80 :: modrm :: immBytes 8 imm))
      (xorR8Imm8Effect p 3 (gprNumber 0 0 (modrmRm modrm)) imm) := by
  rintro s h hcode rfl
  refine ⟨_, xor_r8_imm8_legacy_step s h modrm imm hmod hreg hsmall hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), ReadyToStep.afterStep_writeOutputs h 3 _ _ 1 _,
    ⟨afterStep_writeOutputs_rip h 3 _ _ 1 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ 1 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp [writeOutputs, Operand.read, Operand.write, xorSpec, setFlags,
      afterFetches, beforeFetch, resetStepFields]
  · simp only [BitVec.signExtend_eq]
    exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

@[x86_local] theorem xorR8Imm8Effect_local (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) :
    Effect.Local (xorR8Imm8Effect p len dst imm) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [xorR8Imm8Effect, h.read_reg]
  · intro s
    simp [xorR8Imm8Effect, Write.Full, Operand.Full]

attribute [x86_compose] xorR8Imm8Effect

end P256.Proofs.Common.Instructions.ByteLogic
