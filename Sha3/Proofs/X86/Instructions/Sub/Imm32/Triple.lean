import Sha3.Proofs.X86.Instructions.Sub.Imm32.Step
import Sha3.Proofs.X86.Instructions.Sub.Imm32.Encode
import X86Proofs.Program.Effect

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def subR64Imm32Effect (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 64).read s
  let b := imm.signExtend 64
  { rip := p + 7
    writes := [⟨(Operand.reg dst : Operand 64), a - b⟩]
    flags := some (.ofStatusFlags (subSpec a b).2) }

@[simp] theorem subR64Imm32Effect_components (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32)
    (s : RamState) :
    (subR64Imm32Effect p dst imm s).components = [.reg dst, .flags, .rip] := rfl

theorem subR64Imm32Effect_avoids (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (s : RamState)
    (code : CodeMap) : (subR64Imm32Effect p dst imm s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem sub_r64_imm32_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (imm : BitVec 32) (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 5) :
    StepEffect (fun s => s.RIP = p) (codeRange p (rex :: 0x81 :: modrm :: immBytes 32 imm))
      (subR64Imm32Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm) := by
  rintro s h hcode rfl
  refine ⟨_, sub_r64_imm32_step s h rex modrm imm hrex hmod hreg hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), sub_r64_imm32_ready h rex modrm imm,
    ⟨afterStep_writeOutputs_rip h 7 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 7 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, subSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem sub_r64_imm32_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (imm : BitVec 32) (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 5) :
    Triple (fun s => s.RIP = p) (codeRange p (rex :: 0x81 :: modrm :: immBytes 32 imm))
      (Effect.post (subR64Imm32Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => subR64Imm32Effect_avoids p _ _ s _)
    (sub_r64_imm32_effect_step p rex modrm imm hrex hmod hreg)

theorem sub_r64_imm32_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 32) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeSubR64Imm32 dst imm))
      (Effect.post (subR64Imm32Effect p (dst.setWidth 5) imm)) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩ := encodeSubR64Imm32_spec dst imm
  rw [hbytes, ← hdst]
  exact sub_r64_imm32_triple_of_bytes p rex modrm imm hrex hmod hreg

def subR32Imm32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 32).read s
  let b := imm.signExtend 32
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), (a - b).setWidth 64⟩]
    flags := some (.ofStatusFlags (subSpec a b).2) }

@[simp] theorem subR32Imm32Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32)
    (s : RamState) :
    (subR32Imm32Effect p len dst imm s).components = [.reg dst, .flags, .rip] := rfl

theorem subR32Imm32Effect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (s : RamState)
    (code : CodeMap) : (subR32Imm32Effect p len dst imm s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem sub_r32_imm32_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (imm : BitVec 32) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 5) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0x81 :: modrm :: immBytes 32 imm))
      (subR32Imm32Effect p 6 (gprNumber 0 0 (modrmRm modrm)) imm) := by
  rintro s h hcode rfl
  refine ⟨_, sub_r32_imm32_step s h modrm imm hmod hreg hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), sub_r32_imm32_ready h modrm imm,
    ⟨afterStep_writeOutputs_rip h 6 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 6 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, subSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem sub_r32_imm32_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (imm : BitVec 32) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 5) :
    Triple (fun s => s.RIP = p) (codeRange p (0x81 :: modrm :: immBytes 32 imm))
      (Effect.post (subR32Imm32Effect p 6 (gprNumber 0 0 (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => subR32Imm32Effect_avoids p _ _ _ s _)
    (sub_r32_imm32_effect_step p modrm imm hmod hreg)

theorem sub_r32_imm32_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (imm : BitVec 32) (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 5) :
    StepEffect (fun s => s.RIP = p) (codeRange p (rex :: 0x81 :: modrm :: immBytes 32 imm))
      (subR32Imm32Effect p 7 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm) := by
  rintro s h hcode rfl
  refine ⟨_, sub_r32_imm32_rex_step s h rex modrm imm hrex hmod hreg hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), sub_r32_imm32_rex_ready h rex modrm imm,
    ⟨afterStep_writeOutputs_rip h 7 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 7 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, subSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem sub_r32_imm32_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (imm : BitVec 32) (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 5) :
    Triple (fun s => s.RIP = p) (codeRange p (rex :: 0x81 :: modrm :: immBytes 32 imm))
      (Effect.post (subR32Imm32Effect p 7 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => subR32Imm32Effect_avoids p _ _ _ s _)
    (sub_r32_imm32_rex_effect_step p rex modrm imm hrex hmod hreg)

theorem sub_r32_imm32_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 32) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeSubR32Imm32 dst imm))
      (Effect.post (subR32Imm32Effect p (encodeSubR32Imm32 dst imm).length (dst.setWidth 5) imm)) := by
  rcases encodeSubR32Imm32_spec dst imm with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    simpa using sub_r32_imm32_triple_of_bytes p modrm imm hmod hreg
  · rw [hbytes, ← hdst]
    simpa using sub_r32_imm32_rex_triple_of_bytes p rex modrm imm hrex hmod hreg

end X86Proofs
