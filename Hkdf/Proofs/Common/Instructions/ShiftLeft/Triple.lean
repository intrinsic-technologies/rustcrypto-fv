import Hkdf.Proofs.Common.Instructions.ShiftLeft.Step
import Hkdf.Proofs.Common.Instructions.ShiftLeft.Encode
import X86Proofs.Program.Effect
import X86Proofs.Step.FetchImm

namespace Hkdf.Proofs.Common.Instructions.ShiftLeft

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

def shlR64Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 64).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), a <<< c⟩]
    flags := some (shlFlags (StatusFlags.ofRFLAGS s.RFLAGS) c a) }

theorem shlR64Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat)
    (s : RamState) : (shlR64Effect p len dst c s).components = [.reg dst, .flags, .rip] := rfl

theorem shlR64Effect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (s : RamState)
    (code : CodeMap) : (shlR64Effect p len dst c s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [shlR64Effect_components, Component.Covers]) code

theorem shl_r64_imm8_effect_step [Bindings] (p : BitVec 64) (rex modrm imm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xC1, modrm, imm])
      (shlR64Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (shiftCount 64 imm.toBitVec)) := by
  rintro s h hcode rfl
  refine ⟨_, shl_r64_imm8_step s h rex modrm imm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), shl_r64_imm8_ready h rex modrm imm,
    ⟨afterStep_writeOutputs_rip h 4 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, shlSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply shlFlags_allows

theorem shl_r64_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm imm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0xC1, modrm, imm])
      (Effect.post (shlR64Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (shiftCount 64 imm.toBitVec))) :=
  Triple.of_effect (fun s _ => shlR64Effect_avoids p _ _ _ s _)
    (shl_r64_imm8_effect_step p rex modrm imm hrex hmod hreg)

theorem shl_r64_imm8_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeShlR64Imm8 dst imm))
      (Effect.post (shlR64Effect p
        4 (dst.setWidth 5)
        (shiftCount 64 imm))) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩ := encodeShlR64Imm8_spec imm dst
  rw [hbytes, ← hdst, immBytes_eight]
  exact shl_r64_imm8_triple_of_bytes p rex modrm (UInt8.ofBitVec imm) hrex hmod hreg

end Hkdf.Proofs.Common.Instructions.ShiftLeft
