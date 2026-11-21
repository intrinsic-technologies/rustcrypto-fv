import P256.Proofs.Verifying.Combination.Naf.Machine.Instructions.ShiftCount.Step
import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Core.Gpr
import X86Proofs.Instructions.Shr.Generated.R.Triple
import P256.Proofs.Common.Instructions.ShiftLeft.Triple
import X86Proofs.Program.Compose

open P256.Proofs.Common.Instructions.ShiftLeft (shlFlags shlFlags_allows shlR64Effect shlR64Effect_avoids shlSpec)

namespace P256.Proofs.Verifying.Combination.Naf.Machine.Instructions.ShiftCount

open X86 X86.Machine X86.UserProcess X86Proofs

def shrR64CLEffect (p : BitVec 64) (dst : BitVec 5) (s : RamState) : Effect :=
  shrR64Effect p 3 dst (clCount s) s

theorem shr_r64_cl_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 5) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xD3, modrm])
      (shrR64CLEffect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, shr_r64_cl_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), shr_r64_cl_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, shrSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply shrFlags_allows

def shlR64CLEffect (p : BitVec 64) (dst : BitVec 5) (s : RamState) : Effect :=
  shlR64Effect p 3 dst (clCount s) s

theorem shl_r64_cl_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xD3, modrm])
      (shlR64CLEffect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, shl_r64_cl_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), shl_r64_cl_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, shlSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply shlFlags_allows

attribute [x86_compose] clCount shrR64CLEffect shlR64CLEffect shrR64Effect shrFlags
  shlR64Effect shlFlags

@[x86_local] theorem shrR64CLEffect_local (p : BitVec 64) (dst : BitVec 5) :
    Effect.Local (shrR64CLEffect p dst) := by
  refine ⟨fun t t' h => ?_, fun t t' h => ?_, fun t t' h => ?_, fun t t' h i hi => ?_,
    fun t => ?_⟩
  · rfl
  · simp [shrR64CLEffect, shrR64Effect, clCount, h.read_reg]
  · rfl
  · cases i <;> simp_all [shrR64CLEffect, shrR64Effect, shrFlags, clCount,
      Effect.flag, StatusFlagsOutcome.get, StatusFlags.get, StatusFlagsOutcome.ofStatusFlags,
      h.read_reg] <;> split <;> simp_all
  · simp [shrR64CLEffect, shrR64Effect, Write.Full, Operand.Full]

@[x86_local] theorem shlR64CLEffect_local (p : BitVec 64) (dst : BitVec 5) :
    Effect.Local (shlR64CLEffect p dst) := by
  refine ⟨fun t t' h => ?_, fun t t' h => ?_, fun t t' h => ?_, fun t t' h i hi => ?_,
    fun t => ?_⟩
  · rfl
  · simp [shlR64CLEffect, shlR64Effect, clCount, h.read_reg]
  · rfl
  · cases i <;> simp_all [shlR64CLEffect, shlR64Effect, shlFlags, clCount,
      Effect.flag, StatusFlagsOutcome.get, StatusFlags.get, StatusFlagsOutcome.ofStatusFlags,
      h.read_reg] <;> split <;> simp_all
  · simp [shlR64CLEffect, shlR64Effect, Write.Full, Operand.Full]

end P256.Proofs.Verifying.Combination.Naf.Machine.Instructions.ShiftCount
