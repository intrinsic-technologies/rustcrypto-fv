import Md5.Proofs.Block.Shl
import Md5.Proofs.Block.Rounds.Register.Or

namespace Md5.Proofs.Buffered.FinalizeReset.Length

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs
open Md5.Proofs.Block Md5.Proofs.Block.Rounds.Register

theorem shl_r32_imm8_rex_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (rex modrm imm : UInt8) (hrex : RexNoWPrefix rex.toBitVec)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4)
    (hcode : BytesAt s s.RIP [rex, 0xC1, modrm, imm]) (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    let dst : Operand 32 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    let c := shiftCount 32 imm.toBitVec
    X86.Machine.step s = some (.next (afterStep s 4 fun t ↦
      writeOutputs t dst (shlSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (shrOracleAF t.oracle c) c (dst.read t))
        (shrOracleBits c) (BitVec.add s.RIP 4#64))) := by
  have hdecode := decodeLegacy0_run_of_rex_C1_shl s h rex modrm imm hmod hreg hcode hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have himm : (Mem_Fetch (BitVec.add s.RIP 3#64) 8).run (afterFetches (beforeFetch s) 4) =
      (.ok imm.toBitVec, afterFetches (beforeFetch s) 5) :=
    memFetch_run_of_bytesAt (beforeFetch s) 4 h.fetchReady hcode hlow 3 (by simp) (by decide)
  rw [shl_r_imm8_form _ _ _ _ _ _ (hmode 4) himm (hmode 5) 32 (by decide)
    (hrex.operand_size s.DS) rfl,
    show BitVec.add (BitVec.add s.RIP 3#64) 1#64 = BitVec.add s.RIP 4#64 from
      BitVec.add_assoc s.RIP 3#64 1#64] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex 0xC1 [modrm, imm] hrex.rexPrefix
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode ((hmode 5).of_cs_lma_eq rfl rfl)

def shlR32Effect (p : BitVec 64) (dst : BitVec 5) (c : Nat) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 32).read s
  { rip := p + 4
    writes := [⟨(Operand.reg dst : Operand 64), (a <<< c).setWidth 64⟩]
    flags := some (shlFlags (StatusFlags.ofRFLAGS s.RFLAGS) c a) }

theorem shl_r32_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm imm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p [rex, 0xC1, modrm, imm])
      (shlR32Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (shiftCount 32 imm.toBitVec)) := by
  rintro s h hcode rfl
  refine ⟨_, shl_r32_imm8_rex_step s h rex modrm imm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), ReadyToStep.afterStep_writeOutputs h 4 _ _ _ _,
    ⟨afterStep_writeOutputs_rip h 4 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 4 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, shlSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply shlFlags_allows

theorem or_r64_r64_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP [rex, 0x09, modrm]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    let dst : Operand 64 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    let src : Operand 64 := .reg (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
    X86.Machine.step s = some (.next (afterStep s 3 fun t ↦
      writeOutputs t dst (orSpec (oracleBit t.oracle) (dst.read t) (src.read t)) 1
        (BitVec.add s.RIP 3#64))) := by
  have hdecode := decodeLegacy0_run_of_rex_09 s h rex modrm hmod hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 4) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [or_r_r_form _ _ _ _ _ hmode 64 (by decide)
    (hrex.operand_size s.DS) rfl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex 0x09 [modrm] hrex.rexPrefix
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)

def orR64R64Effect (p : BitVec 64) (dst src : BitVec 5) (s : RamState) : Effect :=
  let r := (Operand.reg dst : Operand 64).read s ||| (Operand.reg src : Operand 64).read s
  { rip := p + 3
    writes := [⟨(Operand.reg dst : Operand 64), r⟩]
    flags := some (andFlags r) }

theorem or_r64_r64_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s ↦ s.RIP = p) (codeRange p [rex, 0x09, modrm])
      (orR64R64Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, or_r64_r64_step s h rex modrm hrex hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), ReadyToStep.afterStep_writeOutputs h 3 _ _ 1 _,
    ⟨afterStep_writeOutputs_rip h 3 _ _ 1 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ 1 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, orSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

attribute [x86_compose] shlR32Effect orR64R64Effect

@[x86_local] theorem shlR32Effect_local {p : BitVec 64} {dst : BitVec 5} {c : Nat} :
    Effect.Local (shlR32Effect p dst c) := by
  refine ⟨fun _ _ _ ↦ rfl, fun t t' h ↦ ?_, fun _ _ _ ↦ rfl,
    fun t t' h i hi ↦ ?_, fun _ ↦ ?_⟩
  · simp only [shlR32Effect, h.read_reg]
  · cases i <;> simp_all [shlR32Effect, Effect.flag, StatusFlagsOutcome.get,
      StatusFlags.get, StatusFlagsOutcome.ofStatusFlags, shlFlags, h.read_reg] <;>
      split <;> simp_all
  · simp [shlR32Effect, Write.Full, Operand.Full]

@[x86_local] theorem orR64R64Effect_local {p : BitVec 64} {dst src : BitVec 5} :
    Effect.Local (orR64R64Effect p dst src) := by
  refine ⟨fun _ _ _ ↦ rfl, fun t t' h ↦ ?_, fun _ _ _ ↦ rfl,
    fun t t' h i hi ↦ ?_, fun _ ↦ ?_⟩
  · simp only [orR64R64Effect, h.read_reg]
  · cases i <;> simp_all [orR64R64Effect, Effect.flag, StatusFlagsOutcome.get,
      StatusFlags.get, andFlags, h.read_reg]
  · simp [orR64R64Effect, Write.Full, Operand.Full]

end Md5.Proofs.Buffered.FinalizeReset.Length
