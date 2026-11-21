import Sha3.Proofs.Scalar.Condition.Dec.Step
import X86Proofs.Program.Effect

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def decR64Effect (p : BitVec 64) (dst : BitVec 5) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 64).read s
  { rip := p + 3
    writes := [⟨(Operand.reg dst : Operand 64), a - 1⟩]
    flags := some (.ofStatusFlags (decSpec (StatusFlags.ofRFLAGS s.RFLAGS) a).2) }

theorem decR64Effect_components (p : BitVec 64) (dst : BitVec 5) (s : RamState) :
    (decR64Effect p dst s).components = [.reg dst, .flags, .rip] := rfl

theorem decR64Effect_avoids (p : BitVec 64) (dst : BitVec 5) (s : RamState) (code : CodeMap) :
    (decR64Effect p dst s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [decR64Effect_components, Component.Covers]) code

theorem dec_r64_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xFF, modrm])
      (decR64Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, dec_r64_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), dec_r64_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, decSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem dec_r13_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x49, 0xFF, 0xCD])
      (decR64Effect p 13) :=
  dec_r64_effect_step p 0x49 0xCD (by simp [RexWPrefix]) (by decide) (by decide)

theorem dec_rbx_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x48, 0xFF, 0xCB])
      (decR64Effect p 3) :=
  dec_r64_effect_step p 0x48 0xCB (by simp [RexWPrefix]) (by decide) (by decide)

end X86Proofs
