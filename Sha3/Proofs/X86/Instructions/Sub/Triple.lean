import Sha3.Proofs.X86.Instructions.Sub.Step
import Sha3.Proofs.X86.Instructions.Sub.Encode
import X86Proofs.Program.Effect

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def subR64R64Effect (p : BitVec 64) (dst src : BitVec 5) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 64).read s
  let b := (Operand.reg src : Operand 64).read s
  { rip := p + 3
    writes := [⟨(Operand.reg dst : Operand 64), a - b⟩]
    flags := some (.ofStatusFlags (subSpec a b).2) }

@[simp] theorem subR64R64Effect_components (p : BitVec 64) (dst src : BitVec 5) (s : RamState) :
    (subR64R64Effect p dst src s).components = [.reg dst, .flags, .rip] := rfl

theorem subR64R64Effect_avoids (p : BitVec 64) (dst src : BitVec 5) (s : RamState)
    (code : CodeMap) : (subR64R64Effect p dst src s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

def subR32R32Effect (p : BitVec 64) (len : Nat) (dst src : BitVec 5) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 32).read s
  let b := (Operand.reg src : Operand 32).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), (a - b).setWidth 64⟩]
    flags := some (.ofStatusFlags (subSpec a b).2) }

@[simp] theorem subR32R32Effect_components (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (s : RamState) : (subR32R32Effect p len dst src s).components = [.reg dst, .flags, .rip] := rfl

theorem subR32R32Effect_avoids (p : BitVec 64) (len : Nat) (dst src : BitVec 5) (s : RamState)
    (code : CodeMap) : (subR32R32Effect p len dst src s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem sub_r64_r64_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0x29, modrm])
      (subR64R64Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, sub_r64_r64_step s h rex modrm hrex hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), sub_r64_r64_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, subSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem sub_r64_r64_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0x29, modrm])
      (Effect.post (subR64R64Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)))) :=
  Triple.of_effect (fun s _ => subR64R64Effect_avoids p _ _ s _)
    (sub_r64_r64_effect_step p rex modrm hrex hmod)

theorem sub_r32_r32_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x29, modrm])
      (subR32R32Effect p 2 (gprNumber 0 0 (modrmRm modrm))
        (gprNumber 0 0 (modrmReg modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, sub_r32_r32_step s h modrm hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), sub_r32_r32_ready h modrm,
    ⟨afterStep_writeOutputs_rip h 2 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 2 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, subSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem sub_r32_r32_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p) (codeRange p [0x29, modrm])
      (Effect.post (subR32R32Effect p 2 (gprNumber 0 0 (modrmRm modrm))
        (gprNumber 0 0 (modrmReg modrm)))) :=
  Triple.of_effect (fun s _ => subR32R32Effect_avoids p _ _ _ s _)
    (sub_r32_r32_effect_step p modrm hmod)

theorem sub_r32_r32_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0x29, modrm])
      (subR32R32Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, sub_r32_r32_rex_step s h rex modrm hrex hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), sub_r32_r32_rex_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ 0 _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ 0 _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, subSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem sub_r32_r32_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0x29, modrm])
      (Effect.post (subR32R32Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)))) :=
  Triple.of_effect (fun s _ => subR32R32Effect_avoids p _ _ _ s _)
    (sub_r32_r32_rex_effect_step p rex modrm hrex hmod)

theorem sub_r64_r64_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeSubR64R64 dst src))
      (Effect.post (subR64R64Effect p (dst.setWidth 5) (src.setWidth 5))) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩ := encodeSubR64R64_spec dst src
  rw [hbytes, ← hdst, ← hsrc]
  exact sub_r64_r64_triple_of_bytes p rex modrm hrex hmod

theorem sub_r32_r32_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeSubR32R32 dst src))
      (Effect.post (subR32R32Effect p (encodeSubR32R32 dst src).length (dst.setWidth 5)
        (src.setWidth 5))) := by
  rcases encodeSubR32R32_spec dst src with ⟨modrm, hbytes, hmod, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact sub_r32_r32_triple_of_bytes p modrm hmod
  · rw [hbytes, ← hdst, ← hsrc]
    exact sub_r32_r32_rex_triple_of_bytes p rex modrm hrex hmod

end X86Proofs
