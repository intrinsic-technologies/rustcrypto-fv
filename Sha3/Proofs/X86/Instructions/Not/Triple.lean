import Sha3.Proofs.X86.Instructions.Not.Step
import Sha3.Proofs.X86.Instructions.Not.Encode
import X86Proofs.Program.Effect

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def notR64Effect (p : BitVec 64) (dst : BitVec 5) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 64).read s
  { rip := p + 3
    writes := [⟨(Operand.reg dst : Operand 64), ~~~a⟩]
    flags := none }

@[simp] theorem notR64Effect_components (p : BitVec 64) (dst : BitVec 5) (s : RamState) :
    (notR64Effect p dst s).components = [.reg dst, .rip] := rfl

theorem notR64Effect_avoids (p : BitVec 64) (dst : BitVec 5) (s : RamState) (code : CodeMap) :
    (notR64Effect p dst s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

def notR32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 32).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), (~~~a).setWidth 64⟩]
    flags := none }

@[simp] theorem notR32Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (s : RamState) : (notR32Effect p len dst s).components = [.reg dst, .rip] := rfl

theorem notR32Effect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState)
    (code : CodeMap) : (notR32Effect p len dst s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem not_r64_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xF7, modrm])
      (notR64Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, not_r64_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), not_r64_ready h rex modrm,
    ⟨afterStep_writeResult_rip h 3 _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s 3 _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeResult_self, notSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]

theorem not_r64_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0xF7, modrm])
      (Effect.post (notR64Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => notR64Effect_avoids p _ s _)
    (not_r64_effect_step p rex modrm hrex hmod hreg)

theorem not_r32_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xF7, modrm])
      (notR32Effect p 2 (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, not_r32_step s h modrm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), not_r32_ready h modrm,
    ⟨afterStep_writeResult_rip h 2 _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s 2 _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeResult_self32, notSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]

theorem not_r32_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    Triple (fun s => s.RIP = p) (codeRange p [0xF7, modrm])
      (Effect.post (notR32Effect p 2 (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => notR32Effect_avoids p _ _ s _)
    (not_r32_effect_step p modrm hmod hreg)

theorem not_r32_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xF7, modrm])
      (notR32Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, not_r32_rex_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), not_r32_rex_ready h rex modrm,
    ⟨afterStep_writeResult_rip h 3 _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s 3 _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeResult_self32, notSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]

theorem not_r32_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0xF7, modrm])
      (Effect.post (notR32Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => notR32Effect_avoids p _ _ s _)
    (not_r32_rex_effect_step p rex modrm hrex hmod hreg)

theorem not_r64_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeNotR64 dst))
      (Effect.post (notR64Effect p (dst.setWidth 5))) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩ := encodeNotR64_spec dst
  rw [hbytes, ← hdst]
  exact not_r64_triple_of_bytes p rex modrm hrex hmod hreg

theorem not_r32_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeNotR32 dst))
      (Effect.post (notR32Effect p (encodeNotR32 dst).length (dst.setWidth 5))) := by
  rcases encodeNotR32_spec dst with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    exact not_r32_triple_of_bytes p modrm hmod hreg
  · rw [hbytes, ← hdst]
    exact not_r32_rex_triple_of_bytes p rex modrm hrex hmod hreg

end X86Proofs
