import Sha2.Proofs.Common.Instructions.Ror.Step
import X86Proofs.Program.Effect
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
import Sha2.Proofs.Common.EffectCompose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def rorR64Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 64).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), a.rotateRight c⟩]
    flags := some (rorFlags (StatusFlags.ofRFLAGS s.RFLAGS) c a) }

@[x86_local] theorem rorR64Effect_local (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) :
    Effect.Local (rorR64Effect p len dst c) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s t h
    simp [rorR64Effect, h.read_reg]
  · intro s t h
    simp [rorR64Effect, h.read_reg]
  · intro s t h
    simp [rorR64Effect, h.read_reg]
  · intro s t h i hi
    cases i <;> simp_all [rorR64Effect, rorFlags, Effect.flag, StatusFlagsOutcome.get,
      StatusFlags.get, StatusFlagsOutcome.ofStatusFlags, h.read_reg] <;> split <;> simp_all
  · intro s
    simp [rorR64Effect, Write.Full, Operand.Full]


@[simp] theorem rorR64Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat)
    (s : RamState) : (rorR64Effect p len dst c s).components = [.reg dst, .flags, .rip] := rfl


theorem rorR64Effect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (s : RamState)
    (code : CodeMap) : (rorR64Effect p len dst c s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code


def rorR32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 32).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), (a.rotateRight c).setWidth 64⟩]
    flags := some (rorFlags (StatusFlags.ofRFLAGS s.RFLAGS) c a) }

@[x86_local] theorem rorR32Effect_local (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) :
    Effect.Local (rorR32Effect p len dst c) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s t h
    simp [rorR32Effect, h.read_reg]
  · intro s t h
    simp [rorR32Effect, h.read_reg]
  · intro s t h
    simp [rorR32Effect, h.read_reg]
  · intro s t h i hi
    cases i <;> simp_all [rorR32Effect, rorFlags, Effect.flag, StatusFlagsOutcome.get,
      StatusFlags.get, StatusFlagsOutcome.ofStatusFlags, h.read_reg] <;> split <;> simp_all
  · intro s
    simp [rorR32Effect, Write.Full, Operand.Full]


@[simp] theorem rorR32Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat)
    (s : RamState) : (rorR32Effect p len dst c s).components = [.reg dst, .flags, .rip] := rfl


theorem rorR32Effect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (s : RamState)
    (code : CodeMap) : (rorR32Effect p len dst c s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code



theorem ror_r64_one_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0xD1, modrm])
      (rorR64Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (1)) := by
  rintro s h hcode rfl
  refine ⟨_, ror_r64_one_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)), ror_r64_one_ready h rex modrm,
    ⟨afterStep_writeOutputs_rip h 3 _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s 3 _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, rorSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · apply rorFlags_allows



end X86Proofs
