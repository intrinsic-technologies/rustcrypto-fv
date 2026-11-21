import Sha2.Proofs.Common.Instructions.MemoryAlu.AndLoad.Step
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
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

set_option autoImplicit false

namespace Sha2.Proofs.Common.Instructions.MemoryAlu

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

def andR64M64Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : Effect :=
  let addr := am.addr s (p + BitVec.ofNat 64 len)
  let r := (Operand.reg dst : Operand 64).read s &&&
    (Operand.mem addr : Operand 64).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), r⟩]
    flags := some (andFlags r) }

theorem andR64M64Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (am : AddrMode) (s : RamState) :
    (andR64M64Effect p len dst am s).components = [.reg dst, .flags, .rip] := rfl

theorem and_r64_m64_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 8)
      (codeRange p (rex :: 0x23 :: am.modrm reg :: am.tail))
      (andR64M64Effect p (3 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp only [List.length_cons]; omega)
    simp only [List.length_cons] at this
    omega
  have hr := hrex.rexPrefix
  have hstep := X86Proofs.and_r64_m64_step s h rex hrex reg am hv hx hb hcode.bytesAt hlow hread
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteOutputs h _ _ _ _ _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, andSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    rfl
  · simp only [andFlags, andSpec, Operand.read_afterFetches, Operand.read_beforeFetch]
    exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem and_r64_m64_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 8)
      (codeRange p (rex :: 0x23 :: am.modrm reg :: am.tail))
      (Effect.post (andR64M64Effect p (3 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [andR64M64Effect_components]; simp [Component.Covers]) _)
    (and_r64_m64_effect_step p rex hrex reg am hv hx hb)

attribute [x86_compose] andR64M64Effect

@[x86_local] theorem andR64M64Effect_local (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (am : AddrMode) : Effect.Local (andR64M64Effect p len dst am) := by
  apply Sha2.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [andR64M64Effect, AddrMode.addr_obs h, h.read_reg, h.read_mem]
  · intro s
    simp [andR64M64Effect, Write.Full, Operand.Full]

end Sha2.Proofs.Common.Instructions.MemoryAlu
