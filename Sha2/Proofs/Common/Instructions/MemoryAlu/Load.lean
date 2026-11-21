import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu.Step
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Xor.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Xor.Generated.M8R8.Triple
import X86Proofs.Program.ReadWrite.Rmw
import X86Proofs.Instructions.Xor.Generated.MR.Step
import X86Proofs.Core.Gpr
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
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

def addR64M64Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : Effect :=
  let addr := am.addr s (p + BitVec.ofNat 64 len)
  let out := addSpec ((Operand.reg dst : Operand 64).read s)
    ((Operand.mem addr : Operand 64).read s)
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), out.1⟩]
    flags := some (.ofStatusFlags out.2) }

theorem addR64M64Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (am : AddrMode) (s : RamState) :
    (addR64M64Effect p len dst am s).components = [.reg dst, .flags, .rip] := rfl

theorem add_r64_m64_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 8)
      (codeRange p (rex :: 0x03 :: am.modrm reg :: am.tail))
      (addR64M64Effect p (3 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp only [List.length_cons]; omega)
    simp only [List.length_cons] at this
    omega
  have hr := hrex.rexPrefix
  have hstep := Sha2.Proofs.Common.SHA256.Compression.add_r_m_step
    s h [rex] (by simpa using hr.scanPrefix) (by simp) 64 (.inl rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) reg am hv
    (by rw [scanContext_rex _ _ hr]; exact AddrContext.rex _ _ am hx hb)
    hcode.bytesAt hlow hread
  simp only [scanContext_rex _ _ hr,
    show (rexContext s.DS rex.toBitVec).rex_r4 = 0 from rfl,
    show (rexContext s.DS rex.toBitVec).rex_r3 = rexR rex.toBitVec from rfl] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteOutputs h _ _ _ _ _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, addSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    rfl
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem add_r64_m64_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 8)
      (codeRange p (rex :: 0x03 :: am.modrm reg :: am.tail))
      (Effect.post (addR64M64Effect p (3 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [addR64M64Effect_components]; simp [Component.Covers]) _)
    (add_r64_m64_effect_step p rex hrex reg am hv hx hb)

attribute [x86_compose] addR64M64Effect

@[x86_local] theorem addR64M64Effect_local (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (am : AddrMode) : Effect.Local (addR64M64Effect p len dst am) := by
  apply Sha2.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [addR64M64Effect, AddrMode.addr_obs h, h.read_reg, h.read_mem]
  · intro s
    simp [addR64M64Effect, Write.Full, Operand.Full]

end Sha2.Proofs.Common.Instructions.MemoryAlu
