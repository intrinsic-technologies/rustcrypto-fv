import Sha3.Proofs.X86.Instructions.XorLoad.Step
import Sha3.Proofs.X86.Instructions.XorLoad.Encode
import X86Proofs.Instructions.MovLoad.Triple
import Sha3.Proofs.X86.Instructions.Xor.Triple

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def xorR64M64Effect (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (s : RamState) : Effect :=
  let r := (Operand.reg dst : Operand 64).read s ^^^
    (Operand.mem (am.addr s (p + BitVec.ofNat 64 (movLoadLen am))) : Operand 64).read s
  { rip := p + BitVec.ofNat 64 (movLoadLen am)
    writes := [⟨(Operand.reg dst : Operand 64), r⟩]
    flags := some (xorFlags r) }

def xorR32M32Effect (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (s : RamState) : Effect :=
  let r := (Operand.reg dst : Operand 32).read s ^^^
    (Operand.mem (am.addr s (p + BitVec.ofNat 64 (movLoadLen am))) : Operand 32).read s
  { rip := p + BitVec.ofNat 64 (movLoadLen am)
    writes := [⟨(Operand.reg dst : Operand 64), r.setWidth 64⟩]
    flags := some (xorFlags r) }

@[simp] theorem xorR64M64Effect_components (p : BitVec 64) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : (xorR64M64Effect p dst am s).components = [.reg dst, .flags, .rip] := rfl

@[simp] theorem xorR32M32Effect_components (p : BitVec 64) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : (xorR32M32Effect p dst am s).components = [.reg dst, .flags, .rip] := rfl

theorem xor_r64_m64_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (movLoadLen am))) 8)
      (codeRange p (rex :: 0x33 :: am.modrm reg :: am.tail))
      (xorR64M64Effect p (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  rintro s h hcode ⟨hp, hread⟩
  have hlow := movLoadLen_low hp am hcode
  subst hp
  refine ⟨_, xor_r64_m64_step s h rex hrex reg am hv hx hb hcode.bytesAt hlow hread,
    ReadyToStep.afterStep_loadWriteOutputs h _ _ _ _ _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, xorSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    rfl
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem xor_r64_m64_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (movLoadLen am))) 8)
      (codeRange p (rex :: 0x33 :: am.modrm reg :: am.tail))
      (Effect.post (xorR64M64Effect p (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [xorR64M64Effect_components]; simp [Component.Covers]) _)
    (xor_r64_m64_effect_step p rex hrex reg am hv hx hb)

theorem xor_r32_m32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (movLoadLen am))) 4)
      (codeRange p (rex :: 0x33 :: am.modrm reg :: am.tail))
      (xorR32M32Effect p (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  rintro s h hcode ⟨hp, hread⟩
  have hlow := movLoadLen_low hp am hcode
  subst hp
  refine ⟨_, xor_r32_m32_step s h rex hrex reg am hv hx hb hcode.bytesAt hlow hread,
    ReadyToStep.afterStep_loadWriteOutputs h _ _ _ _ _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, xorSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    rfl
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

theorem xor_r32_m32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (movLoadLen am))) 4)
      (codeRange p (rex :: 0x33 :: am.modrm reg :: am.tail))
      (Effect.post (xorR32M32Effect p (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [xorR32M32Effect_components]; simp [Component.Covers]) _)
    (xor_r32_m32_effect_step p rex hrex reg am hv hx hb)

theorem xor_r64_m64_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (movLoadLen am))) 8)
      (codeRange p (encodeXorR64M64 dst am))
      (Effect.post (xorR64M64Effect p (dst.setWidth 5) am)) := by
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec dst
  have := xor_r64_m64_triple_of_bytes p _ hrex (regLow dst) am hv hx hb
  rwa [hr, gprNumber_reg] at this

example : encodeXorR64M64 8 (.sib 4 none 0 .none) = [0x4C, 0x33, 0x04, 0x24] := by decide

example : encodeXorR64M64 3 (.sib 4 none 0 (.d8 0x38)) = [0x48, 0x33, 0x5C, 0x24, 0x38] := by
  decide

example : encodeXorR64M64 6 (.sib 4 none 0 (.d8 0xb8)) = [0x48, 0x33, 0x74, 0x24, 0xB8] := by
  decide

example : encodeXorR64M64 15 (.sib 4 none 0 (.d8 0x80)) = [0x4C, 0x33, 0x7C, 0x24, 0x80] := by
  decide

example : encodeXorR64M64 3 (.base 6 (.d32 0x2000c0)) =
    [0x48, 0x33, 0x9E, 0xC0, 0x00, 0x20, 0x00] := by decide

end X86Proofs
