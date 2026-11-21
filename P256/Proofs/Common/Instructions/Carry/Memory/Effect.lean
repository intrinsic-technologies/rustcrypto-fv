import P256.Proofs.Common.Instructions.Carry.Memory.Step
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Program.ReadWrite.LoadFlags

set_option autoImplicit false

namespace P256.Proofs.Common.Instructions.Carry

open X86 X86.Machine X86.UserProcess X86Proofs

def adcR64M64Effect (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 64).read s
  let b := (Operand.mem (am.addr s (p + BitVec.ofNat 64 (movLoadLen am))) : Operand 64).read s
  let out := adcSpec a b (s.RFLAGS.extractLsb' 0 1)
  { rip := p + BitVec.ofNat 64 (movLoadLen am)
    writes := [⟨(Operand.reg dst : Operand 64), out.1⟩]
    flags := some (.ofStatusFlags out.2) }

theorem adcR64M64Effect_components (p : BitVec 64) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : (adcR64M64Effect p dst am s).components = [.reg dst, .flags, .rip] := rfl

theorem adcR64M64Effect_avoids (p : BitVec 64) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) (code : CodeMap) : (adcR64M64Effect p dst am s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [adcR64M64Effect_components, Component.Covers]) code

theorem adc_r64_m64_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (movLoadLen am))) 8)
      (codeRange p (rex :: 0x13 :: am.modrm reg :: am.tail))
      (adcR64M64Effect p (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  rintro s h hcode ⟨hp, hread⟩
  have hlow := movLoadLen_low hp am hcode
  subst hp
  refine ⟨_, adc_r64_m64_step s h rex hrex reg am hv hx hb hcode.bytesAt hlow hread,
    ReadyToStep.afterStep_loadWriteOutputs h _ _ _ _ _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, adcSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    rfl
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

def sbbR64M64Effect (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 64).read s
  let b := (Operand.mem (am.addr s (p + BitVec.ofNat 64 (movLoadLen am))) : Operand 64).read s
  let out := sbbSpec a b (s.RFLAGS.extractLsb' 0 1)
  { rip := p + BitVec.ofNat 64 (movLoadLen am)
    writes := [⟨(Operand.reg dst : Operand 64), out.1⟩]
    flags := some (.ofStatusFlags out.2) }

end P256.Proofs.Common.Instructions.Carry
