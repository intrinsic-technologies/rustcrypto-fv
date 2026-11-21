import P256.Proofs.Verifying.Combination.Naf.Machine.Instructions.AndLoad.Step
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Program.ReadWrite.LoadFlags
import P256.Proofs.Common.EffectCompose

set_option autoImplicit false

open X86Proofs

namespace P256.Proofs.Verifying.Combination.Naf.Machine.Instructions.AndLoad

open X86 X86.Machine X86.UserProcess

def andR64M64Effect (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (s : RamState) : Effect :=
  let r := (Operand.reg dst : Operand 64).read s &&&
    (Operand.mem (am.addr s (p + BitVec.ofNat 64 (movLoadLen am))) : Operand 64).read s
  { rip := p + BitVec.ofNat 64 (movLoadLen am)
    writes := [⟨(Operand.reg dst : Operand 64), r⟩]
    flags := some (andFlags r) }

theorem and_r64_m64_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (movLoadLen am))) 8)
      (codeRange p (rex :: 0x23 :: am.modrm reg :: am.tail))
      (andR64M64Effect p (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  rintro s h hcode ⟨hp, hread⟩
  have hlow := movLoadLen_low hp am hcode
  subst hp
  refine ⟨_, and_r64_m64_step s h rex hrex reg am hv hx hb hcode.bytesAt hlow hread,
    ReadyToStep.afterStep_loadWriteOutputs h _ _ _ _ _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, andSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    rfl
  · exact ⟨rfl, rfl, trivial, rfl, rfl, rfl⟩

attribute [x86_compose] andR64M64Effect

end P256.Proofs.Verifying.Combination.Naf.Machine.Instructions.AndLoad
