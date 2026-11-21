import P256.Proofs.Common.Instructions.Imul.Memory.Step
import X86Proofs.Instructions.MovLoad.Triple

set_option autoImplicit false

open X86Proofs

namespace P256.Proofs.Common.Instructions

open X86 X86.Machine X86.UserProcess

def imulR64M64Effect (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 64).read s
  let b := (Operand.mem (am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) : Operand 64).read s
  { rip := p + BitVec.ofNat 64 (4 + am.tail.length)
    writes := [⟨(Operand.reg dst : Operand 64), a * b⟩]
    flags := some (imulFlags64 a b) }

theorem imul_r64_m64_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 8)
      (codeRange p (rex :: 0x0F :: 0xAF :: am.modrm reg :: am.tail))
      (imulR64M64Effect p (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := hcode.low (by simp) (by simp; have := am.tail_length_le; omega)
    simp only [List.length_cons] at this
    omega
  refine ⟨_, imul_r64_m64_step s h rex hrex reg am hv hx hb hcode.bytesAt hlow hread,
    ReadyToStep.afterStep_loadWriteOutputs h _ _ _ _ _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, imulSpec64, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    rfl
  · exact imulFlags64_allows _ _ _

end P256.Proofs.Common.Instructions
