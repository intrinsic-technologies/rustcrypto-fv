import P256.Proofs.Common.Instructions.AddByte.Memory.Step
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Xor.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Xor.Generated.M8R8.Triple
import X86Proofs.Program.ReadWrite.Rmw
import X86Proofs.Instructions.Xor.Generated.MR.Step
import X86Proofs.Core.Gpr

set_option autoImplicit false

namespace P256.Proofs.Common.Instructions.AddByte

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

def addM8Imm8Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8)
    (s : RamState) : Effect :=
  let addr := am.addr s (p + BitVec.ofNat 64 len)
  let out := addSpec ((Operand.mem addr : Operand 8).read s) imm
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem addr : Operand 8), out.1⟩]
    flags := some (.ofStatusFlags out.2) }

theorem addM8Imm8Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode)
    (imm : BitVec 8) (s : RamState) :
    (addM8Imm8Effect p len am imm s).components =
      [.mem (am.addr s (p + BitVec.ofNat 64 len)) 1, .flags, .rip] := by
  simp [addM8Imm8Effect, Effect.components]

theorem add_m8_imm8_effect_step [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : UInt8) :
    StepEffect (RmwPre p am 1 (3 + am.tail.length))
      (codeRange p (0x80 :: am.modrm 0 :: (am.tail ++ [imm])))
      (addM8Imm8Effect p (3 + am.tail.length) am imm.toBitVec) := by
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append] at this
    omega
  have hstep := add_m8_imm8_step s h [] (by simp) (by simp) rfl rfl rfl am hv
    (AddrContext.legacy _ am hx hb) imm hcode.bytesAt hlow hread
  simp only [BitVec.signExtend_eq] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 8) s _ (by decide) (by decide) _ _ _ _
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

end P256.Proofs.Common.Instructions.AddByte
