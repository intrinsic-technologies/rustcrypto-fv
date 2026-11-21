import Sha2.Proofs.Wrapper512.Absorb.Large.Counter.Step
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Xor.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Xor.Generated.M8R8.Triple
import X86Proofs.Program.ReadWrite.Rmw
import X86Proofs.Instructions.Xor.Generated.MR.Step
import X86Proofs.Core.Gpr

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Absorb.Large.Counter

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

def addM64Imm8Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (s : RamState) : Effect :=
  let addr := am.addr s (p + BitVec.ofNat 64 len)
  let out := addSpec ((Operand.mem addr : Operand 64).read s) (imm.signExtend 64)
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem addr : Operand 64), out.1⟩]
    flags := some (.ofStatusFlags out.2) }

theorem add_m64_imm8_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : UInt8) :
    StepEffect (RmwPre p am 8 (4 + am.tail.length))
      (codeRange p (rex :: 0x83 :: am.modrm 0 :: (am.tail ++ [imm])))
      (addM64Imm8Effect p (4 + am.tail.length) am imm.toBitVec) := by
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp only [List.length_cons, List.length_append, List.length_nil]; omega)
    simp only [List.length_cons, List.length_append, List.length_nil] at this
    omega
  have hr := hrex.rexPrefix
  have hstep := add_m64_imm8_step s h [rex] (by simpa using hr.scanPrefix) (by simp)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) am hv
    (by rw [scanContext_rex _ _ hr]; exact AddrContext.rex _ _ am hx hb) imm hcode.bytesAt hlow hread
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 64) s _ (by decide) (by decide) _ _ _ _
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

def adcM64Imm8Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (s : RamState) : Effect :=
  let addr := am.addr s (p + BitVec.ofNat 64 len)
  let out := addSpec ((Operand.mem addr : Operand 64).read s) (BitVec.ofNat 64 (s.RFLAGS.getLsbD 0).toNat)
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem addr : Operand 64), out.1⟩]
    flags := some (.ofStatusFlags out.2) }

theorem adc_m64_imm8_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (RmwPre p am 8 (4 + am.tail.length))
      (codeRange p (rex :: 0x83 :: am.modrm 2 :: (am.tail ++ [0])))
      (adcM64Imm8Effect p (4 + am.tail.length) am) := by
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp only [List.length_cons, List.length_append, List.length_nil]; omega)
    simp only [List.length_cons, List.length_append, List.length_nil] at this
    omega
  have hr := hrex.rexPrefix
  have hstep := adc_m64_imm8_step s h [rex] (by simpa using hr.scanPrefix) (by simp)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) am hv
    (by rw [scanContext_rex _ _ hr]; exact AddrContext.rex _ _ am hx hb) hcode.bytesAt hlow hread
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact Operand.read_afterStep_rmw (n := 64) s _ (by decide) (by decide) _ _ _ _
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

end Sha2.Proofs.Wrapper512.Absorb.Large.Counter
