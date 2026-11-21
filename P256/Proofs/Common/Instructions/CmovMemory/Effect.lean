import P256.Proofs.Common.Instructions.CmovMemory.Step

set_option autoImplicit false

open X86Proofs

namespace P256.Proofs.Common.Instructions

open X86 X86.Machine X86.UserProcess

def cmovR32M32Effect (p : BitVec 64) (len : Nat) (cc : BitVec 4) (dst : BitVec 5)
    (am : AddrMode) (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      (cmovR32M32Value cc dst (am.addr s (p + BitVec.ofNat 64 len)) s).setWidth 64⟩] }

theorem cmov_r32_m32_effect_step [Bindings] (p : BitVec 64)
    (op : UInt8) (hop : op = 0x42 ∨ op = 0x44 ∨ op = 0x45)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 4)
      (codeRange p (0x0f :: op :: am.modrm reg :: am.tail))
      (cmovR32M32Effect p (3 + am.tail.length) (op.toBitVec.extractLsb' 0 4)
        (gprNumber 0 0 reg) am) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp only [List.length_cons]; omega)
    simp only [List.length_cons] at this
    omega
  refine ⟨_, cmov_r32_m32_step s h op hop reg am hv hx hb hcode.bytesAt hlow hread,
    ReadyToStep.afterStep_load h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep, Operand.read_writeResult_self32]
  rfl

theorem cmov_r32_m32_rex_effect_step [Bindings] (p : BitVec 64) (rex op : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hop : op = 0x42 ∨ op = 0x44 ∨ op = 0x45)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 4)
      (codeRange p (rex :: 0x0f :: op :: am.modrm reg :: am.tail))
      (cmovR32M32Effect p (4 + am.tail.length) (op.toBitVec.extractLsb' 0 4)
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp only [List.length_cons]; omega)
    simp only [List.length_cons] at this
    omega
  refine ⟨_, cmov_r32_m32_rex_step s h rex op hrex hop reg am hv hx hb hcode.bytesAt hlow hread,
    ReadyToStep.afterStep_load h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep, Operand.read_writeResult_self32]
  rfl

theorem cmove_r12d_rsp68_effect_step [Bindings] (p : BitVec 64) :
    let am : AddrMode := .sib 4 none 0 (.d8 0x68)
    StepEffect (LoadPre p (fun s => am.addr s (p + 6)) 4)
      (codeRange p [0x44, 0x0f, 0x44, 0x64, 0x24, 0x68])
      (cmovR32M32Effect p 6 4 12 am) := by
  exact cmov_r32_m32_rex_effect_step p 0x44 0x44 (by simp [RexNoWPrefix])
    (Or.inr (Or.inl rfl)) 4 (.sib 4 none 0 (.d8 0x68)) (by simp [AddrMode.Valid]) rfl rfl

theorem cmove_ecx_rsp2c0_effect_step [Bindings] (p : BitVec 64) :
    let am : AddrMode := .sib 4 none 0 (.d32 0x2c0)
    StepEffect (LoadPre p (fun s => am.addr s (p + 8)) 4)
      (codeRange p [0x0f, 0x44, 0x8c, 0x24, 0xc0, 0x02, 0x00, 0x00])
      (cmovR32M32Effect p 8 4 1 am) := by
  exact cmov_r32_m32_effect_step p 0x44 (Or.inr (Or.inl rfl)) 1
    (.sib 4 none 0 (.d32 0x2c0)) (by simp [AddrMode.Valid]) rfl rfl

end P256.Proofs.Common.Instructions
