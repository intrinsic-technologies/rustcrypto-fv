import Sha3.Proofs.X86.Instructions.MovzxLoad.Step
import Sha3.Proofs.X86.Instructions.MovzxLoad.Encode
import X86Proofs.Instructions.MovLoad.Triple

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def movzxR32M8Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (s : RamState) :
    Effect :=
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      ((Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 8).read s).setWidth 64⟩] }

@[simp] theorem movzxR32M8Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (am : AddrMode) (s : RamState) : (movzxR32M8Effect p len dst am s).components = [.reg dst, .rip] :=
  rfl

theorem movzx_r32_m8_effect_step [Bindings] (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 1)
      (codeRange p (0x0F :: 0xB6 :: am.modrm reg :: am.tail))
      (movzxR32M8Effect p (3 + am.tail.length) (gprNumber 0 0 reg) am) := by
  rintro s h hcode ⟨hp, hread⟩
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    subst hp
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  subst hp
  refine ⟨_, movzx_r32_m8_step s h reg am hv hx hb hcode.bytesAt hlow hread,
    ReadyToStep.afterStep_load h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self32, movzxSpec]
  exact BitVec.setWidth_setWidth (by decide)

theorem movzx_r32_m8_triple_of_bytes [Bindings] (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 1)
      (codeRange p (0x0F :: 0xB6 :: am.modrm reg :: am.tail))
      (Effect.post (movzxR32M8Effect p (3 + am.tail.length) (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s _ =>
    Effect.avoids_of_components_reg_rip (movzxR32M8Effect_components p _ _ am s) _)
    (movzx_r32_m8_effect_step p reg am hv hx hb)

theorem movzx_r_m8_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexPrefix rex.toBitVec) (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : ∀ seg, (rexContext seg rex.toBitVec).operand_size = n) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 1)
      (codeRange p (rex :: 0x0F :: 0xB6 :: am.modrm reg :: am.tail))
      (movzxR32M8Effect p (4 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg)
        am) := by
  rintro s h hcode ⟨hp, hread⟩
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    subst hp
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  subst hp
  refine ⟨_, movzx_r_m8_rex_step s h rex hrex n hn (hsize _) reg am hv hx hb hcode.bytesAt hlow
    hread, ReadyToStep.afterStep_load h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  rcases hn with rfl | rfl
  · simp only [Operand.read_writeResult_self, movzxSpec]
    rfl
  · simp only [Operand.read_writeResult_self32, movzxSpec]
    exact BitVec.setWidth_setWidth (by decide)

theorem movzx_r_m8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexPrefix rex.toBitVec) (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : ∀ seg, (rexContext seg rex.toBitVec).operand_size = n) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 1)
      (codeRange p (rex :: 0x0F :: 0xB6 :: am.modrm reg :: am.tail))
      (Effect.post (movzxR32M8Effect p (4 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg)
        am)) :=
  Triple.of_effect (fun s _ =>
    Effect.avoids_of_components_reg_rip (movzxR32M8Effect_components p _ _ am s) _)
    (movzx_r_m8_rex_effect_step p rex hrex n hn hsize reg am hv hx hb)

theorem movzx_r64_m8_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 1)
      (codeRange p (rex :: 0x0F :: 0xB6 :: am.modrm reg :: am.tail))
      (Effect.post (movzxR32M8Effect p (4 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg)
        am)) :=
  movzx_r_m8_rex_triple_of_bytes p rex hrex.rexPrefix 64 (.inl rfl) hrex.operand_size reg am hv hx hb

theorem movzx_r32_m8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 1)
      (codeRange p (rex :: 0x0F :: 0xB6 :: am.modrm reg :: am.tail))
      (Effect.post (movzxR32M8Effect p (4 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg)
        am)) :=
  movzx_r_m8_rex_triple_of_bytes p rex hrex.rexPrefix 32 (.inr rfl) hrex.operand_size reg am hv hx hb

theorem movzx_r32_m8_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple (LoadPre p (fun s => am.addr s
        (p + BitVec.ofNat 64 (encodeMovzxR32M8 dst am).length)) 1)
      (codeRange p (encodeMovzxR32M8 dst am))
      (Effect.post (movzxR32M8Effect p (encodeMovzxR32M8 dst am).length (dst.setWidth 5) am)) := by
  unfold encodeMovzxR32M8
  split
  · rename_i hlow
    obtain ⟨hr, hx, hb⟩ := hlow
    have := movzx_r32_m8_triple_of_bytes p (regLow dst) am hv hx hb
    rw [← gprNumber_reg, hr]
    simpa only [List.length_cons, show 3 + am.tail.length = am.tail.length + 1 + 1 + 1 by omega]
      using this
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := movzx_r32_m8_rex_triple_of_bytes p _ hrex (regLow dst) am hv hx hb
    rw [hr, gprNumber_reg] at this
    simpa only [List.length_cons, show 4 + am.tail.length = am.tail.length + 1 + 1 + 1 + 1 by omega]
      using this

example : encodeMovzxR32M8 7 (.sib 6 (some 0) 0 .none) = [0x0F, 0xB6, 0x3C, 0x06] := by decide

example : encodeMovzxR32M8 7 (.sib 2 (some 0) 0 .none) = [0x0F, 0xB6, 0x3C, 0x02] := by decide

example : encodeMovzxR32M8 1 (.sib 4 none 0 (.d32 0x1d0)) =
    [0x0F, 0xB6, 0x8C, 0x24, 0xD0, 0x01, 0x00, 0x00] := by decide

end X86Proofs
