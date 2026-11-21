import Sha2.Proofs.Common.SHA256.Absorb.Contract

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb

open X86 X86.Machine X86.UserProcess X86Proofs

theorem prepare_source {l : Layout} {sp : BitVec 64} {s t : RamState}
    (sourceNotCount : l.registers.source ≠ 2)
    (sourceNotRemaining : l.registers.source ≠ l.registers.remaining)
    (effect : (Stage.prepare.effect l sp s).Holds s t) :
    Blocks.readReg t l.registers.source = Blocks.readReg s l.registers.source := by
  apply effect.agrees.read
  simp only [Stage.effect, Blocks.effect, Effect.components, List.map_cons, List.map_nil,
    Write.component, Operand.component, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, not_or]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro h
    have eq := congrArg (fun r : BitVec 5 => r.setWidth 4) (Component.reg.inj h)
    simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 4 ≤ 5), BitVec.setWidth_eq,
      BitVec.reduceSetWidth] at eq
    exact sourceNotCount eq
  · intro h
    have eq := congrArg (fun r : BitVec 5 => r.setWidth 4) (Component.reg.inj h)
    simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 4 ≤ 5),
      BitVec.setWidth_eq] at eq
    exact sourceNotRemaining eq
  all_goals simp

theorem prepare_values {l : Layout} {sp : BitVec 64} {s t : RamState}
    {prior : ByteArray} {input : Sha2.Spec.Program.Input}
    (data : Prepared l sp prior input s)
    (effect : (Stage.prepare.effect l sp s).Holds s t) :
    t.regValue .rdx = BitVec.ofNat 64 (64 - prior.size % 64) ∧
    Blocks.readReg t l.registers.remaining =
      BitVec.ofNat 64 input.bytes.size - BitVec.ofNat 64 (64 - prior.size % 64) ∧
    (StatusFlags.ofRFLAGS t.RFLAGS).CF = decide (input.bytes.size < 64 - prior.size % 64) := by
  have gap : (64 : BitVec 64) - Blocks.readReg s l.registers.tail =
      BitVec.ofNat 64 (64 - prior.size % 64) := by
    rw [data.position]
    exact BitVec.ofNat_sub_ofNat_of_le 64 _ (by omega) (by omega)
  have writes := effect.writes
  change t.regValue .rdx = 64 - Blocks.readReg s l.registers.tail ∧
    Blocks.readReg t l.registers.remaining = Blocks.readReg s l.registers.length -
      (64 - Blocks.readReg s l.registers.tail) at writes
  refine ⟨writes.1.trans gap, writes.2.trans (by rw [data.length, gap]), ?_⟩
  rw [effect.flags.1]
  change (Blocks.readReg s l.registers.length).ult (64 - Blocks.readReg s l.registers.tail) = _
  rw [data.length, gap, BitVec.ult_eq_decide, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := data.messageBound; omega), Nat.mod_eq_of_lt (by omega)]

end Sha2.Proofs.Common.SHA256.Absorb
