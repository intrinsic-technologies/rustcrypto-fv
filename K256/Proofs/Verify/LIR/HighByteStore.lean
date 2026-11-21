import K256.Proofs.Common.Lift.Footprint
import K256.Proofs.Common.Lift.Eval
import X86Proofs.Instructions.Mov.Generated.M8R8.Triple

namespace K256.Proofs.Verify.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift

private theorem readByteReg_get (s : RamState) (r : BitVec 3) :
    (Operand.byteReg r).read s =
      if r.toNat < 4 then ((Reg.gpr (byteRegGpr r)).read s).get 8
      else (((Reg.gpr (byteRegGpr r)).read s).get 64).extractLsb' 8 8 := by
  simp only [Operand.read_byteReg, Reg.read, Value.get, Operand.read_reg64, BitVec.setWidth_eq]

theorem movM8R8NoRexEffect_footprint (p : BitVec 64) (len : Nat) (src : BitVec 3) (am : AddrMode) :
    EffectFootprint p (movM8R8NoRexEffect p len src am) (([.gpr (byteRegGpr src)] : List Reg) ++ addrRegs am) []
      [.rip] :=
  ⟨.ofLocal movM8R8NoRexEffect_local, by lift_reads [movM8R8NoRexEffect, storeEffect, readByteReg_get], by lift_closed, by lift_params,
    by lift_components [movM8R8NoRexEffect, storeEffect_components]⟩

@[cfg_eval ↓] theorem_by movM8R8NoRexEffect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (src : BitVec 3) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 1) (movM8R8NoRexEffect p len src am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [movM8R8NoRexEffect, storeEffect, readByteReg_get]
  · simp only [movM8R8NoRexEffect, storeEffect_components]; rfl

end K256.Proofs.Verify.LIR
