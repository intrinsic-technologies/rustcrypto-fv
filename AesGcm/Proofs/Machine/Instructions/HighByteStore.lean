import AesGcm.Proofs.Copied.X86Proofs.Lift.Eval
import AesGcm.Proofs.Copied.X86Proofs.Lift.Footprint
import X86Proofs.Instructions.Mov.Generated.M8R8.Triple

namespace AesGcm.Proofs.Machine.Instructions

open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift

@[cfg_eval] theorem Operand.read_byteReg_get (t : RamState) (src : BitVec 3) :
    (Operand.byteReg src).read t =
      if src.toNat < 4 then ((Reg.gpr ((src.setWidth 2).setWidth 5)).read t).get 8
      else (((Reg.gpr ((src.setWidth 2).setWidth 5)).read t).get 64).extractLsb' 8 8 := by
  rw [Operand.read_byteReg]
  simp [byteRegGpr, Reg.read, Value.get, Operand.read]

theorem movM8R8NoRexEffect_footprint (p : BitVec 64) (len : Nat) (src : BitVec 3)
    (am : AddrMode) :
    EffectFootprint p (movM8R8NoRexEffect p len src am)
      (([.gpr ((src.setWidth 2).setWidth 5)] : List Reg) ++ addrRegs am) [] [.rip] :=
  ⟨.ofLocal movM8R8NoRexEffect_local,
    by lift_reads [movM8R8NoRexEffect, storeEffect, Operand.read_byteReg_get],
    by lift_closed, by lift_params,
    by lift_components [movM8R8NoRexEffect, storeEffect_components]⟩

@[cfg_eval ↓] theorem_by movM8R8NoRexEffect_exec (code : CodeMap) (p : BitVec 64)
    (len : Nat) (src : BitVec 3) (am : AddrMode) (R : List Reg)
    (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p
      (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 1)
      (movM8R8NoRexEffect p len src am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [movM8R8NoRexEffect, storeEffect, Operand.read_byteReg_get]
  · simp only [movM8R8NoRexEffect, storeEffect_components]
    rfl

end AesGcm.Proofs.Machine.Instructions
