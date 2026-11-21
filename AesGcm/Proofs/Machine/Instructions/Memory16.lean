import AesGcm.Proofs.Copied.X86Proofs.Lift.Eval
import AesGcm.Proofs.Copied.X86Proofs.Lift.Footprint
import X86Proofs.Instructions.Not.Generated.M.Triple
import X86Proofs.Instructions.Rol.Generated.M.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple

namespace AesGcm.Proofs.Machine.Instructions

open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift

theorem xorR16M16Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (xorR16M16Effect p len dst am) (([.gpr dst] : List Reg) ++ addrRegs am) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal xorR16M16Effect_local, by lift_reads [xorR16M16Effect], by lift_closed, by lift_params,
    by lift_components [xorR16M16Effect_components]⟩

@[cfg_eval] theorem_by xorR16M16Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (xorR16M16Effect p len dst am t) t' = _ := by lift_value [xorR16M16Effect]

@[cfg_eval] theorem_by xorR16M16Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (xorR16M16Effect p len dst am t) t' = _ := by lift_value [xorR16M16Effect]

@[cfg_eval] theorem_by xorR16M16Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (xorR16M16Effect p len dst am t) t' = _ := by lift_value [xorR16M16Effect]

@[cfg_eval] theorem_by xorR16M16Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (xorR16M16Effect p len dst am t) t' = _ := by lift_value [xorR16M16Effect]

@[cfg_eval] theorem_by xorR16M16Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (xorR16M16Effect p len dst am t) t' = _ := by lift_value [xorR16M16Effect]

@[cfg_eval] theorem_by xorR16M16Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (xorR16M16Effect p len dst am t) t' = _ := by lift_value [xorR16M16Effect]

@[cfg_eval ↓] theorem xorR16M16Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 2) (xorR16M16Effect p len dst am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 2 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [xorR16M16Effect_components])

theorem xorMREffect16_footprint (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    EffectFootprint p (xorMREffect p len 16 src am) (([.gpr src] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal xorMREffect_local16, by lift_reads [xorMREffect], by lift_closed, by lift_params,
    by lift_components [xorMREffect_components]⟩

@[cfg_eval] theorem_by xorMREffect16_CF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (xorMREffect p len 16 src am t) t' = _ := by lift_value [xorMREffect]

@[cfg_eval] theorem_by xorMREffect16_PF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (xorMREffect p len 16 src am t) t' = _ := by lift_value [xorMREffect]

@[cfg_eval] theorem_by xorMREffect16_ZF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (xorMREffect p len 16 src am t) t' = _ := by lift_value [xorMREffect]

@[cfg_eval] theorem_by xorMREffect16_SF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (xorMREffect p len 16 src am t) t' = _ := by lift_value [xorMREffect]

@[cfg_eval] theorem_by xorMREffect16_OF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (xorMREffect p len 16 src am t) t' = _ := by lift_value [xorMREffect]

@[cfg_eval ↓] theorem_by xorMREffect16_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 2) (xorMREffect p len 16 src am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [xorMREffect]
  · simp only [xorMREffect_components]; rfl

theorem notMEffect16_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) :
    EffectFootprint p (notMEffect p len 16 am) (addrRegs am) []
      [.rip] :=
  ⟨.ofLocal notMEffect_local16, by lift_reads [notMEffect], by lift_closed, by lift_params,
    by lift_components [notMEffect_components]⟩

@[cfg_eval ↓] theorem_by notMEffect16_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 2) (notMEffect p len 16 am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [notMEffect]
  · simp only [notMEffect_components]; rfl

theorem rolMEffect16_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) :
    EffectFootprint p (rolMEffect p len 16 am c) (([.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal rolMEffect_local16, by lift_reads [rolMEffect, rolFlags], by lift_closed, by lift_params,
    by lift_components [rolMEffect_components]⟩

theorem rolMEffect16_fresh (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .OF] : List StatusFlag),
      FlagFresh [] (rolMEffect p len 16 am c) f := by
  lift_fresh [rolMEffect, rolFlags]

@[cfg_eval] theorem_by rolMEffect16_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (rolMEffect p len 16 am c t) t' = _ := by lift_value [rolMEffect, rolFlags]

@[cfg_eval] theorem_by rolMEffect16_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (rolMEffect p len 16 am c t) t' = _ := by lift_value [rolMEffect, rolFlags]

@[cfg_eval] theorem_by rolMEffect16_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (rolMEffect p len 16 am c t) t' = _ := by lift_value [rolMEffect, rolFlags]

@[cfg_eval] theorem_by rolMEffect16_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (rolMEffect p len 16 am c t) t' = _ := by lift_value [rolMEffect, rolFlags]

@[cfg_eval] theorem_by rolMEffect16_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (rolMEffect p len 16 am c t) t' = _ := by lift_value [rolMEffect, rolFlags]

@[cfg_eval] theorem_by rolMEffect16_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (rolMEffect p len 16 am c t) t' = _ := by lift_value [rolMEffect, rolFlags]

@[cfg_eval ↓] theorem_by rolMEffect16_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 2) (rolMEffect p len 16 am c) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [rolMEffect, rolFlags]
  · simp only [rolMEffect_components]; rfl

end AesGcm.Proofs.Machine.Instructions
