import K256.Proofs.Common.Lift.Eval
import K256.Proofs.Common.Lift.Rep
import K256.Proofs.Ecdh.LIR.Generated.Footprints
import K256.Proofs.Sec1.LIR.Generated.Values
import K256.Proofs.Generate.LIR.Generated.Values
import X86Proofs.Instructions.Bt.Generated.RR.Triple

namespace K256.Proofs.Ecdh.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift

open K256.Proofs.Sec1.LIR K256.Proofs.Generate.LIR

@[cfg_eval] theorem_by btR32R32Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (btR32R32Effect p len dst src t) t' = _ := by lift_value [btR32R32Effect, btFlags]

@[cfg_eval] theorem_by btR32R32Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (btR32R32Effect p len dst src t) t' = _ := by lift_value [btR32R32Effect, btFlags]

@[cfg_eval] theorem btR32R32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (btR32R32Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [btR32R32Effect_components])

end K256.Proofs.Ecdh.LIR
