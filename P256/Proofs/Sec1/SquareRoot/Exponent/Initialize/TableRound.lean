import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.TableSetup

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.ExponentInitialize

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def TableRoundPlan (offset n : Nat) (disp : BitVec 32) : Prop :=
  TableSetupPlan offset (160+32*n) ∧
  Extracted.textBytes.toListFrom (offset+20) 5=encodeCallRel32 disp ∧
  branchTarget (Extracted.textAddress+BitVec.ofNat 64 (offset+20)) 5 (disp.signExtend 64)=0x1145e0 ∧
  TableCopyPlan (offset+25) (160+32*(n+1))

instance (offset n : Nat) (disp : BitVec 32) : Decidable (TableRoundPlan offset n disp) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem table_round [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x n : Nat}
    (ctx : ExponentPre s boundary x) (h : TableState s t x (n+1)) (hn : n<15)
    (offset : Nat) (disp : BitVec 32) (bound : offset+77<118431)
    (code : TableRoundPlan offset n disp) (rip : t.RIP=Extracted.textAddress+BitVec.ofNat 64 offset) :
    ∃ u fuel, Advances boundary fuel t u ∧ TableState s u x (n+2) ∧
      u.RIP=Extracted.textAddress+BitVec.ofNat 64 (offset+77) := by
  obtain ⟨setup,call,target,copy⟩ := code
  obtain ⟨v,a1,h1,ip1,si,dx,di,cx,r8⟩ := table_setup ctx h offset (160+32*n)
    (by omega) (by omega) setup rip
  obtain ⟨w,fuel,a2,h2,ip2,value,_⟩ := table_multiply_call ctx h1 hn (offset+20) disp
    (by omega) call target ip1 si dx di cx r8
  obtain ⟨u,a3,h3,ip3,_⟩ := copy_table_entry ctx h2 (by omega) value (offset+25)
    (by omega) copy (by simpa only [Nat.add_assoc,Nat.reduceAdd] using ip2)
  exact ⟨u,5+fuel+8,(a1.trans a2).trans a3,h3,by
    simpa only [Nat.add_assoc,Nat.reduceAdd] using ip3⟩

end P256.Proofs.Sec1.SquareRoot.ExponentInitialize
