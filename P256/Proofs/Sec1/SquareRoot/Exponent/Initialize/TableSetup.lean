import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.MoveStep
import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.LeaStep
import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.TableValues

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.ExponentInitialize

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def TableSetupPlan (offset target : Nat) : Prop :=
  Extracted.textBytes.toListFrom offset 3=[0x48,0x89,0xef] ∧
  Extracted.textBytes.toListFrom (offset+3) 8=
    0x48 :: 0x8d :: (AddrMode.sib 4 none 0 (.d32 (BitVec.ofNat 32 target))).modrm 6 ::
      (AddrMode.sib 4 none 0 (.d32 (BitVec.ofNat 32 target))).tail ∧
  Extracted.textBytes.toListFrom (offset+11) 3=[0x48,0x89,0xda] ∧
  Extracted.textBytes.toListFrom (offset+14) 3=[0x4c,0x89,0xf9] ∧
  Extracted.textBytes.toListFrom (offset+17) 3=[0x4d,0x89,0xe8]

instance (offset target : Nat) : Decidable (TableSetupPlan offset target) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

theorem table_setup [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x n : Nat}
    (ctx : ExponentPre s boundary x) (h : TableState s t x n)
    (offset target : Nat) (ht : target<2^31) (bound : offset+20<118431)
    (code : TableSetupPlan offset target) (rip : t.RIP=Extracted.textAddress+BitVec.ofNat 64 offset) :
    ∃ u, Advances boundary 5 t u ∧ TableState s u x n ∧
      u.RIP=Extracted.textAddress+BitVec.ofNat 64 (offset+20) ∧
      u.regValue .rsi=exponentFrameBase s+BitVec.ofNat 64 target ∧
      u.regValue .rdx=exponentFrameBase s+0x2f8 ∧
      u.regValue .rdi=exponentFrameBase s+0x10 ∧
      u.regValue .rcx=s.regValue .rsi+32 ∧ u.regValue .r8=1 := by
  obtain ⟨c1,c2,c3,c4,c5⟩ := code
  have len : (AddrMode.sib 4 none 0 (.d32 (BitVec.ofNat 32 target))).tail.length=5 := rfl
  obtain ⟨t1,a1,f1,ip1,v1,g1,m1⟩ := frame_move_r64 ctx.outerBoundary h.frame
    (offset+0) 0x48 0xef (by simp [RexWPrefix]) rfl (by decide)
    (by simpa only [Nat.add_assoc,Nat.reduceAdd,Nat.add_zero,len] using rip) (by omega) c1
  have val1 := v1.trans h.output
  change AgreesExcept [.reg 7,.rip] t t1 at g1
  obtain ⟨t2,a2,f2,ip2,v2,g2,m2⟩ := frame_lea_r64 ctx.outerBoundary f1
    (offset+3) 0x48 6 (.sib 4 none 0 (.d32 (BitVec.ofNat 32 target)))
    (by simp [RexWPrefix]) (by simp [AddrMode.Valid]) rfl rfl (by decide) ip1
    (by rw [len]; omega) c2
  have val2 : t2.regValue .rsi=exponentFrameBase s+BitVec.ofNat 64 target := by
    change t2.regValue .rsi=stackPtr t1+(BitVec.ofNat 32 target).signExtend 64 at v2
    rw [f1.rsp,signExtend32_offset ht] at v2
    exact v2
  change AgreesExcept [.reg 6,.rip] t1 t2 at g2
  obtain ⟨t3,a3,f3,ip3,v3,g3,m3⟩ := frame_move_r64 ctx.outerBoundary f2
    (offset+11) 0x48 0xda (by simp [RexWPrefix]) rfl (by decide)
    (by simpa only [Nat.add_assoc,Nat.reduceAdd,Nat.add_zero,len] using ip2) (by omega) c3
  have val3 := v3.trans (((g1.trans g2).read (n := 64) (r := 3) (by simp)).trans h.input)
  change AgreesExcept [.reg 2,.rip] t2 t3 at g3
  obtain ⟨t4,a4,f4,ip4,v4,g4,m4⟩ := frame_move_r64 ctx.outerBoundary f3
    (offset+14) 0x4c 0xf9 (by simp [RexWPrefix]) rfl (by decide)
    (by simpa only [Nat.add_assoc,Nat.reduceAdd,Nat.add_zero,len] using ip3) (by omega) c4
  have val4 := v4.trans ((((g1.trans g2).trans g3).read (n := 64) (r := 15) (by simp)).trans h.parameter)
  change AgreesExcept [.reg 1,.rip] t3 t4 at g4
  obtain ⟨t5,a5,f5,ip5,v5,g5,m5⟩ := frame_move_r64 ctx.outerBoundary f4
    (offset+17) 0x4d 0xe8 (by simp [RexWPrefix]) rfl (by decide)
    (by simpa only [Nat.add_assoc,Nat.reduceAdd,Nat.add_zero,len] using ip4) (by omega) c5
  have val5 := v5.trans (((((g1.trans g2).trans g3).trans g4).read (n := 64) (r := 13) (by simp)).trans h.negativeInverse)
  change AgreesExcept [.reg 8,.rip] t4 t5 at g5
  have state := h.of_agrees f5 ((((g1.trans g2).trans g3).trans g4).trans g5) (by simp) (by simp [Component.Covers])
  refine ⟨t5,((((a1.trans a2).trans a3).trans a4).trans a5),state,?_,?_,?_,?_,?_,val5⟩
  · simpa only [Nat.add_assoc,Nat.reduceAdd] using ip5
  · exact (((g3.trans g4).trans g5).read (n := 64) (r := 6) (by simp)).trans val2
  · exact ((g4.trans g5).read (n := 64) (r := 2) (by simp)).trans val3
  · exact ((((g2.trans g3).trans g4).trans g5).read (n := 64) (r := 7) (by simp)).trans val1
  · exact (g5.read (n := 64) (r := 1) (by simp)).trans val4

end P256.Proofs.Sec1.SquareRoot.ExponentInitialize
