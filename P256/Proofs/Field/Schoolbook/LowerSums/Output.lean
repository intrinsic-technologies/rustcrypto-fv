import P256.Proofs.Field.Schoolbook.Products
import P256.Proofs.Field.Schoolbook.Correspondence
import P256.Proofs.Field.Schoolbook.LowerSums.Arithmetic
import P256.Proofs.Field.Schoolbook.LowerSums.Facts

set_option autoImplicit false
namespace P256.Proofs.Field.Schoolbook

open P256.Proofs.Field.Montgomery (wordBase)
open P256.Proofs.Common.Field.Montgomery.Schoolbook
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

private theorem lowerSums_restoreCarry (carry : Bool) :
    (addSpec (if carry then 1#8 else 0#8) 255#8).2.CF = carry := by
  cases carry <;> decide +kernel

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 4096 in
theorem lower_sums_output {s t u : RamState}
    (hp : (productsEffect s).Holds s t) (hl : (lowerSumsEffect t).Holds t u) :
    let a0 := (Operand.mem ((Operand.reg 6 : Operand 64).read s) : Operand 64).read s
    let a1 := (Operand.mem ((Operand.reg 6 : Operand 64).read s+8#64) : Operand 64).read s
    let b0 := (Operand.mem ((Operand.reg 1 : Operand 64).read s) : Operand 64).read s
    let b1 := (Operand.mem ((Operand.reg 1 : Operand 64).read s+8#64) : Operand 64).read s
    let b2 := (Operand.mem ((Operand.reg 1 : Operand 64).read s+16#64) : Operand 64).read s
    let b3 := (Operand.mem ((Operand.reg 1 : Operand 64).read s+24#64) : Operand 64).read s
    upperInputRow u = secondRow
      (firstRow (b0.toNat*a0.toNat) (b1.toNat*a0.toNat) (b2.toNat*a0.toNat) (b3.toNat*a0.toNat))
      (b0.toNat*a1.toNat) (b1.toNat*a1.toNat) (b2.toNat*a1.toNat) (b3.toNat*a1.toNat) := by
  dsimp only
  rw [lowerSums_firstRow, lowerSums_secondRow]
  have hspL : rspOf u = rspOf t := hl.agrees.read (by rw [lowerSums_components]; simp)
  have hoL := hl.obsAfter
    ((((lowerSumsFirst_local.seq lowerSumsSecond_local).seq lowerSumsThird_local).seq lowerSumsFourth_local).full t) true
  have hoP := hp.obsAfter (by simp [productsEffect, Write.Full, Operand.Full]) true
  simp only [upperInputRow, hspL, ← hoL.read_reg, ← hoL.read_mem]
  x86_norm [lowerSumsEffect, lowerSumsMiddleEffect, lowerSumsPrefixEffect,
    lowerSumsFirstEffect, lowerSumsSecondEffect, lowerSumsThirdEffect, lowerSumsFourthEffect,
    savedSource, BitVec.add_zero, Bool.or_eq_false_iff, Bool.or_eq_true_iff]
  simp only [← hoP.read_reg, ← hoP.read_mem]
  x86_norm [productsEffect, BitVec.add_zero, lowerSums_restoreCarry]

structure LowerSumsInputs (s t : RamState) : Prop where
  stack64 : (Operand.mem (rspOf t+64#64) : Operand 64).read t =
    (Operand.mem ((Operand.reg 1 : Operand 64).read s) : Operand 64).read s
  stack72 : (Operand.mem (rspOf t+72#64) : Operand 64).read t =
    (Operand.mem ((Operand.reg 1 : Operand 64).read s+8#64) : Operand 64).read s
  stack40 : (Operand.mem (rspOf t+40#64) : Operand 64).read t =
    (Operand.mem ((Operand.reg 1 : Operand 64).read s+16#64) : Operand 64).read s
  stack56 : (Operand.mem (rspOf t+56#64) : Operand 64).read t =
    (Operand.mem ((Operand.reg 1 : Operand 64).read s+24#64) : Operand 64).read s
  r14 : (Operand.reg 14 : Operand 64).read t =
    (Operand.mem ((Operand.reg 1 : Operand 64).read s+16#64) : Operand 64).read s
  rbx : (Operand.reg 3 : Operand 64).read t =
    (Operand.mem ((Operand.reg 1 : Operand 64).read s+24#64) : Operand 64).read s
  source : savedSource t = (Operand.reg 6 : Operand 64).read s

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 4096 in
theorem lower_sums_inputs {s t u : RamState}
    (hp : (productsEffect s).Holds s t) (hl : (lowerSumsEffect t).Holds t u) :
    LowerSumsInputs s u := by
  have hspL : rspOf u = rspOf t := hl.agrees.read (by rw [lowerSums_components]; simp)
  have hoL := hl.obsAfter
    ((((lowerSumsFirst_local.seq lowerSumsSecond_local).seq lowerSumsThird_local).seq lowerSumsFourth_local).full t) true
  have hoP := hp.obsAfter (by simp [productsEffect, Write.Full, Operand.Full]) true
  constructor
  all_goals simp only [savedSource, hspL, ← hoL.read_reg, ← hoL.read_mem]
  all_goals x86_norm [lowerSumsEffect, lowerSumsMiddleEffect, lowerSumsPrefixEffect,
    lowerSumsFirstEffect, lowerSumsSecondEffect, lowerSumsThirdEffect, lowerSumsFourthEffect,
    savedSource, BitVec.add_zero, Bool.or_eq_false_iff, Bool.or_eq_true_iff]
  all_goals simp only [← hoP.read_reg, ← hoP.read_mem]
  all_goals x86_norm [productsEffect, BitVec.add_zero]

end P256.Proofs.Field.Schoolbook
