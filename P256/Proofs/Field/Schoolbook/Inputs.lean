import P256.Proofs.Field.Schoolbook.Preconditions
import P256.Proofs.Field.Schoolbook.Bytes
import P256.Proofs.Field.Schoolbook.LowerSums.Facts

open P256.Proofs.SecretKeyFromBytes.Scalar

set_option autoImplicit false

namespace P256.Proofs.Field.Schoolbook

open P256.Proofs.Field.Montgomery (wordBase)
open P256.Proofs.Common.Field.Montgomery.Schoolbook

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem nat256_limb_toNat {s : RamState} {address : BitVec 64} {value : Nat}
    (h : Nat256At s address value) (j : Nat) (hj : j < 4) :
    (memLoad s.external (address+BitVec.ofNat 64 (8*j)) 64).toNat = (limbsOfNat value)[j] := by
  rw [h.memLoad_limb j hj, BitVec.toNat_ofNat]
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases hj' with rfl | rfl | rfl | rfl
  · simp [limbsOfNat, wordBase]
  · rfl
  · rfl
  · rfl

theorem entry_inputs [Bindings] {s entry : RamState} {boundary : ReturnBoundary}
    (ctx : ExecutionContext s boundary entry) {a b : Nat}
    (ha : Nat256At s (s.regValue .rsi) a) (hb : Nat256At s (s.regValue .rcx) b) :
    Nat256At entry ((Operand.reg 6 : Operand 64).read entry) a ∧
      Nat256At entry ((Operand.reg 1 : Operand 64).read entry) b := by
  have left : (Operand.reg 6 : Operand 64).read entry = s.regValue .rsi :=
    ctx.agrees.read (by simp [P256.Proofs.Common.Field.SquareRoot.Multiply.prologueComponents])
  have right : (Operand.reg 1 : Operand 64).read entry = s.regValue .rcx :=
    ctx.agrees.read (by simp [P256.Proofs.Common.Field.SquareRoot.Multiply.prologueComponents])
  rw [left, right]
  exact ⟨(BodyState.initial ctx).nat256 ctx.pre.inputBounded
      (ctx.pre.separation (0 : Fin 3) 1 (by decide))
      (ctx.pre.separation (0 : Fin 3) 2 (by decide)) ha,
    (BodyState.initial ctx).nat256 ctx.pre.rightBounded ctx.pre.rightOutput ctx.pre.rightStack hb⟩

theorem lower_left_inputs [Bindings] {s entry p lo : RamState} {boundary : ReturnBoundary}
    {ctx : ExecutionContext s boundary entry} {a : Nat}
    (ps : BodyState ctx p) (los : BodyState ctx lo)
    (hp : (productsEffect entry).Holds entry p) (hl : (lowerSumsEffect p).Holds p lo)
    (ha : Nat256At s (s.regValue .rsi) a) :
    ((Operand.mem ((Operand.reg 6 : Operand 64).read lo+16) : Operand 64).read lo).toNat =
        (limbsOfNat a)[2] ∧
      ((Operand.reg 1 : Operand 64).read lo).toNat = (limbsOfNat a)[3] := by
  have src : savedSource p = s.regValue .rsi := (products_savedSource hp).trans
    (ctx.agrees.read (by simp [P256.Proofs.Common.Field.SquareRoot.Multiply.prologueComponents]))
  have rsi : lo.regValue .rsi = s.regValue .rsi := (lowerSums_source hl).trans src
  have naP := ps.nat256 ctx.pre.inputBounded
    (ctx.pre.separation (0 : Fin 3) 1 (by decide))
    (ctx.pre.separation (0 : Fin 3) 2 (by decide)) ha
  have naL := los.nat256 ctx.pre.inputBounded
    (ctx.pre.separation (0 : Fin 3) 1 (by decide))
    (ctx.pre.separation (0 : Fin 3) 2 (by decide)) ha
  constructor
  · change (memLoad lo.external (lo.regValue .rsi+16#64) 64).toNat = _
    rw [rsi]
    exact nat256_limb_toNat naL 2 (by decide)
  · change (lo.regValue .rcx).toNat = _
    rw [lowerSums_source_limb (lower_pre ps hp) hl, src]
    exact nat256_limb_toNat naP 3 (by decide)

end P256.Proofs.Field.Schoolbook
