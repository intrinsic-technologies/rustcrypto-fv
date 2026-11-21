import X86Proofs.Core.Shift
import X86Proofs.Program.Effect

namespace P256.Proofs.Common.Instructions.ShiftLeft

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

def shldOneResult (x y : BitVec 64) : BitVec 64 :=
  (BitVec.ofNat 128 ((x.toNat <<< 64) + y.toNat)).extractLsb' 63 64

def shldOneSpec (af : Bool) (x y : BitVec 64) : BitVec 64 × StatusFlags :=
  let r := shldOneResult x y
  (r, { CF := x.msb, PF := evenParity (r.extractLsb' 0 8), AF := af, ZF := r == 0, SF := r.msb, OF := x.msb != r.msb })

theorem shld_one_operation {σ : Type} (s : X86.State σ) (x y : BitVec 64) :
    (X86.Instructions.Operations.SHLD 64 x y 1).run s =
      let (r, flags) := shldOneSpec (oracleBit s.oracle) x y
      (.ok r, setFlags {s with oracle := oracleSkip s.oracle 1} flags) := by
  unfold X86.Instructions.Operations.SHLD
  simp only [isParityEven8_run]
  repeat spec_bind_rfl
  simp only [shldOneSpec, shldOneResult]
  rw [setFlags_eq_of_store]
  · rfl
  · rflags_ext

end P256.Proofs.Common.Instructions.ShiftLeft
