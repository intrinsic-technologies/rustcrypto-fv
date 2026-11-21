import X86Proofs.Core.Shift

namespace P256.Proofs.Common.Instructions

open X86 X86.Helpers X86Proofs

theorem shiftRightArithmetic_one {n : Nat} (hn : 1 < n) (x : BitVec n) :
    Std.Bits.Shift_Right_Arithmetic (size := (n : Int)) x 1 = .ok (x.sshiftRight 1) := by
  simp [Std.Bits.Shift_Right_Arithmetic, Std.Bits.Shift_Right_Arithmetic_Restricted,
    Runtime.shiftRightArithmetic, pure, Except.pure, bind, Except.bind, x86_runtime, show 0 ≤ (n : Int) by omega,
    show (1 : Int) < n by omega, show n ≠ 0 by omega, show (1 : Int) ≤ n by omega]

theorem sar_fold {n : Nat} (x : BitVec n) (cf : BitVec 1) (k : Nat)
    (hk : 0 < k) (hkn : k ≤ n) :
    (Runtime.intRange 0 ((k : Int) - 1)).foldl
        (fun (acc : BitVec n × BitVec 1) (_ : Int) =>
          (acc.1.sshiftRight 1, acc.1.extractLsb' 0 1)) (x, cf) =
      (x.sshiftRight k, x.extractLsb' (k - 1) 1) := by
  have hr : Runtime.intRange 0 ((k : Int) - 1) =
      (List.range k).map (fun i : Nat => (0 : Int) + i) := by
    simp only [x86_runtime]
    congr 2
    omega
  rw [hr, List.foldl_map]
  clear hr
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  clear hk
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, ih (by omega)]
    simp only [List.foldl_cons, List.foldl_nil, Nat.add_sub_cancel, Prod.mk.injEq]
    constructor
    · exact BitVec.sshiftRight_add.symm
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_sshiftRight]
      simp [show i = 0 by omega, show k + 1 < n by omega, show n ≠ 0 by omega]

end P256.Proofs.Common.Instructions
