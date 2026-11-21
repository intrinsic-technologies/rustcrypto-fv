import X86Proofs.Core.Shift
import Sha2.Proofs.Common.Instructions.Imul.Spec

set_option autoImplicit false

open X86Proofs

namespace Sha2.Proofs.Common.Instructions

open X86 X86.Helpers

theorem oracle_mk_skip (o : X86.Runtime.Oracle) (k : Nat) :
    ({ bits := o.bits, position := o.position + k, limit := o.limit } : X86.Runtime.Oracle) =
      oracleSkip o k := rfl

theorem oracleTake_match_skip (o : X86.Runtime.Oracle) (k : Nat) :
    X86.Runtime.Oracle.take.match_1 (fun _ => Nat) o.limit
      (fun limit => min 1 (limit - (o.position + k))) (fun _ => 1) =
      oracleTakeCount (oracleSkip o k) 1 := rfl

theorem imul64_operation {σ : Type} (s : X86.State σ) (a b : BitVec 64) :
    (X86.Instructions.Operations.IMUL_SINGLE 64 a b).run s =
      (.ok (a * b), setFlags {s with oracle := oracleSkip s.oracle 4}
        (imulSpec64 s.oracle a b).2) := by
  unfold X86.Instructions.Operations.IMUL_SINGLE
  simp only [Int.reduceBEq, Bool.false_or, x86_runtime, X86.Runtime.CheckedSlice.read,
    X86.Runtime.intSlice, bind_pure_comp, pure_bind, map_pure, Int.reduceToNat,
    Int.reducePow, Int.ediv_one]
  repeat (spec_bind_rfl!; dsimp only [])
  change ((Except.ok _ : Except (Runtime.Error Exception) (BitVec 64)), _) = _
  simp [imulSpec64, imulOverflow64, setFlags, StatusFlags.store,
    Int.reduceToNat, oracle_mk_skip, oracleTake_match_skip, oracleTake_match_eq_oracleTakeCount,
    oracleTakeGo_one,
    BitVec.ofInt_mul, Nat.add_assoc, BitVec.ofBool]

end Sha2.Proofs.Common.Instructions
