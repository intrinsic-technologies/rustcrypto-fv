import X86Proofs.Core.Shift
import P256.Proofs.Common.Instructions.Mul.Spec

set_option autoImplicit false

open X86Proofs

namespace P256.Proofs.Common.Instructions

open X86 X86.Helpers

theorem mul64_operation {σ : Type} (s : X86.State σ) (src : BitVec 64) :
    (X86.Instructions.Operations.MUL 64 src).run s = (.ok (), mulResult64 s src) := by
  unfold X86.Instructions.Operations.MUL
  simp only [Int.reduceBEq, Bool.false_or,
    x86_runtime, X86.Runtime.sliceElement, X86.Runtime.CheckedSlice.read,
    X86.Runtime.intSlice, mergeGPR64_run, mergeGPR_64,
    bind_pure_comp, pure_bind, map_pure, bind_pure, Int.reduceMul, Int.reduceToNat,
    Int.reducePow, Int.ediv_one, BitVec.extractLsb'_eq_self]
  repeat (spec_bind_rfl!; dsimp only [])
  change ((Except.ok () : Except (Runtime.Error Exception) Unit), _) = _
  have oracle_mk_skip (o : X86.Runtime.Oracle) (k : Nat) :
      ({ bits := o.bits, position := o.position + k, limit := o.limit } : X86.Runtime.Oracle) =
        oracleSkip o k := rfl
  have oracleTake_match_skip (o : X86.Runtime.Oracle) (k : Nat) :
      X86.Runtime.Oracle.take.match_1 (fun _ => Nat) o.limit
        (fun limit => min 1 (limit - (o.position + k))) (fun _ => 1) =
        oracleTakeCount (oracleSkip o k) 1 := rfl
  simp [mulResult64, setFlags, mulStatus64, StatusFlags.store,
    Int.reduceToNat, BitVec.ofNat_eq_ofNat, oracle_mk_skip, oracleTake_match_skip,
    oracleTake_match_eq_oracleTakeCount, oracleTakeGo_one,
    mulHigh64_eq_ofInt, BitVec.ofInt_mul, BitVec.ofInt_natCast,
    gprIndex, Nat.add_assoc, BitVec.ofBool, bne]

end P256.Proofs.Common.Instructions
