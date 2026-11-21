import X86Proofs.Core.Run
import Sha3.Proofs.X86.Instructions.MovzxLoad.Spec

namespace X86Proofs

open X86 X86.Helpers

theorem movzx_operation_except (n : Nat) (hn : n = 64 ∨ n = 32) (x : BitVec 8) :
    X86.Instructions.Operations.MOVZX 8 n x = .ok (movzxSpec n x) := by
  rcases hn with rfl | rfl <;>
  simp [X86.Instructions.Operations.MOVZX, x86_runtime, movzxSpec, bind, pure, Except.bind,
    Except.pure]

theorem movzx_operation {σ : Type} (s : X86.State σ) (n : Nat) (hn : n = 64 ∨ n = 32)
    (x : BitVec 8) :
    (liftM (X86.Instructions.Operations.MOVZX 8 n x) :
      X86.Runtime.SpecM X86.Exception (X86.State σ) (BitVec n)).run s =
        (.ok (movzxSpec n x), s) := by
  rw [movzx_operation_except n hn]
  rfl

end X86Proofs
