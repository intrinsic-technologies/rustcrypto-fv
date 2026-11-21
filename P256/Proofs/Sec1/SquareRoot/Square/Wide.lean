import P256.Proofs.Sec1.SquareRoot.Square.Wide.Execute

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Square

open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem wide_square_correct [Bindings] {s : RamState} {boundary : ReturnBoundary} {a : Nat}
    (pre : WidePre s boundary) (count : s.regValue .rdx = 4)
    (input : Nat256At s (s.regValue .rsi) a) :
    ∃ t, CalleeResult s t boundary 64 88 ∧
      Bytes t.external (s.regValue .rdi) 64
        (fun i => UInt8.ofNat ((a * a) / 256^i % 256)) := by
  obtain ⟨t, u, result, frame, bytes⟩ := Wide.execute_correct pre count
  have rsi : t.regValue .rsi = s.regValue .rsi :=
    frame.read (n := 64) (r := 6)
      (by simp [P256.Proofs.Common.Field.SquareRoot.Multiply.prologueComponents])
  have ht : Nat256At t (t.regValue .rsi) a := by
    refine ⟨input.1, ?_⟩
    intro i hi
    rw [rsi, Wide.input_bytes pre (Wide.prologue_frame frame) hi]
    exact input.2 i hi
  rw [Wide.squareWords_correct, Wide.sourceWords_nat ht,
    P256.Proofs.Field.Schoolbook.packFour_limbsOfNat input.1, Nat.pow_two] at bytes
  exact ⟨u, result, bytes⟩

end P256.Proofs.Sec1.SquareRoot.Square
