import P256.Proofs.Sec1.Decompress.Cubic
import P256.Proofs.Sec1.Decompress.Input
import P256.Proofs.Sec1.Decompress.Select
import P256.Proofs.Sec1.Decompress.Output
import P256.Proofs.Sec1.Decompress.Epilogue
import P256.Proofs.Sec1.Representation

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decompress

open P256.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Standards.SECG.ECC

theorem decompress_correct_of_input_sqrt [Bindings]
    (input : ∀ (s : RamState) (boundary : ReturnBoundary) (bytes : ByteArray) (odd : Bool),
      Pre s boundary bytes odd → ∃ fuel t, Advances boundary fuel s t ∧
        InputState s t (Encoding.octetsToNat bytes) odd)
    (sqrt : ∀ (s : RamState) (boundary : ReturnBoundary) (x : Nat),
      SquareRoot.Pre s boundary → Field.MontgomeryAt s (s.regValue .rsi) x →
      ∃ t, CalleeResult s t boundary 40 2176 ∧
        SquareRoot.SquareRootResultAt t (s.regValue .rdi) x)
    {s : RamState} {boundary : ReturnBoundary} {bytes : ByteArray} {odd : Bool}
    (pre : Pre s boundary bytes odd) :
    ∃ t, CalleeResult s t boundary 80 2592 ∧ AffineResultAt t (s.regValue .rdi)
      (P256.Spec.Points.decompress (Encoding.octetsToNat bytes) odd) := by
  obtain ⟨n,a,runA,entry⟩ := input s boundary bytes odd pre
  obtain ⟨m,b,runB,root⟩ := root_correct pre entry (fun v x hp hx ↦ sqrt v boundary x hp hx)
  obtain ⟨k,c,runC,selected⟩ := select_correct pre root
  obtain ⟨j,d,runD,frame,rip,value⟩ := output_correct pre selected
  obtain ⟨t,result,memory⟩ := finish pre.toCalleePre frame rip
    ⟨n+m+k+j,((runA.trans runB).trans runC).trans runD⟩
  exact ⟨t,result,value.of_bytes_eq (fun _ _ ↦ by rw [memory])⟩

theorem decompress_correct_of_sqrt [Bindings]
    (sqrt : ∀ (s : RamState) (boundary : ReturnBoundary) (x : Nat),
      SquareRoot.Pre s boundary → Field.MontgomeryAt s (s.regValue .rsi) x →
      ∃ t, CalleeResult s t boundary 40 2176 ∧
        SquareRoot.SquareRootResultAt t (s.regValue .rdi) x)
    {s : RamState} {boundary : ReturnBoundary} {bytes : ByteArray} {odd : Bool}
    (pre : Pre s boundary bytes odd) :
    ∃ t, CalleeResult s t boundary 80 2592 ∧ AffineResultAt t (s.regValue .rdi)
      (P256.Spec.Points.decompress (Encoding.octetsToNat bytes) odd) :=
  decompress_correct_of_input_sqrt (fun _ _ _ _ hp ↦ input_correct hp) sqrt pre

end P256.Proofs.Sec1.Decompress
