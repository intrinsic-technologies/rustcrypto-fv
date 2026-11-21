import P256.Proofs.SignatureFromDer.Fixed.Finish.Output.Memory
import P256.Proofs.Common.Encoding.Serialize.Convert.SavePointer

set_option autoImplicit false

open P256.Proofs.Program (CalleePre)

namespace P256.Proofs.SignatureFromDer.Fixed.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

theorem after_stack_store [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {fuel off : Nat} {inputBytes : Nat} (pre : CalleePre s boundary 0x109ac0 inputBytes 72 560)
    (state : Stage s t boundary) (run : Advances boundary fuel t u) (ready : ReadyToStep u)
    (frame : AgreesExcept [.mem (stackPtr t + BitVec.ofNat 64 off) 8, .rip] t u)
    (bound : off + 8 ≤ 168) : Stage s u boundary := by
  apply state.after pre run ready frame
  · intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · refine ⟨workRegion s, by simp, ?_⟩
      rw [Program.ScalarFrame.scalar_stack_address (frameOffset := 184) state.rsp (by decide) (by omega)] at ha
      exact Program.ScalarFrame.Work.contains pre (by omega) (by omega) ha
    · exact ha.elim
  · exact (frame.read (n := 64) (r := 4) (by simp)).trans state.rsp
  · simp

theorem after_output_store [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {fuel off : Nat} {inputBytes : Nat} (pre : CalleePre s boundary 0x109ac0 inputBytes 72 560)
    (state : Stage s t boundary) (run : Advances boundary fuel t u) (ready : ReadyToStep u)
    (frame : AgreesExcept [.mem (s.regValue .rdi + BitVec.ofNat 64 off) 8, .rip] t u)
    (bound : off + 8 ≤ 72) : Stage s u boundary := by
  apply state.after pre run ready frame
  · intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨registerRegion s .rdi 72, by simp, output_contains pre bound ha⟩
    · exact ha.elim
  · exact (frame.read (n := 64) (r := 4) (by simp)).trans state.rsp
  · simp

theorem nat256_after_stack_store {t u : RamState} {off base x : Nat}
    (frame : AgreesExcept [.mem (stackPtr t + BitVec.ofNat 64 off) 8, .rip] t u)
    (apart : OffsetsApart (BitVec.ofNat 64 off) 8 (BitVec.ofNat 64 base) 32)
    (scalar : Nat256At t (stackPtr t + BitVec.ofNat 64 base) x) :
    Nat256At u (stackPtr u + BitVec.ofNat 64 base) x := by
  have rsp : stackPtr u = stackPtr t := frame.read (n := 64) (r := 4) (by simp)
  rw [rsp]
  refine ⟨scalar.1, ?_⟩
  intro i hi
  refine (frame.byte ?_).trans (scalar.2 i hi)
  intro c hc hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · obtain ⟨j, hj, he⟩ := hv
    exact apart.ne (stackPtr t) hj hi (by decide) he.symm
  · exact hv.elim

theorem output_word_preserved {s t : RamState} {address : BitVec 64} {off target : Nat}
    (frame : AgreesExcept [.mem (address + BitVec.ofNat 64 off) 8, .rip] s t)
    (apart : OffsetsApart (BitVec.ofNat 64 off) 8 (BitVec.ofNat 64 target) 8) :
    memLoad t.external (address + BitVec.ofNat 64 target) 64 =
      memLoad s.external (address + BitVec.ofNat 64 target) 64 := by
  apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees frame
  intro i hi c hc hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · obtain ⟨j, hj, he⟩ := hv
    exact apart.ne address hj hi (by decide) he.symm
  · exact hv.elim

structure Payload (t : RamState) (x y : Nat) : Prop where
  rax : (Operand.reg 0 : Operand 64).read t = BitVec.ofNat 64 (x / 2^192)
  rcx : (Operand.reg 1 : Operand 64).read t = BitVec.ofNat 64 (x / 2^128)
  rdx : (Operand.reg 2 : Operand 64).read t = BitVec.ofNat 64 (x / 2^0)
  rsi : (Operand.reg 6 : Operand 64).read t = BitVec.ofNat 64 (x / 2^64)
  rdi : (Operand.reg 7 : Operand 64).read t = BitVec.ofNat 64 (y / 2^0)
  r8 : (Operand.reg 8 : Operand 64).read t = BitVec.ofNat 64 (y / 2^64)
  r9 : (Operand.reg 9 : Operand 64).read t = BitVec.ofNat 64 (y / 2^128)
  r10 : (Operand.reg 10 : Operand 64).read t = BitVec.ofNat 64 (y / 2^192)

theorem Payload.of_agrees {t u : RamState} {x y : Nat} {cs : List Component}
    (payload : Payload t x y) (frame : AgreesExcept cs t u)
    (preserve : ∀ r, .reg r ∉ cs) : Payload u x y := by
  exact ⟨(frame.read (n := 64) (r := 0) (preserve 0)).trans payload.rax,
    (frame.read (n := 64) (r := 1) (preserve 1)).trans payload.rcx,
    (frame.read (n := 64) (r := 2) (preserve 2)).trans payload.rdx,
    (frame.read (n := 64) (r := 6) (preserve 6)).trans payload.rsi,
    (frame.read (n := 64) (r := 7) (preserve 7)).trans payload.rdi,
    (frame.read (n := 64) (r := 8) (preserve 8)).trans payload.r8,
    (frame.read (n := 64) (r := 9) (preserve 9)).trans payload.r9,
    (frame.read (n := 64) (r := 10) (preserve 10)).trans payload.r10⟩

end P256.Proofs.SignatureFromDer.Fixed.Finish
