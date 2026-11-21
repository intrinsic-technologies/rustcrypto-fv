import P256.Proofs.Field.Preserve
import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.Prepared
import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.TableCopy

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.ExponentInitialize

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open SecretKeyFromBytes.Scalar (Nat256At)

structure TableData (s t : RamState) (x count : Nat) : Prop where
  table : ∀ i<count, Field.MontgomeryAt t
    (exponentFrameBase s+BitVec.ofNat 64 (160+32*i)) (x^i%P256.Spec.Operations.domain.p)
  exponent : Nat256At t (exponentFrameBase s+0x538) sqrtExponent
  input : Field.MontgomeryAt t (exponentFrameBase s+0x2f8) x
  output : exponentWordAt t (exponentFrameBase s+0x2a0) (s.regValue .rdi)

structure TableState [Bindings] (s t : RamState) (x count : Nat) : Prop where
  frame : Frame s t
  data : TableData s t x count
  bitCount : t.regValue .r14=254
  parameter : t.regValue .r15=s.regValue .rsi+32
  input : t.regValue .rbx=exponentFrameBase s+0x2f8
  inverse : t.regValue .r12=0xffffffffffffffff
  negativeInverse : t.regValue .r13=1
  output : t.regValue .rbp=exponentFrameBase s+0x10

def TableDataOffset (count offset : Nat) : Prop :=
  (160≤offset ∧ offset<160+32*count) ∨ (1336≤offset ∧ offset<1368) ∨
  (760≤offset ∧ offset<792) ∨ (672≤offset ∧ offset<680)

theorem TableData.of_bytes {s t u : RamState} {x count : Nat} (h : TableData s t x count)
    (hb : ∀ offset, TableDataOffset count offset →
      u.external[exponentFrameBase s+BitVec.ofNat 64 offset]?=
      t.external[exponentFrameBase s+BitVec.ofNat 64 offset]?) : TableData s u x count := by
  refine ⟨?_,?_,?_,?_⟩
  · intro i hi
    apply (h.table i hi).of_bytes_eq
    intro j hj
    simpa only [BitVec.add_assoc,← BitVec.ofNat_add] using
      hb (160+32*i+j) (by unfold TableDataOffset; omega)
  · refine ⟨h.exponent.1,?_⟩
    intro j hj
    apply Eq.trans ?_ (h.exponent.2 j hj)
    simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,← BitVec.ofNat_add] using
      hb (1336+j) (by unfold TableDataOffset; omega)
  · apply h.input.of_bytes_eq
    intro j hj
    simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,← BitVec.ofNat_add] using
      hb (760+j) (by unfold TableDataOffset; omega)
  · apply Eq.trans ?_ h.output
    apply memLoad_congr
    intro j hj
    change (u.external[_]?).getD 0=(t.external[_]?).getD 0
    congr 1
    simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,← BitVec.ofNat_add] using
      hb (672+j) (by unfold TableDataOffset; omega)

theorem TableData.of_agrees {s t u : RamState} {x count : Nat} {cs : List Component}
    (h : TableData s t x count) (g : AgreesExcept cs t u)
    (ha : ∀ off, TableDataOffset count off → ∀ c∈cs,
      ¬c.Covers (exponentFrameBase s+BitVec.ofNat 64 off)) : TableData s u x count :=
  h.of_bytes (fun off ho ↦ g.memory _ (ha off ho))

theorem TableState.of_agrees [Bindings] {s t u : RamState} {x count : Nat} {cs : List Component}
    (h : TableState s t x count) (hf : Frame s u) (g : AgreesExcept cs t u)
    (hr : ∀ r∈([3,5,12,13,14,15] : List (BitVec 5)), .reg r∉cs)
    (ha : ∀ off, TableDataOffset count off → ∀ c∈cs,
      ¬c.Covers (exponentFrameBase s+BitVec.ofNat 64 off)) : TableState s u x count := by
  refine ⟨hf,h.data.of_agrees g ha,?_,?_,?_,?_,?_,?_⟩
  · exact (g.read (n := 64) (r := 14) (hr _ (by simp))).trans h.bitCount
  · exact (g.read (n := 64) (r := 15) (hr _ (by simp))).trans h.parameter
  · exact (g.read (n := 64) (r := 3) (hr _ (by simp))).trans h.input
  · exact (g.read (n := 64) (r := 12) (hr _ (by simp))).trans h.inverse
  · exact (g.read (n := 64) (r := 13) (hr _ (by simp))).trans h.negativeInverse
  · exact (g.read (n := 64) (r := 5) (hr _ (by simp))).trans h.output

end P256.Proofs.Sec1.SquareRoot.ExponentInitialize
