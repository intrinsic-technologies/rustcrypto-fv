import P256.Proofs.Sec1.Affine.State

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compact.Copy

open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem stack_span {s t : RamState} {cs registers : List Component} {base : BitVec 64}
    {start len : Nat} (agrees : AgreesExcept cs s t)
    (regs : ∀ c ∈ cs, c.isMem = false → c ∈ registers)
    (memory : ∀ address count, Component.mem address count ∈ cs →
      ∃ off : Nat, address = base + BitVec.ofNat 64 off ∧ start ≤ off ∧ off + count ≤ start + len) :
    AgreesExcept (.mem (base + BitVec.ofNat 64 start) len :: registers) s t := by
  apply agrees.widen
  · intro c hc hm
    exact .tail _ (regs c hc hm)
  · intro a c hc ha
    cases c <;> try exact ha.elim
    case mem address count =>
      obtain ⟨off,rfl,lower,upper⟩ := memory address count hc
      obtain ⟨j,hj,eq⟩ := ha
      refine ⟨.mem (base + BitVec.ofNat 64 start) len,by simp,off-start+j,by omega,?_⟩
      rw [eq,BitVec.add_assoc,← BitVec.ofNat_add,BitVec.add_assoc,← BitVec.ofNat_add]
      congr 2
      omega


theorem stack_bytes {s t : RamState} {base : BitVec 64} {offset count target len : Nat}
    {registers : List Component}
    (agrees : AgreesExcept (.mem (base-BitVec.ofNat 64 offset) count :: registers) s t)
    (nomem : ∀ c ∈ registers, ∀ a, ¬ c.Covers a)
    (apart : OffsetsApart (-BitVec.ofNat 64 offset) count (-BitVec.ofNat 64 target) len)
    (small : count+len < 2^64) :
    ∀ i < len, t.external[base-BitVec.ofNat 64 target+BitVec.ofNat 64 i]? =
      s.external[base-BitVec.ofNat 64 target+BitVec.ofNat 64 i]? := by
  intro i hi
  apply agrees.byte
  intro c hc ha
  simp only [List.mem_cons] at hc
  rcases hc with rfl | hc
  · obtain ⟨j,hj,eq⟩ := ha
    apply OffsetsApart.ne apart base hj hi small
    simpa only [BitVec.sub_eq_add_neg,BitVec.add_assoc] using eq.symm
  · exact nomem c hc _ ha

end P256.Proofs.Sec1.Affine.Compact.Copy
