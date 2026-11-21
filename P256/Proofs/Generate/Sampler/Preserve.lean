import P256.Proofs.Generate.Sampler.Memory

set_option autoImplicit false

namespace P256.Proofs.Generate.Sampler

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

 theorem preserved_load {t u : RamState} {cs : List Component} {address : BitVec 64} {width : Nat}
    (agrees : AgreesExcept cs t u)
    (apart : ∀ i < width/8, ∀ c ∈ cs, ¬ c.Covers (address + BitVec.ofNat 64 i)) :
    memLoad u.external address width = memLoad t.external address width := by
  apply memLoad_congr
  intro i hi
  change (u.external[address+BitVec.ofNat 64 i]?).getD 0 =
    (t.external[address+BitVec.ofNat 64 i]?).getD 0
  rw [agrees.memory _ (apart i hi)]

theorem stack_load_preserved {t u : RamState} {cs : List Component} {offset : BitVec 64}
    (agrees : AgreesExcept cs t u)
    (apart : ∀ c ∈ cs, ∀ a, c.Covers a →
      ∃ start len, a = stackPtr t + start + BitVec.ofNat 64 len ∧
        ∃ size, len < size ∧ OffsetsApart start size offset 8 ∧ size+8 < 2^64) :
    memLoad u.external (stackPtr t + offset) 64 = memLoad t.external (stackPtr t + offset) 64 := by
  apply preserved_load agrees
  intro i hi c hc covered
  obtain ⟨start,j,eq,size,hj,separate,bounded⟩ := apart c hc _ covered
  exact separate.ne (stackPtr t) hj hi bounded eq.symm

end P256.Proofs.Generate.Sampler
