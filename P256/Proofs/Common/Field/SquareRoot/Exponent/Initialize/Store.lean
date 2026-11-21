import X86Proofs.Program.ReadWrite.Bytes

set_option autoImplicit false

namespace P256.Proofs.Common.Field.SquareRoot.ExponentInitialize

open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem external_of_store {s t : RamState} {n : Nat}
    {address : BitVec 64} {value : BitVec n}
    (h : AgreesExcept [.mem address (n / 8), .rip] s t)
    (hm : ∀ i < n / 8, (s.external[address + BitVec.ofNat 64 i]?).isSome)
    (hv : (Operand.mem address : Operand n).read t = value)
    (hn : n ≤ 128 := by decide) :
    t.external = memStore s.external address value := by
  have hb := Bytes.of_memLoad (n := n) (fun i hi => h.grow _ (hm i hi))
  change memLoad t.external address n = value at hv
  rw [hv] at hb
  apply Std.ExtHashMap.ext_getElem?
  intro a
  by_cases hc : (Component.mem address (n / 8)).Covers a
  · obtain ⟨i, hi, rfl⟩ := hc
    exact (hb i hi).trans (memStore_getElem?_self _ _ _ hn i hi).symm
  · rw [memStore_getElem?_of_ne _ _ _ _ (fun i hi he => hc ⟨i, hi, he.symm⟩)]
    apply h.memory
    intro c hm hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact hc hcov
    · exact hcov

end P256.Proofs.Common.Field.SquareRoot.ExponentInitialize
