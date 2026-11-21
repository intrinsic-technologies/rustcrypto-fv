import P256.Proofs.Program.Compare.Model

namespace P256.Proofs.Program.Compare.Tail

open X86 X86.Machine X86.UserProcess X86Proofs

theorem small_length_split (n : BitVec 64) (hn : n.toNat < 16) :
    let a := (n.setWidth 32 &&& 24).toNat
    let b := (n.setWidth 32 &&& 4).toNat
    let c := (n.setWidth 32 &&& 2).toNat
    let d := (n.setWidth 8 &&& 1).toNat
    a + b + c + d = n.toNat ∧
      (a = 0 ∨ a = 8) ∧ (b = 0 ∨ b = 4) ∧ (c = 0 ∨ c = 2) ∧ (d = 0 ∨ d = 1) := by
  have h : ∀ i : Fin 16,
      let k := BitVec.ofNat 64 i.val
      let a := (k.setWidth 32 &&& 24).toNat
      let b := (k.setWidth 32 &&& 4).toNat
      let c := (k.setWidth 32 &&& 2).toNat
      let d := (k.setWidth 8 &&& 1).toNat
      a + b + c + d = k.toNat ∧
        (a = 0 ∨ a = 8) ∧ (b = 0 ∨ b = 4) ∧ (c = 0 ∨ c = 2) ∧ (d = 0 ∨ d = 1) := by
    decide +kernel
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using h ⟨n.toNat, hn⟩

end P256.Proofs.Program.Compare.Tail
