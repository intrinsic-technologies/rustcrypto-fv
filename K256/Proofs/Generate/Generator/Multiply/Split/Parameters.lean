import K256.Proofs.Generate.Generator.Multiply.Split.Contract
import K256.Proofs.Common.Image
import K256.Proofs.Common.Refine.Lemma.SysVEntry

namespace K256.Proofs.Generate.Generator.Multiply.Split

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine Standards.SECG.DomainParameters.Secp256k1
open K256.Proofs.Generate.Curve

def parameters : List (BitVec 64 × Nat) :=
  [(0x202180, 1), (0x2021a0, domain.n), (0x202200, g1), (0x202220, minusB1),
    (0x202240, g2), (0x202260, minusB2), (0x202280, domain.n - eigenvalue)]

private def parameterBytes (x : Nat) : List UInt8 :=
  List.ofFn fun i : Fin 32 =>
    storedByte ((scalarWords x).get ⟨i.val / 8, by omega⟩) (i.val % 8)

set_option maxRecDepth 8192 in
private theorem parameterImage {p : BitVec 64} {x : Nat} (h : (p,x) ∈ parameters) :
    (∀ b ∈ codeRange p (parameterBytes x), b ∈ Extracted.programImage) ∧ p.toNat + 32 ≤ 2^32 := by
  let sec : ImageSection := ⟨Extracted.rodataAddress, Extracted.rodataBytes⟩
  have hs : sec ∈ Extracted.programSections := by simp [sec, Extracted.programSections]
  simp only [parameters, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact ⟨codeRange_sub_section hs 0x2180 32 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) rfl, by decide⟩
  · exact ⟨codeRange_sub_section hs 0x21a0 32 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) rfl, by decide⟩
  · exact ⟨codeRange_sub_section hs 0x2200 32 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) rfl, by decide⟩
  · exact ⟨codeRange_sub_section hs 0x2220 32 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) rfl, by decide⟩
  · exact ⟨codeRange_sub_section hs 0x2240 32 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) rfl, by decide⟩
  · exact ⟨codeRange_sub_section hs 0x2260 32 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) rfl, by decide⟩
  · exact ⟨codeRange_sub_section hs 0x2280 32 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) rfl, by decide⟩

structure ParameterAt (m : Ram) (p : BitVec 64) (x : Nat) : Prop where
  readable : Readable m p 32
  words : WordsAt m p 64 (scalarWords x)
  apart : ∀ {dst size}, Writable Extracted.programImage m dst size → 0 < size →
    p.toNat + 32 ≤ dst.toNat ∨ dst.toNat + size ≤ p.toNat

theorem parameterAt {m : Ram} (loaded : ∀ b ∈ Extracted.programImage, m[b.1]? = some b.2)
    {p : BitVec 64} {x : Nat} (h : (p,x) ∈ parameters) : ParameterAt m p x := by
  obtain ⟨image, bound⟩ := parameterImage h
  have byte (i : Nat) (hi : i < 32) :=
    image _ (mem_codeRange p (parameterBytes x) i (by simpa only [parameterBytes, List.length_ofFn] using hi))
  refine ⟨⟨bound, fun i hi => ?_⟩, ?_, ?_⟩
  · rw [loaded _ (byte i hi)]
    rfl
  · intro i hi
    refine Bytes.memLoad ?_ (by decide) (by decide)
    intro j hj
    have hij : 8*i+j < 32 := by omega
    have v := loaded _ (byte _ hij)
    simp only [parameterBytes, List.getElem_ofFn, Nat.mul_add_div (by decide : 0 < 8),
      Nat.mul_add_mod, Nat.mod_eq_of_lt (show j < 8 by omega), Nat.div_eq_of_lt (show j < 8 by omega),
      Nat.add_zero, BitVec.ofNat_add, ← BitVec.add_assoc] at v
    exact v
  · intro dst size w pos
    apply Classical.byContradiction
    intro hn
    obtain ⟨hl, hr⟩ := not_or.mp hn
    let a := max dst.toNat p.toNat
    have ha : p.toNat ≤ a ∧ dst.toNat ≤ a ∧ a < p.toNat + 32 ∧ a < dst.toNat + size := by
      dsimp [a]
      omega
    apply w.notCode _ (byte (a - p.toNat) (by omega)) (a - dst.toNat) (by omega)
    simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      congrArg (BitVec.ofNat 64) (show p.toNat + (a - p.toNat) = dst.toNat + (a - dst.toNat) by omega)

end K256.Proofs.Generate.Generator.Multiply.Split
