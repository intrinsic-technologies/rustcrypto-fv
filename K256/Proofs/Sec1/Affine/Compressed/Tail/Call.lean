import K256.Proofs.Sec1.Affine.Compressed.Tail.Mask
import K256.Proofs.Sec1.Affine.Compressed.Tail.Choose
import K256.Proofs.Sec1.Affine.Compressed.Tail.Normalize
import K256.Proofs.Sec1.Affine.Compressed.Tail.Frame
import K256.Proofs.Sec1.Serialize.Normalize.Correct

namespace K256.Proofs.Sec1.Affine.Compressed

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
open K256.Proofs.Refine K256.Proofs.Sec1.LIR K256.Proofs.Common.Field Serialize.Coordinates

theorem selectCall {code : CodeMap} (cover : ∀ e ∈ fnCode, e ∈ code) : SelectCall code := by
  intro fr args mem xs xOK ok want root env body wide hr hw hp
  obtain ⟨n₁,m₁,a,c₁,i₁,repr⟩ := maskRootCall cover body hr wide
  obtain ⟨o₁,e₁,t₁,s₁,k₁,f₁,w₁,b₁⟩ :=
    normalizeRootCall env body i₁ (.inl ⟨rfl,rfl⟩) (by decide)
  have ⟨body₁,F₁⟩ := bodyAt_selectWrites body s₁ k₁ f₁
  obtain ⟨p,b,n₂,m₂,reach,c₂,i₂⟩ := chooseRootCall cover body₁ w₁ b₁
  obtain ⟨o₂,e₂,t₂,s₂,k₂,f₂,w₂,b₂⟩ :=
    normalizeRootCall env body₁ i₂ (.inr ⟨rfl,rfl⟩) (by decide)
  have ⟨body₂,F₂⟩ := bodyAt_selectWrites body₁ s₂ k₂ f₂
  refine ⟨_,_, ((reaches_call c₁ e₁ t₁).trans reach).trans (reaches_call c₂ e₂ t₂),
    body₂, ⟨b₂, ?_⟩, F₁.trans F₂ (fun r h => ⟨r,h,Nat.le_refl _,Nat.le_refl _⟩)⟩
  intro h
  refine ⟨_, w₂, ?_⟩
  obtain ⟨width,value⟩ := Serialize.Normalize.normalize_correct a root 8 (repr h) (by decide)
  have sel := selectRoot_repr _ width value (hp h) root.isLt want hw
  have chosen : FieldRepr (selectRoot (Serialize.Normalize.normalize a) want) (chosenY root want) 2 := by
    have eq : chosenY root want = ⟨(if root.val % 2 = want.toNat then root.val else modulus-root.val), by
      have lt := root.isLt
      have pos := hp h
      split <;> omega⟩ := by
      apply Fin.ext
      simp only [chosenY]
      split <;> simp [Nat.mod_eq_of_lt (show modulus-root.val < modulus by have := hp h; omega)]
    rw [eq]
    exact sel
  obtain ⟨wy,vy⟩ := Serialize.Normalize.normalize_correct _ _ 2 chosen (by decide)
  refine ⟨?_, by rw [vy, Nat.mod_eq_of_lt (chosenY root want).isLt]⟩
  intro i
  have hi := wy i
  change _ < 2 ^ (if i.val = 4 then 48 else 52) at hi
  simp (disch := exact i.isLt) only [getElem!_pos]
  split <;> split at hi <;> have := i.isLt <;> omega

end K256.Proofs.Sec1.Affine.Compressed
