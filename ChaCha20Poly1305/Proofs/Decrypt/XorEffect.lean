import ChaCha20Poly1305.Proofs.Decrypt.XorRun

namespace ChaCha20Poly1305.Proofs.Decrypt.Stream.Xor
open Prelude X86 X86.Machine X86Proofs ChaCha20Poly1305.Proofs.Refine

def ptr (a : BitVec 64) (i : Nat) := a+BitVec.ofNat 64 i

theorem ptrNat {a : BitVec 64} {i : Nat} (h : a.toNat+i < 2^64) :
    (ptr a i).toNat = a.toNat+i := by
  simp only [ptr,BitVec.toNat_add, BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show i < 2^64 by omega),
    Nat.mod_eq_of_lt h]

theorem ptr_assoc (a : BitVec 64) (i j : Nat) : ptr (ptr a i) j = ptr a (i+j) := by
  simp only [ptr,BitVec.ofNat_add,BitVec.add_assoc]

structure Shape (src key dst : BitVec 64) (size : Nat) : Prop where
  srcLow : src.toNat+size ≤ 2^32
  keyLow : key.toNat+size ≤ 2^32
  dstLow : dst.toNat+size ≤ 2^32
  keyApart : key.toNat+size ≤ dst.toNat ∨ dst.toNat+size ≤ key.toNat
  srcApart : src = dst ∨ src.toNat+size ≤ dst.toNat ∨ dst.toNat+size ≤ src.toNat

structure Effect (src key dst : BitVec 64) (size : Nat) (m m' : Ram) : Prop where
  frame : RamWriteFrame m m' [⟨dst.toNat,size⟩]
  value : ∀ i, i<size → readAt m' dst i = readAt m key i ^^^ readAt m src i

theorem Effect.zero {src key dst : BitVec 64} {m : Ram} : Effect src key dst 0 m m :=
  ⟨.refl _ _,fun _i hi => False.elim (Nat.not_lt_zero _ hi)⟩

theorem Effect.join {s k d : BitVec 64} {total p q : Nat} {m₀ m₁ m₂ : Ram}
    (shape : Shape s k d total) (bound : p+q ≤ total)
    (first : Effect s k d p m₀ m₁) (last : Effect (ptr s p) (ptr k p) (ptr d p) q m₁ m₂) :
    Effect s k d (p+q) m₀ m₂ := by
  obtain ⟨sl,kl,dl,ka,sa⟩ := shape
  have dp : (ptr d p).toNat = d.toNat+p := ptrNat (by omega)
  have pre (base : BitVec 64) (i : Nat) (ih : i < p+q)
      (bl : base.toNat+total ≤ 2^32)
      (sep : base.toNat+i+1 ≤ d.toNat ∨ d.toNat+p ≤ base.toNat+i) :
      readAt m₁ base i = readAt m₀ base i := by
    apply first.frame.memLoad_eq
    change Outside [_] (ptr base i) 1
    simp only [Outside,List.mem_singleton,forall_eq,ptrNat (show base.toNat+i<2^64 by omega)]
    exact ⟨by omega,sep⟩
  constructor
  · have f := (RamWriteFrame.refl m₀ [⟨d.toNat,p+q⟩]).trans first.frame (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r; exact ⟨_,.head _,Nat.le_refl _,by dsimp; omega⟩)
    apply f.trans last.frame
    intro r hr; simp only [List.mem_singleton] at hr; subst r
    exact ⟨_,.head _,by dsimp; omega,by dsimp; omega⟩
  · intro i hi
    by_cases h : i<p
    · rw [← first.value i h]
      apply last.frame.memLoad_eq
      change Outside [_] (ptr d i) 1
      simp only [Outside,List.mem_singleton,forall_eq,ptrNat (show d.toNat+i < 2^64 by omega),dp]
      exact ⟨by omega,Or.inl (by omega)⟩
    · let j := i-p
      have ij : p+j=i := by dsimp [j]; omega
      have rd (m : Ram) (b : BitVec 64) : readAt m (ptr b p) j = readAt m b i :=
        congrArg (fun a => memLoad m a 8) ((ptr_assoc b p j).trans (congrArg (ptr b) ij))
      have v := last.value j (by dsimp [j]; omega)
      rw [rd,rd,rd] at v
      rw [v,pre k i hi kl (by omega),pre s i hi sl]
      rcases sa with h | h <;> first | (rw [h]; omega) | omega

end ChaCha20Poly1305.Proofs.Decrypt.Stream.Xor
