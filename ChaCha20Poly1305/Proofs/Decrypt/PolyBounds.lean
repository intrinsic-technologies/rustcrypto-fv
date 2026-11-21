import ChaCha20Poly1305.Proofs.Decrypt.Poly1305

namespace ChaCha20Poly1305.Proofs.Decrypt.Poly1305

def Limbs.Bounded (a : Limbs) : Prop :=
  a.x0 < B ∧ a.x1 < B+64 ∧ a.x2 < B ∧ a.x3 < B ∧ a.x4 < B

def Limbs.Tight (a : Limbs) : Prop :=
  a.x0 < B ∧ a.x1 < B ∧ a.x2 < B ∧ a.x3 < B ∧ a.x4 < B

theorem tight_split (w : Nat) : (splitLimbs w).Tight := by
  simp only [Limbs.Tight, splitLimbs]
  exact ⟨Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide),
    Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide)⟩

structure Fits (d : Limbs) : Prop where
  t0 : d.x0 < 2^58
  t1 : d.x1 + d.x0/B < 2^58
  t2 : d.x2 + (d.x1 + d.x0/B)/B < 2^58
  t3 : d.x3 + (d.x2 + (d.x1 + d.x0/B)/B)/B < 2^58
  t4 : d.x4 + (d.x3 + (d.x2 + (d.x1 + d.x0/B)/B)/B)/B < 11*B^2
  fold : d.x0%B + 5*((d.x4 + (d.x3 + (d.x2 + (d.x1 + d.x0/B)/B)/B)/B)/B) < 2^32

theorem convolution_fits {a r block : Limbs} (ha : a.Bounded) (hr : r.Tight) (hb : block.Tight) :
    Fits (convolution (a.plus block) r) := by
  obtain ⟨a0,a1,a2,a3,a4⟩ := ha
  obtain ⟨r0,r1,r2,r3,r4⟩ := hr
  obtain ⟨b0,b1,b2,b3,b4⟩ := hb
  have mult {x y z : Nat} (hx : x < B+64) (hy : y < B) (hz : z < B) :
      (x+y)*z ≤ (2*B+64)*B := Nat.mul_le_mul (by omega) (by omega)
  have h00 := mult (x := a.x0) (y := block.x0) (z := r.x0) (by omega) b0 r0
  have h01 := mult (x := a.x0) (y := block.x0) (z := r.x1) (by omega) b0 r1
  have h02 := mult (x := a.x0) (y := block.x0) (z := r.x2) (by omega) b0 r2
  have h03 := mult (x := a.x0) (y := block.x0) (z := r.x3) (by omega) b0 r3
  have h04 := mult (x := a.x0) (y := block.x0) (z := r.x4) (by omega) b0 r4
  have h10 := mult (x := a.x1) (y := block.x1) (z := r.x0) (by omega) b1 r0
  have h11 := mult (x := a.x1) (y := block.x1) (z := r.x1) (by omega) b1 r1
  have h12 := mult (x := a.x1) (y := block.x1) (z := r.x2) (by omega) b1 r2
  have h13 := mult (x := a.x1) (y := block.x1) (z := r.x3) (by omega) b1 r3
  have h14 := mult (x := a.x1) (y := block.x1) (z := r.x4) (by omega) b1 r4
  have h20 := mult (x := a.x2) (y := block.x2) (z := r.x0) (by omega) b2 r0
  have h21 := mult (x := a.x2) (y := block.x2) (z := r.x1) (by omega) b2 r1
  have h22 := mult (x := a.x2) (y := block.x2) (z := r.x2) (by omega) b2 r2
  have h23 := mult (x := a.x2) (y := block.x2) (z := r.x3) (by omega) b2 r3
  have h24 := mult (x := a.x2) (y := block.x2) (z := r.x4) (by omega) b2 r4
  have h30 := mult (x := a.x3) (y := block.x3) (z := r.x0) (by omega) b3 r0
  have h31 := mult (x := a.x3) (y := block.x3) (z := r.x1) (by omega) b3 r1
  have h32 := mult (x := a.x3) (y := block.x3) (z := r.x2) (by omega) b3 r2
  have h33 := mult (x := a.x3) (y := block.x3) (z := r.x3) (by omega) b3 r3
  have h34 := mult (x := a.x3) (y := block.x3) (z := r.x4) (by omega) b3 r4
  have h40 := mult (x := a.x4) (y := block.x4) (z := r.x0) (by omega) b4 r0
  have h41 := mult (x := a.x4) (y := block.x4) (z := r.x1) (by omega) b4 r1
  have h42 := mult (x := a.x4) (y := block.x4) (z := r.x2) (by omega) b4 r2
  have h43 := mult (x := a.x4) (y := block.x4) (z := r.x3) (by omega) b4 r3
  have h44 := mult (x := a.x4) (y := block.x4) (z := r.x4) (by omega) b4 r4
  constructor <;> simp only [convolution, Limbs.plus, B, Nat.reducePow] at * <;> omega

theorem bounded_carry {d : Limbs} (hf : Fits d) : (carry d).limbs.Bounded := by
  obtain ⟨_, _, _, _, _, hw⟩ := hf
  simp only [carry, Limbs.Bounded, B, Nat.reducePow] at *
  omega

theorem bounded_update {a r block : Limbs} (ha : a.Bounded) (hr : r.Tight) (hb : block.Tight) :
    (update a r block).Bounded :=
  bounded_carry (convolution_fits ha hr hb)

end ChaCha20Poly1305.Proofs.Decrypt.Poly1305
