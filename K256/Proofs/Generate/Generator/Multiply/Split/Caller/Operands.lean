import K256.Proofs.Generate.Generator.Multiply.Split.Caller.Memory
import K256.Proofs.Generate.Generator.Multiply.Split.Parameters

namespace K256.Proofs.Generate.Generator.Multiply.Split.Caller

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters.Secp256k1
open K256.Proofs.Generate.Curve

def Site.x (k : Site) (d : Nat) := match k with
  | .roundFirst | .roundSecond | .addFirst => d
  | .mulFirst => mulShift384 d g1
  | .mulSecond => mulShift384 d g2
  | .addSecond => (mulShift384 d g1 * minusB1) % domain.n
  | .mulLambda => splitSecond d

def Site.y (k : Site) (d : Nat) := match k with
  | .roundFirst => g1
  | .mulFirst => minusB1
  | .roundSecond => g2
  | .mulSecond => minusB2
  | .addSecond => (mulShift384 d g2 * minusB2) % domain.n
  | .mulLambda => domain.n - eigenvalue
  | .addFirst => (splitSecond d * (domain.n - eigenvalue)) % domain.n

def Site.value (k : Site) (d : Nat) := match k with
  | .roundFirst => mulShift384 d g1
  | .roundSecond => mulShift384 d g2
  | .mulFirst => (mulShift384 d g1 * minusB1) % domain.n
  | .mulSecond => (mulShift384 d g2 * minusB2) % domain.n
  | .addSecond => splitSecond d
  | .mulLambda => (splitSecond d * (domain.n - eigenvalue)) % domain.n
  | .addFirst => splitFirst d

def Site.keep (k : Site) (d : Nat) : List (Nat × Nat) := match k with
  | .roundSecond | .mulSecond => [(0xc10,Site.mulFirst.value d)]
  | .mulLambda | .addFirst => [(0x418,splitSecond d)]
  | _ => []

def Site.before (k : Site) (d : Nat) : List (Nat × Nat) := match k with
  | .roundFirst => []
  | .mulFirst => [(0x128,Site.roundFirst.value d)]
  | .roundSecond => [(0xc10,Site.mulFirst.value d)]
  | .mulSecond => [(0x128,Site.roundSecond.value d),(0xc10,Site.mulFirst.value d)]
  | .addSecond => [(0x328,Site.mulSecond.value d),(0xc10,Site.mulFirst.value d)]
  | .mulLambda => [(0x418,splitSecond d)]
  | .addFirst => [(0x128,Site.mulLambda.value d),(0x418,splitSecond d)]

def ScalarsAt (fr : Activation) (m : Ram) (xs : List (Nat × Nat)) :=
  ∀ kv ∈ xs, WordsAt m (slot fr kv.1) 64 (scalarWords kv.2)

def Site.after (k : Site) (d : Nat) := (k.dest,k.value d) :: k.keep d

theorem Site.before_apart (k : Site) (d : Nat) {kv : Nat × Nat} (h : kv ∈ k.before d) :
    kv.1+32 ≤ 3256 ∧ (kv.1+32 ≤ k.dest ∨ k.dest+32 ≤ kv.1) := by
  cases k <;> simp only [Site.before,List.mem_cons,List.not_mem_nil,or_false] at h <;>
    first | contradiction | (rcases h with rfl|rfl <;> dsimp only <;> decide) | (subst kv; dsimp only; decide)

theorem Site.kept (k : Site) (d : Nat) {kv : Nat × Nat} (h : kv ∈ k.keep d) : kv ∈ k.before d := by
  cases k <;> simp [Site.keep,Site.before] at h ⊢ <;> subst kv <;> simp

theorem Site.transfer (k : Site) {d : Nat} {fr : Activation} {a : Registers} (e : CoreEntry fr a d)
    {m n : Ram} (frame : RamWriteFrame m n (k.writes fr))
    (before : ScalarsAt fr m (k.before d)) : ScalarsAt fr n (k.before d) := by
  intro kv h
  obtain ⟨hi,apart⟩ := k.before_apart d h
  exact k.keepWords e frame (before kv h) (by omega) apart

theorem Site.produced (k : Site) {d : Nat} {fr : Activation} {m : Ram}
    (before : ScalarsAt fr m (k.before d)) (out : WordsAt m (slot fr k.dest) 64 (scalarWords (k.value d))) :
    ScalarsAt fr m (k.after d) := by
  intro kv h
  obtain rfl|h := List.mem_cons.mp h
  · exact out
  · exact before kv (k.kept d h)

set_option exponentiation.threshold 512 in
theorem boundedInputs (k : Site) {d : Nat} (bound : d < domain.n) :
    k.x d < domain.n ∧ k.y d < domain.n := by
  have npos : 0 < domain.n := by decide +kernel
  have rounded (g : Nat) (hg : g < domain.n) : mulShift384 d g < domain.n := by
    apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 2^384)).2
    have h₁ := Nat.mul_le_mul (Nat.le_of_lt bound) (Nat.le_of_lt hg)
    have h₂ : domain.n * domain.n + 2^383 < domain.n * 2^384 := by decide +kernel
    omega
  have g₁ : g1 < domain.n := by decide +kernel
  have g₂ : g2 < domain.n := by decide +kernel
  cases k with
  | roundFirst => exact ⟨bound, g₁⟩
  | mulFirst => exact ⟨rounded _ g₁, by change minusB1 < domain.n; decide +kernel⟩
  | roundSecond => exact ⟨bound, g₂⟩
  | mulSecond => exact ⟨rounded _ g₂, by change minusB2 < domain.n; decide +kernel⟩
  | addSecond => exact ⟨Nat.mod_lt _ npos, Nat.mod_lt _ npos⟩
  | mulLambda => exact ⟨Nat.mod_lt _ npos, by change domain.n - eigenvalue < domain.n; decide +kernel⟩
  | addFirst => exact ⟨bound, Nat.mod_lt _ npos⟩

end K256.Proofs.Generate.Generator.Multiply.Split.Caller
